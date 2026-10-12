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
uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(lean_object* v_e_6_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_6_ = stack[0].m_obj;
uint8_t v_res_13_;
v_res_13_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(v_e_6_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed(lean_object* v_e_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(v_e_14_);
lean_dec_ref(v_e_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_ks_21_; lean_object* v_vs_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_46_; 
v_ks_21_ = lean_ctor_get(v_x_17_, 0);
v_vs_22_ = lean_ctor_get(v_x_17_, 1);
v_isSharedCheck_46_ = !lean_is_exclusive(v_x_17_);
if (v_isSharedCheck_46_ == 0)
{
v___x_24_ = v_x_17_;
v_isShared_25_ = v_isSharedCheck_46_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_vs_22_);
lean_inc(v_ks_21_);
lean_dec(v_x_17_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_46_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lean_array_get_size(v_ks_21_);
v___x_27_ = lean_nat_dec_lt(v_x_18_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
lean_dec(v_x_18_);
v___x_28_ = lean_array_push(v_ks_21_, v_x_19_);
v___x_29_ = lean_array_push(v_vs_22_, v_x_20_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v___x_29_);
lean_ctor_set(v___x_24_, 0, v___x_28_);
v___x_31_ = v___x_24_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v___x_29_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
else
{
lean_object* v_k_x27_33_; uint8_t v___x_34_; 
v_k_x27_33_ = lean_array_fget_borrowed(v_ks_21_, v_x_18_);
v___x_34_ = l_Lean_instBEqMVarId_beq(v_x_19_, v_k_x27_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_36_; 
if (v_isShared_25_ == 0)
{
v___x_36_ = v___x_24_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_ks_21_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_vs_22_);
v___x_36_ = v_reuseFailAlloc_40_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = lean_nat_add(v_x_18_, v___x_37_);
lean_dec(v_x_18_);
v_x_17_ = v___x_36_;
v_x_18_ = v___x_38_;
goto _start;
}
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_41_ = lean_array_fset(v_ks_21_, v_x_18_, v_x_19_);
v___x_42_ = lean_array_fset(v_vs_22_, v_x_18_, v_x_20_);
lean_dec(v_x_18_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v___x_42_);
lean_ctor_set(v___x_24_, 0, v___x_41_);
v___x_44_ = v___x_24_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___x_42_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_47_, lean_object* v_k_48_, lean_object* v_v_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_47_, v___x_50_, v_k_48_, v_v_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_52_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(lean_object* v_x_53_, size_t v_x_54_, size_t v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v_es_58_; size_t v___x_59_; size_t v___x_60_; lean_object* v_j_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v_es_58_ = lean_ctor_get(v_x_53_, 0);
v___x_59_ = ((size_t)31ULL);
v___x_60_ = lean_usize_land(v_x_54_, v___x_59_);
v_j_61_ = lean_usize_to_nat(v___x_60_);
v___x_62_ = lean_array_get_size(v_es_58_);
v___x_63_ = lean_nat_dec_lt(v_j_61_, v___x_62_);
if (v___x_63_ == 0)
{
lean_dec(v_j_61_);
lean_dec(v_x_57_);
lean_dec(v_x_56_);
return v_x_53_;
}
else
{
lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_102_; 
lean_inc_ref(v_es_58_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_53_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v_x_53_, 0);
lean_dec(v_unused_103_);
v___x_65_ = v_x_53_;
v_isShared_66_ = v_isSharedCheck_102_;
goto v_resetjp_64_;
}
else
{
lean_dec(v_x_53_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_102_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v_v_67_; lean_object* v___x_68_; lean_object* v_xs_x27_69_; lean_object* v___y_71_; 
v_v_67_ = lean_array_fget(v_es_58_, v_j_61_);
v___x_68_ = lean_box(0);
v_xs_x27_69_ = lean_array_fset(v_es_58_, v_j_61_, v___x_68_);
switch(lean_obj_tag(v_v_67_))
{
case 0:
{
lean_object* v_key_76_; lean_object* v_val_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_87_; 
v_key_76_ = lean_ctor_get(v_v_67_, 0);
v_val_77_ = lean_ctor_get(v_v_67_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_v_67_);
if (v_isSharedCheck_87_ == 0)
{
v___x_79_ = v_v_67_;
v_isShared_80_ = v_isSharedCheck_87_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_val_77_);
lean_inc(v_key_76_);
lean_dec(v_v_67_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_87_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; 
v___x_81_ = l_Lean_instBEqMVarId_beq(v_x_56_, v_key_76_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_del_object(v___x_79_);
v___x_82_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_76_, v_val_77_, v_x_56_, v_x_57_);
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
v___y_71_ = v___x_83_;
goto v___jp_70_;
}
else
{
lean_object* v___x_85_; 
lean_dec(v_val_77_);
lean_dec(v_key_76_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 1, v_x_57_);
lean_ctor_set(v___x_79_, 0, v_x_56_);
v___x_85_ = v___x_79_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_x_56_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_x_57_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
v___y_71_ = v___x_85_;
goto v___jp_70_;
}
}
}
}
case 1:
{
lean_object* v_node_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_100_; 
v_node_88_ = lean_ctor_get(v_v_67_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v_v_67_);
if (v_isSharedCheck_100_ == 0)
{
v___x_90_ = v_v_67_;
v_isShared_91_ = v_isSharedCheck_100_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_node_88_);
lean_dec(v_v_67_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_100_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_92_ = ((size_t)5ULL);
v___x_93_ = lean_usize_shift_right(v_x_54_, v___x_92_);
v___x_94_ = ((size_t)1ULL);
v___x_95_ = lean_usize_add(v_x_55_, v___x_94_);
v___x_96_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_node_88_, v___x_93_, v___x_95_, v_x_56_, v_x_57_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_96_);
v___x_98_ = v___x_90_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
v___y_71_ = v___x_98_;
goto v___jp_70_;
}
}
}
default: 
{
lean_object* v___x_101_; 
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v_x_56_);
lean_ctor_set(v___x_101_, 1, v_x_57_);
v___y_71_ = v___x_101_;
goto v___jp_70_;
}
}
v___jp_70_:
{
lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_72_ = lean_array_fset(v_xs_x27_69_, v_j_61_, v___y_71_);
lean_dec(v_j_61_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_72_);
v___x_74_ = v___x_65_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
else
{
lean_object* v_ks_104_; lean_object* v_vs_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_123_; 
v_ks_104_ = lean_ctor_get(v_x_53_, 0);
v_vs_105_ = lean_ctor_get(v_x_53_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_53_);
if (v_isSharedCheck_123_ == 0)
{
v___x_107_ = v_x_53_;
v_isShared_108_ = v_isSharedCheck_123_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_vs_105_);
lean_inc(v_ks_104_);
lean_dec(v_x_53_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_123_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_ks_104_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_vs_105_);
v___x_110_ = v_reuseFailAlloc_122_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v_newNode_111_; size_t v___x_112_; uint8_t v___x_113_; 
v_newNode_111_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v___x_110_, v_x_56_, v_x_57_);
v___x_112_ = ((size_t)7ULL);
v___x_113_ = lean_usize_dec_le(v___x_112_, v_x_55_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_114_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_111_);
v___x_115_ = lean_unsigned_to_nat(4u);
v___x_116_ = lean_nat_dec_lt(v___x_114_, v___x_115_);
lean_dec(v___x_114_);
if (v___x_116_ == 0)
{
lean_object* v_ks_117_; lean_object* v_vs_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_ks_117_ = lean_ctor_get(v_newNode_111_, 0);
lean_inc_ref(v_ks_117_);
v_vs_118_ = lean_ctor_get(v_newNode_111_, 1);
lean_inc_ref(v_vs_118_);
lean_dec_ref(v_newNode_111_);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_121_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_x_55_, v_ks_117_, v_vs_118_, v___x_119_, v___x_120_);
lean_dec_ref(v_vs_118_);
lean_dec_ref(v_ks_117_);
return v___x_121_;
}
else
{
return v_newNode_111_;
}
}
else
{
return v_newNode_111_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_53_ = stack[0].m_obj;
size_t v_x_54_ = stack[1].m_num;
size_t v_x_55_ = stack[2].m_num;
lean_object* v_x_56_ = stack[3].m_obj;
lean_object* v_x_57_ = stack[4].m_obj;
lean_object* v_res_124_;
v_res_124_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_53_, v_x_54_, v_x_55_, v_x_56_, v_x_57_);
stack->m_obj
 = v_res_124_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_125_, lean_object* v_keys_126_, lean_object* v_vals_127_, lean_object* v_i_128_, lean_object* v_entries_129_){
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
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_125_ = stack[0].m_num;
lean_object* v_keys_126_ = stack[1].m_obj;
lean_object* v_vals_127_ = stack[2].m_obj;
lean_object* v_i_128_ = stack[3].m_obj;
lean_object* v_entries_129_ = stack[4].m_obj;
lean_object* v_res_145_;
v_res_145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_125_, v_keys_126_, v_vals_127_, v_i_128_, v_entries_129_);
stack->m_obj
 = v_res_145_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_146_, lean_object* v_keys_147_, lean_object* v_vals_148_, lean_object* v_i_149_, lean_object* v_entries_150_){
_start:
{
size_t v_depth_boxed_151_; lean_object* v_res_152_; 
v_depth_boxed_151_ = lean_unbox_usize(v_depth_146_);
lean_dec(v_depth_146_);
v_res_152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_151_, v_keys_147_, v_vals_148_, v_i_149_, v_entries_150_);
lean_dec_ref(v_vals_148_);
lean_dec_ref(v_keys_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
size_t v_x_1166__boxed_158_; size_t v_x_1167__boxed_159_; lean_object* v_res_160_; 
v_x_1166__boxed_158_ = lean_unbox_usize(v_x_154_);
lean_dec(v_x_154_);
v_x_1167__boxed_159_ = lean_unbox_usize(v_x_155_);
lean_dec(v_x_155_);
v_res_160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_153_, v_x_1166__boxed_158_, v_x_1167__boxed_159_, v_x_156_, v_x_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
uint64_t v___x_164_; size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; 
v___x_164_ = l_Lean_instHashableMVarId_hash(v_x_162_);
v___x_165_ = lean_uint64_to_usize(v___x_164_);
v___x_166_ = ((size_t)1ULL);
v___x_167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_161_, v___x_165_, v___x_166_, v_x_162_, v_x_163_);
return v___x_167_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object* v_mvarId_168_, lean_object* v_val_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; lean_object* v_mctx_173_; lean_object* v_cache_174_; lean_object* v_zetaDeltaFVarIds_175_; lean_object* v_postponed_176_; lean_object* v_diag_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_207_; 
v___x_172_ = lean_st_ref_take(v___y_170_);
v_mctx_173_ = lean_ctor_get(v___x_172_, 0);
v_cache_174_ = lean_ctor_get(v___x_172_, 1);
v_zetaDeltaFVarIds_175_ = lean_ctor_get(v___x_172_, 2);
v_postponed_176_ = lean_ctor_get(v___x_172_, 3);
v_diag_177_ = lean_ctor_get(v___x_172_, 4);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_207_ == 0)
{
v___x_179_ = v___x_172_;
v_isShared_180_ = v_isSharedCheck_207_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_diag_177_);
lean_inc(v_postponed_176_);
lean_inc(v_zetaDeltaFVarIds_175_);
lean_inc(v_cache_174_);
lean_inc(v_mctx_173_);
lean_dec(v___x_172_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_207_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_depth_181_; lean_object* v_levelAssignDepth_182_; lean_object* v_lmvarCounter_183_; lean_object* v_mvarCounter_184_; lean_object* v_lDecls_185_; lean_object* v_decls_186_; lean_object* v_userNames_187_; lean_object* v_lAssignment_188_; lean_object* v_eAssignment_189_; lean_object* v_dAssignment_190_; lean_object* v_instanceTypedMVars_191_; lean_object* v_synthNormMemo_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_206_; 
v_depth_181_ = lean_ctor_get(v_mctx_173_, 0);
v_levelAssignDepth_182_ = lean_ctor_get(v_mctx_173_, 1);
v_lmvarCounter_183_ = lean_ctor_get(v_mctx_173_, 2);
v_mvarCounter_184_ = lean_ctor_get(v_mctx_173_, 3);
v_lDecls_185_ = lean_ctor_get(v_mctx_173_, 4);
v_decls_186_ = lean_ctor_get(v_mctx_173_, 5);
v_userNames_187_ = lean_ctor_get(v_mctx_173_, 6);
v_lAssignment_188_ = lean_ctor_get(v_mctx_173_, 7);
v_eAssignment_189_ = lean_ctor_get(v_mctx_173_, 8);
v_dAssignment_190_ = lean_ctor_get(v_mctx_173_, 9);
v_instanceTypedMVars_191_ = lean_ctor_get(v_mctx_173_, 10);
v_synthNormMemo_192_ = lean_ctor_get(v_mctx_173_, 11);
v_isSharedCheck_206_ = !lean_is_exclusive(v_mctx_173_);
if (v_isSharedCheck_206_ == 0)
{
v___x_194_ = v_mctx_173_;
v_isShared_195_ = v_isSharedCheck_206_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_synthNormMemo_192_);
lean_inc(v_instanceTypedMVars_191_);
lean_inc(v_dAssignment_190_);
lean_inc(v_eAssignment_189_);
lean_inc(v_lAssignment_188_);
lean_inc(v_userNames_187_);
lean_inc(v_decls_186_);
lean_inc(v_lDecls_185_);
lean_inc(v_mvarCounter_184_);
lean_inc(v_lmvarCounter_183_);
lean_inc(v_levelAssignDepth_182_);
lean_inc(v_depth_181_);
lean_dec(v_mctx_173_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_206_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_196_ = lean_box(0);
v___x_197_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_189_, v_mvarId_168_, v_val_169_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 8, v___x_197_);
v___x_199_ = v___x_194_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_depth_181_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_levelAssignDepth_182_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_lmvarCounter_183_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_mvarCounter_184_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_lDecls_185_);
lean_ctor_set(v_reuseFailAlloc_205_, 5, v_decls_186_);
lean_ctor_set(v_reuseFailAlloc_205_, 6, v_userNames_187_);
lean_ctor_set(v_reuseFailAlloc_205_, 7, v_lAssignment_188_);
lean_ctor_set(v_reuseFailAlloc_205_, 8, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_205_, 9, v_dAssignment_190_);
lean_ctor_set(v_reuseFailAlloc_205_, 10, v_instanceTypedMVars_191_);
lean_ctor_set(v_reuseFailAlloc_205_, 11, v_synthNormMemo_192_);
v___x_199_ = v_reuseFailAlloc_205_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_199_);
v___x_201_ = v___x_179_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_cache_174_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_zetaDeltaFVarIds_175_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_postponed_176_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_diag_177_);
v___x_201_ = v_reuseFailAlloc_204_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_st_ref_put(v___y_170_, v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_196_);
return v___x_203_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_168_ = stack[0].m_obj;
lean_object* v_val_169_ = stack[1].m_obj;
lean_object* v___y_170_ = stack[2].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_168_, v_val_169_, v___y_170_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object* v_mvarId_209_, lean_object* v_val_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_209_, v_val_210_, v___y_211_);
lean_dec(v___y_211_);
return v_res_213_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object* v_mvarId_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___f_221_; lean_object* v___x_222_; 
v___f_221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
lean_inc(v_mvarId_215_);
v___x_222_ = l_Lean_MVarId_getType(v_mvarId_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_266_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_266_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_266_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_266_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; 
v___x_227_ = lean_find_expr(v___f_221_, v_a_223_);
lean_dec(v_a_223_);
if (lean_obj_tag(v___x_227_) == 1)
{
lean_object* v_val_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_del_object(v___x_225_);
v_val_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = l_Lean_Expr_appArg_x21(v_val_228_);
lean_dec(v_val_228_);
lean_inc(v_mvarId_215_);
v___x_230_ = l_Lean_MVarId_getType(v_mvarId_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = l_Lean_Meta_mkFalseElim(v_a_231_, v___x_229_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_243_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_232_, 1);
v___x_234_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_215_, v_a_233_, v_a_217_);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; 
v_unused_244_ = lean_ctor_get(v___x_234_, 0);
lean_dec(v_unused_244_);
v___x_236_ = v___x_234_;
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
else
{
lean_dec(v___x_234_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_238_ = 1;
v___x_239_ = lean_box(v___x_238_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec(v_mvarId_215_);
v_a_245_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_232_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_232_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec_ref(v___x_229_);
lean_dec(v_mvarId_215_);
v_a_253_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_230_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_230_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
lean_dec(v___x_227_);
lean_dec(v_mvarId_215_);
v___x_261_ = 0;
v___x_262_ = lean_box(v___x_261_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_262_);
v___x_264_ = v___x_225_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_mvarId_215_);
v_a_267_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_222_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_222_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_215_ = stack[0].m_obj;
lean_object* v_a_216_ = stack[1].m_obj;
lean_object* v_a_217_ = stack[2].m_obj;
lean_object* v_a_218_ = stack[3].m_obj;
lean_object* v_a_219_ = stack[4].m_obj;
lean_object* v_res_275_;
v_res_275_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
stack->m_obj
 = v_res_275_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object* v_mvarId_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
return v_res_282_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object* v_mvarId_283_, lean_object* v_val_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_283_, v_val_284_, v___y_286_);
return v___x_290_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_283_ = stack[0].m_obj;
lean_object* v_val_284_ = stack[1].m_obj;
lean_object* v___y_285_ = stack[2].m_obj;
lean_object* v___y_286_ = stack[3].m_obj;
lean_object* v___y_287_ = stack[4].m_obj;
lean_object* v___y_288_ = stack[5].m_obj;
lean_object* v_res_291_;
v_res_291_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(v_mvarId_283_, v_val_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object* v_mvarId_292_, lean_object* v_val_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(v_mvarId_292_, v_val_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object* v_00_u03b2_300_, lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_x_301_, v_x_302_, v_x_303_);
return v___x_304_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_305_, lean_object* v_x_306_, size_t v_x_307_, size_t v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_306_, v_x_307_, v_x_308_, v_x_309_, v_x_310_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_306_ = stack[1].m_obj;
size_t v_x_307_ = stack[2].m_num;
size_t v_x_308_ = stack[3].m_num;
lean_object* v_x_309_ = stack[4].m_obj;
lean_object* v_x_310_ = stack[5].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_box(0), v_x_306_, v_x_307_, v_x_308_, v_x_309_, v_x_310_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
size_t v_x_1703__boxed_319_; size_t v_x_1704__boxed_320_; lean_object* v_res_321_; 
v_x_1703__boxed_319_ = lean_unbox_usize(v_x_315_);
lean_dec(v_x_315_);
v_x_1704__boxed_320_ = lean_unbox_usize(v_x_316_);
lean_dec(v_x_316_);
v_res_321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_313_, v_x_314_, v_x_1703__boxed_319_, v_x_1704__boxed_320_, v_x_317_, v_x_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_322_, lean_object* v_n_323_, lean_object* v_k_324_, lean_object* v_v_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v_n_323_, v_k_324_, v_v_325_);
return v___x_326_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_327_, size_t v_depth_328_, lean_object* v_keys_329_, lean_object* v_vals_330_, lean_object* v_heq_331_, lean_object* v_i_332_, lean_object* v_entries_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_328_, v_keys_329_, v_vals_330_, v_i_332_, v_entries_333_);
return v___x_334_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_328_ = stack[1].m_num;
lean_object* v_keys_329_ = stack[2].m_obj;
lean_object* v_vals_330_ = stack[3].m_obj;
lean_object* v_i_332_ = stack[5].m_obj;
lean_object* v_entries_333_ = stack[6].m_obj;
lean_object* v_res_335_;
v_res_335_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_depth_328_, v_keys_329_, v_vals_330_, lean_box(0), v_i_332_, v_entries_333_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_336_, lean_object* v_depth_337_, lean_object* v_keys_338_, lean_object* v_vals_339_, lean_object* v_heq_340_, lean_object* v_i_341_, lean_object* v_entries_342_){
_start:
{
size_t v_depth_boxed_343_; lean_object* v_res_344_; 
v_depth_boxed_343_ = lean_unbox_usize(v_depth_337_);
lean_dec(v_depth_337_);
v_res_344_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_336_, v_depth_boxed_343_, v_keys_338_, v_vals_339_, v_heq_340_, v_i_341_, v_entries_342_);
lean_dec_ref(v_vals_339_);
lean_dec_ref(v_keys_338_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_346_, v_x_347_, v_x_348_, v_x_349_);
return v___x_350_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* v_fvarId_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_FVarId_getType___redArg(v_fvarId_351_, v_a_352_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v___x_363_ = l_Lean_Meta_whnfD(v_a_362_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_390_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_390_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_390_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_390_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Expr_getAppFn(v_a_364_);
lean_dec(v_a_364_);
if (lean_obj_tag(v___x_368_) == 4)
{
lean_object* v_declName_369_; lean_object* v___x_370_; lean_object* v_env_371_; uint8_t v___x_372_; lean_object* v___x_373_; 
v_declName_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_declName_369_);
lean_dec_ref_known(v___x_368_, 2);
v___x_370_ = lean_st_ref_get(v_a_355_);
v_env_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_ref(v_env_371_);
lean_dec(v___x_370_);
v___x_372_ = 0;
v___x_373_ = l_Lean_Environment_find_x3f(v_env_371_, v_declName_369_, v___x_372_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_del_object(v___x_366_);
goto v___jp_357_;
}
else
{
lean_object* v_val_374_; 
v_val_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v___x_373_, 1);
if (lean_obj_tag(v_val_374_) == 5)
{
lean_object* v_val_375_; lean_object* v_numIndices_376_; lean_object* v_ctors_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_val_375_ = lean_ctor_get(v_val_374_, 0);
lean_inc_ref(v_val_375_);
lean_dec_ref_known(v_val_374_, 1);
v_numIndices_376_ = lean_ctor_get(v_val_375_, 2);
lean_inc(v_numIndices_376_);
v_ctors_377_ = lean_ctor_get(v_val_375_, 4);
lean_inc(v_ctors_377_);
lean_dec_ref(v_val_375_);
v___x_378_ = l_List_lengthTR___redArg(v_ctors_377_);
lean_dec(v_ctors_377_);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_nat_dec_eq(v___x_378_, v___x_379_);
lean_dec(v___x_378_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_381_ = lean_nat_dec_lt(v___x_379_, v_numIndices_376_);
lean_dec(v_numIndices_376_);
v___x_382_ = lean_box(v___x_381_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_382_);
v___x_384_ = v___x_366_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec(v_numIndices_376_);
v___x_386_ = lean_box(v___x_380_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_386_);
v___x_388_ = v___x_366_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_dec(v_val_374_);
lean_del_object(v___x_366_);
goto v___jp_357_;
}
}
}
else
{
lean_dec_ref(v___x_368_);
lean_del_object(v___x_366_);
goto v___jp_357_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_363_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_363_);
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
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_361_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_361_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
v___jp_357_:
{
uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = 0;
v___x_359_ = lean_box(v___x_358_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_351_ = stack[0].m_obj;
lean_object* v_a_352_ = stack[1].m_obj;
lean_object* v_a_353_ = stack[2].m_obj;
lean_object* v_a_354_ = stack[3].m_obj;
lean_object* v_a_355_ = stack[4].m_obj;
lean_object* v_res_407_;
v_res_407_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
stack->m_obj
 = v_res_407_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object* v_fvarId_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_414_;
}
}
lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object* v_s_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_SavedState_restore___redArg(v_s_415_, v___y_418_, v___y_420_);
return v___x_422_;
}
}
LEAN_EXPORT void l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_415_ = stack[0].m_obj;
lean_object* v___y_416_ = stack[1].m_obj;
lean_object* v___y_417_ = stack[2].m_obj;
lean_object* v___y_418_ = stack[3].m_obj;
lean_object* v___y_419_ = stack[4].m_obj;
lean_object* v___y_420_ = stack[5].m_obj;
lean_object* v_res_423_;
v_res_423_ = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(v_s_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
stack->m_obj
 = v_res_423_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object* v_s_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(v_s_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
return v_res_431_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object* v_x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; 
lean_inc(v___y_441_);
v___x_447_ = lean_apply_6(v_x_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, lean_box(0));
return v___x_447_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_440_ = stack[0].m_obj;
lean_object* v___y_441_ = stack[1].m_obj;
lean_object* v___y_442_ = stack[2].m_obj;
lean_object* v___y_443_ = stack[3].m_obj;
lean_object* v___y_444_ = stack[4].m_obj;
lean_object* v___y_445_ = stack[5].m_obj;
lean_object* v_res_448_;
v_res_448_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(v_x_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object* v_x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(v_x_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_450_);
return v_res_456_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* v_mvarId_457_, lean_object* v_x_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___f_465_; lean_object* v___x_466_; 
lean_inc(v___y_459_);
v___f_465_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_465_, 0, v_x_458_);
lean_closure_set(v___f_465_, 1, v___y_459_);
v___x_466_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_457_, v___f_465_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_466_) == 0)
{
return v___x_466_;
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_457_ = stack[0].m_obj;
lean_object* v_x_458_ = stack[1].m_obj;
lean_object* v___y_459_ = stack[2].m_obj;
lean_object* v___y_460_ = stack[3].m_obj;
lean_object* v___y_461_ = stack[4].m_obj;
lean_object* v___y_462_ = stack[5].m_obj;
lean_object* v___y_463_ = stack[6].m_obj;
lean_object* v_res_475_;
v_res_475_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_457_, v_x_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object* v_mvarId_476_, lean_object* v_x_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_476_, v_x_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
return v_res_484_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object* v_00_u03b1_485_, lean_object* v_mvarId_486_, lean_object* v_x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_486_, v_x_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_494_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_486_ = stack[1].m_obj;
lean_object* v_x_487_ = stack[2].m_obj;
lean_object* v___y_488_ = stack[3].m_obj;
lean_object* v___y_489_ = stack[4].m_obj;
lean_object* v___y_490_ = stack[5].m_obj;
lean_object* v___y_491_ = stack[6].m_obj;
lean_object* v___y_492_ = stack[7].m_obj;
lean_object* v_res_495_;
v_res_495_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_box(0), v_mvarId_486_, v_x_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
stack->m_obj
 = v_res_495_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object* v_00_u03b1_496_, lean_object* v_mvarId_497_, lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(v_00_u03b1_496_, v_mvarId_497_, v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
return v_res_505_;
}
}
lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* v_x_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Meta_saveState___redArg(v___y_509_, v___y_511_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___y_516_; lean_object* v___y_517_; uint8_t v___y_518_; lean_object* v___y_537_; lean_object* v_a_538_; lean_object* v___x_541_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
lean_inc(v___y_509_);
lean_inc_ref(v___y_508_);
lean_inc(v___y_507_);
v___x_541_ = lean_apply_6(v_x_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, lean_box(0));
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; uint8_t v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
v___x_543_ = lean_unbox(v_a_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
lean_dec_ref_known(v___x_541_, 1);
lean_inc(v_a_514_);
v___x_544_ = l_Lean_Meta_SavedState_restore___redArg(v_a_514_, v___y_509_, v___y_511_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec(v_a_514_);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_544_, 0);
lean_dec(v_unused_552_);
v___x_546_ = v___x_544_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_dec(v___x_544_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v_a_542_);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_542_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_a_542_);
v_a_553_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_544_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_544_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
lean_inc(v_a_553_);
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
v___y_537_ = v___x_558_;
v_a_538_ = v_a_553_;
goto v___jp_536_;
}
}
}
}
else
{
lean_dec(v_a_542_);
lean_dec(v_a_514_);
return v___x_541_;
}
}
else
{
lean_object* v_a_561_; 
v_a_561_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_561_);
v___y_537_ = v___x_541_;
v_a_538_ = v_a_561_;
goto v___jp_536_;
}
v___jp_515_:
{
if (v___y_518_ == 0)
{
lean_object* v___x_519_; 
lean_dec_ref(v___y_516_);
v___x_519_ = l_Lean_Meta_SavedState_restore___redArg(v_a_514_, v___y_509_, v___y_511_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v___x_519_, 0);
lean_dec(v_unused_527_);
v___x_521_ = v___x_519_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_dec(v___x_519_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 1);
lean_ctor_set(v___x_521_, 0, v___y_517_);
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___y_517_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v___y_517_);
v_a_528_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_519_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_519_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
else
{
lean_dec_ref(v___y_517_);
lean_dec(v_a_514_);
return v___y_516_;
}
}
v___jp_536_:
{
uint8_t v___x_539_; 
v___x_539_ = l_Lean_Exception_isInterrupt(v_a_538_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
lean_inc_ref(v_a_538_);
v___x_540_ = l_Lean_Exception_isRuntime(v_a_538_);
v___y_516_ = v___y_537_;
v___y_517_ = v_a_538_;
v___y_518_ = v___x_540_;
goto v___jp_515_;
}
else
{
v___y_516_ = v___y_537_;
v___y_517_ = v_a_538_;
v___y_518_ = v___x_539_;
goto v___jp_515_;
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v_x_506_);
v_a_562_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_513_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_513_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_506_ = stack[0].m_obj;
lean_object* v___y_507_ = stack[1].m_obj;
lean_object* v___y_508_ = stack[2].m_obj;
lean_object* v___y_509_ = stack[3].m_obj;
lean_object* v___y_510_ = stack[4].m_obj;
lean_object* v___y_511_ = stack[5].m_obj;
lean_object* v_res_570_;
v_res_570_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_x_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
return v_res_578_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object* v_msgData_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; lean_object* v_env_586_; uint8_t v___x_587_; lean_object* v_env_588_; lean_object* v___x_589_; lean_object* v_toCold_590_; lean_object* v_mctx_591_; lean_object* v_lctx_592_; lean_object* v_options_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_585_ = lean_st_ref_get(v___y_583_);
v_env_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_env_586_);
lean_dec(v___x_585_);
v___x_587_ = 0;
v_env_588_ = l_Lean_Environment_setRecordingDeps(v_env_586_, v___x_587_);
v___x_589_ = lean_st_ref_get(v___y_581_);
v_toCold_590_ = lean_ctor_get(v___y_582_, 0);
v_mctx_591_ = lean_ctor_get(v___x_589_, 0);
lean_inc_ref(v_mctx_591_);
lean_dec(v___x_589_);
v_lctx_592_ = lean_ctor_get(v___y_580_, 2);
v_options_593_ = lean_ctor_get(v_toCold_590_, 2);
lean_inc_ref(v_options_593_);
lean_inc_ref(v_lctx_592_);
v___x_594_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_594_, 0, v_env_588_);
lean_ctor_set(v___x_594_, 1, v_mctx_591_);
lean_ctor_set(v___x_594_, 2, v_lctx_592_);
lean_ctor_set(v___x_594_, 3, v_options_593_);
v___x_595_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v_msgData_579_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_579_ = stack[0].m_obj;
lean_object* v___y_580_ = stack[1].m_obj;
lean_object* v___y_581_ = stack[2].m_obj;
lean_object* v___y_582_ = stack[3].m_obj;
lean_object* v___y_583_ = stack[4].m_obj;
lean_object* v_res_597_;
v_res_597_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
stack->m_obj
 = v_res_597_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_604_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_605_; double v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = lean_float_of_nat(v___x_605_);
return v___x_606_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_610_, lean_object* v_msg_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_ref_617_; lean_object* v___x_618_; lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_664_; 
v_ref_617_ = lean_ctor_get(v___y_614_, 2);
v___x_618_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_664_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_664_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_664_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v_traceState_624_; lean_object* v_env_625_; lean_object* v_nextMacroScope_626_; lean_object* v_ngen_627_; lean_object* v_auxDeclNGen_628_; lean_object* v_cache_629_; lean_object* v_recordedDeps_630_; lean_object* v_messages_631_; lean_object* v_infoState_632_; lean_object* v_snapshotTasks_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_663_; 
v___x_623_ = lean_st_ref_take(v___y_615_);
v_traceState_624_ = lean_ctor_get(v___x_623_, 4);
v_env_625_ = lean_ctor_get(v___x_623_, 0);
v_nextMacroScope_626_ = lean_ctor_get(v___x_623_, 1);
v_ngen_627_ = lean_ctor_get(v___x_623_, 2);
v_auxDeclNGen_628_ = lean_ctor_get(v___x_623_, 3);
v_cache_629_ = lean_ctor_get(v___x_623_, 5);
v_recordedDeps_630_ = lean_ctor_get(v___x_623_, 6);
v_messages_631_ = lean_ctor_get(v___x_623_, 7);
v_infoState_632_ = lean_ctor_get(v___x_623_, 8);
v_snapshotTasks_633_ = lean_ctor_get(v___x_623_, 9);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_663_ == 0)
{
v___x_635_ = v___x_623_;
v_isShared_636_ = v_isSharedCheck_663_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snapshotTasks_633_);
lean_inc(v_infoState_632_);
lean_inc(v_messages_631_);
lean_inc(v_recordedDeps_630_);
lean_inc(v_cache_629_);
lean_inc(v_traceState_624_);
lean_inc(v_auxDeclNGen_628_);
lean_inc(v_ngen_627_);
lean_inc(v_nextMacroScope_626_);
lean_inc(v_env_625_);
lean_dec(v___x_623_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_663_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
uint64_t v_tid_637_; lean_object* v_traces_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_662_; 
v_tid_637_ = lean_ctor_get_uint64(v_traceState_624_, sizeof(void*)*1);
v_traces_638_ = lean_ctor_get(v_traceState_624_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v_traceState_624_);
if (v_isSharedCheck_662_ == 0)
{
v___x_640_ = v_traceState_624_;
v_isShared_641_ = v_isSharedCheck_662_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_traces_638_);
lean_dec(v_traceState_624_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_662_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; double v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_642_ = lean_box(0);
v___x_643_ = lean_box(0);
v___x_644_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_645_ = 0;
v___x_646_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_647_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_647_, 0, v_cls_610_);
lean_ctor_set(v___x_647_, 1, v___x_643_);
lean_ctor_set(v___x_647_, 2, v___x_646_);
lean_ctor_set_float(v___x_647_, sizeof(void*)*3, v___x_644_);
lean_ctor_set_float(v___x_647_, sizeof(void*)*3 + 8, v___x_644_);
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*3 + 16, v___x_645_);
v___x_648_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_649_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v_a_619_);
lean_ctor_set(v___x_649_, 2, v___x_648_);
lean_inc(v_ref_617_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_ref_617_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = l_Lean_PersistentArray_push___redArg(v_traces_638_, v___x_650_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_651_);
v___x_653_ = v___x_640_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_651_);
lean_ctor_set_uint64(v_reuseFailAlloc_661_, sizeof(void*)*1, v_tid_637_);
v___x_653_ = v_reuseFailAlloc_661_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 4, v___x_653_);
v___x_655_ = v___x_635_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_env_625_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_nextMacroScope_626_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_ngen_627_);
lean_ctor_set(v_reuseFailAlloc_660_, 3, v_auxDeclNGen_628_);
lean_ctor_set(v_reuseFailAlloc_660_, 4, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_660_, 5, v_cache_629_);
lean_ctor_set(v_reuseFailAlloc_660_, 6, v_recordedDeps_630_);
lean_ctor_set(v_reuseFailAlloc_660_, 7, v_messages_631_);
lean_ctor_set(v_reuseFailAlloc_660_, 8, v_infoState_632_);
lean_ctor_set(v_reuseFailAlloc_660_, 9, v_snapshotTasks_633_);
v___x_655_ = v_reuseFailAlloc_660_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = lean_st_ref_put(v___y_615_, v___x_655_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_642_);
v___x_658_ = v___x_621_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_642_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_610_ = stack[0].m_obj;
lean_object* v_msg_611_ = stack[1].m_obj;
lean_object* v___y_612_ = stack[2].m_obj;
lean_object* v___y_613_ = stack[3].m_obj;
lean_object* v___y_614_ = stack[4].m_obj;
lean_object* v___y_615_ = stack[5].m_obj;
lean_object* v_res_665_;
v_res_665_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_610_, v_msg_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
stack->m_obj
 = v_res_665_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_666_, lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_666_, v_msg_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_681_, lean_object* v_mvarId_682_, lean_object* v_fields_683_, lean_object* v_sz_684_, lean_object* v___x_685_, lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
size_t v_sz_boxed_694_; size_t v___x_16224__boxed_695_; uint8_t v___x_16226__boxed_696_; lean_object* v_res_697_; 
v_sz_boxed_694_ = lean_unbox_usize(v_sz_684_);
lean_dec(v_sz_684_);
v___x_16224__boxed_695_ = lean_unbox_usize(v___x_685_);
lean_dec(v___x_685_);
v___x_16226__boxed_696_ = lean_unbox(v___x_687_);
v_res_697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_681_, v_mvarId_682_, v_fields_683_, v_sz_boxed_694_, v___x_16224__boxed_695_, v___x_686_, v___x_16226__boxed_696_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v_fields_683_);
return v_res_697_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_698_, lean_object* v_as_699_, size_t v_sz_700_, size_t v_i_701_, lean_object* v_b_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = lean_usize_dec_lt(v_i_701_, v_sz_700_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_b_702_);
return v___x_710_;
}
else
{
lean_object* v_a_711_; lean_object* v_toInductionSubgoal_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v_b_702_);
v_a_711_ = lean_array_uget(v_as_699_, v_i_701_);
v_toInductionSubgoal_712_ = lean_ctor_get(v_a_711_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v_a_711_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v_a_711_, 1);
lean_dec(v_unused_754_);
v___x_714_ = v_a_711_;
v_isShared_715_ = v_isSharedCheck_753_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_toInductionSubgoal_712_);
lean_dec(v_a_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_753_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_mvarId_716_; lean_object* v_fields_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; size_t v_sz_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___f_726_; lean_object* v___x_727_; 
v_mvarId_716_ = lean_ctor_get(v_toInductionSubgoal_712_, 0);
lean_inc_n(v_mvarId_716_, 2);
v_fields_717_ = lean_ctor_get(v_toInductionSubgoal_712_, 1);
lean_inc_ref(v_fields_717_);
v___x_718_ = lean_box(0);
v___x_719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_nat_dec_eq(v_val_698_, v___x_720_);
v_sz_722_ = lean_array_size(v_fields_717_);
v___x_723_ = lean_box_usize(v_sz_722_);
v___x_724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_725_ = lean_box(v___x_721_);
v___f_726_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_726_, 0, v_toInductionSubgoal_712_);
lean_closure_set(v___f_726_, 1, v_mvarId_716_);
lean_closure_set(v___f_726_, 2, v_fields_717_);
lean_closure_set(v___f_726_, 3, v___x_723_);
lean_closure_set(v___f_726_, 4, v___x_724_);
lean_closure_set(v___f_726_, 5, v___x_719_);
lean_closure_set(v___f_726_, 6, v___x_725_);
v___x_727_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_716_, v___f_726_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_744_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_744_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
uint8_t v___x_732_; 
v___x_732_ = lean_unbox(v_a_728_);
lean_dec(v_a_728_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_733_ = lean_box(v___x_721_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v___x_718_);
lean_ctor_set(v___x_714_, 0, v___x_734_);
v___x_736_ = v___x_714_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_718_);
v___x_736_ = v_reuseFailAlloc_740_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_736_);
v___x_738_ = v___x_730_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
else
{
size_t v___x_741_; size_t v___x_742_; 
lean_del_object(v___x_730_);
lean_del_object(v___x_714_);
v___x_741_ = ((size_t)1ULL);
v___x_742_ = lean_usize_add(v_i_701_, v___x_741_);
v_i_701_ = v___x_742_;
v_b_702_ = v___x_719_;
goto _start;
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_del_object(v___x_714_);
v_a_745_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_727_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_727_);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_698_ = stack[0].m_obj;
lean_object* v_as_699_ = stack[1].m_obj;
size_t v_sz_700_ = stack[2].m_num;
size_t v_i_701_ = stack[3].m_num;
lean_object* v_b_702_ = stack[4].m_obj;
lean_object* v___y_703_ = stack[5].m_obj;
lean_object* v___y_704_ = stack[6].m_obj;
lean_object* v___y_705_ = stack[7].m_obj;
lean_object* v___y_706_ = stack[8].m_obj;
lean_object* v___y_707_ = stack[9].m_obj;
lean_object* v_res_755_;
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_698_, v_as_699_, v_sz_700_, v_i_701_, v_b_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
stack->m_obj
 = v_res_755_;
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_767_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_768_ = l_Lean_Name_append(v___x_767_, v___x_766_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_771_ = l_Lean_stringToMessageData(v___x_770_);
return v___x_771_;
}
}
lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_772_, lean_object* v_fvarId_773_, lean_object* v___x_774_, uint8_t v___x_775_, lean_object* v___x_776_, lean_object* v_val_777_, uint8_t v___x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_MVarId_cases(v_mvarId_772_, v_fvarId_773_, v___x_774_, v___x_775_, v___x_776_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v_toCold_819_; lean_object* v_options_820_; uint8_t v_hasTrace_821_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v_toCold_819_ = lean_ctor_get(v___y_782_, 0);
v_options_820_ = lean_ctor_get(v_toCold_819_, 2);
v_hasTrace_821_ = lean_ctor_get_uint8(v_options_820_, sizeof(void*)*1);
if (v_hasTrace_821_ == 0)
{
v___y_788_ = v___y_779_;
v___y_789_ = v___y_780_;
v___y_790_ = v___y_781_;
v___y_791_ = v___y_782_;
v___y_792_ = v___y_783_;
goto v___jp_787_;
}
else
{
lean_object* v_inheritedTraceOptions_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_inheritedTraceOptions_822_ = lean_ctor_get(v_toCold_819_, 11);
v___x_823_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_824_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_825_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_822_, v_options_820_, v___x_824_);
if (v___x_825_ == 0)
{
v___y_788_ = v___y_779_;
v___y_789_ = v___y_780_;
v___y_790_ = v___y_781_;
v___y_791_ = v___y_782_;
v___y_792_ = v___y_783_;
goto v___jp_787_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_826_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_827_ = lean_array_get_size(v_a_786_);
v___x_828_ = l_Nat_reprFast(v___x_827_);
v___x_829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = l_Lean_MessageData_ofFormat(v___x_829_);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_826_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_823_, v___x_831_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_dec_ref_known(v___x_832_, 1);
v___y_788_ = v___y_779_;
v___y_789_ = v___y_780_;
v___y_790_ = v___y_781_;
v___y_791_ = v___y_782_;
v___y_792_ = v___y_783_;
goto v___jp_787_;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_a_786_);
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
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
}
v___jp_787_:
{
lean_object* v___x_793_; size_t v_sz_794_; size_t v___x_795_; lean_object* v___x_796_; 
v___x_793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_794_ = lean_array_size(v_a_786_);
v___x_795_ = ((size_t)0ULL);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_777_, v_a_786_, v_sz_794_, v___x_795_, v___x_793_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v_a_786_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_810_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_810_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_810_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_810_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_fst_801_; 
v_fst_801_ = lean_ctor_get(v_a_797_, 0);
lean_inc(v_fst_801_);
lean_dec(v_a_797_);
if (lean_obj_tag(v_fst_801_) == 0)
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_box(v___x_778_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_802_);
v___x_804_ = v___x_799_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_object* v_val_806_; lean_object* v___x_808_; 
v_val_806_ = lean_ctor_get(v_fst_801_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v_fst_801_, 1);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v_val_806_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_val_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_796_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_796_);
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
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_886_; 
v_a_841_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_886_ == 0)
{
v___x_843_ = v___x_785_;
v_isShared_844_ = v_isSharedCheck_886_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_785_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_886_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint8_t v___y_846_; uint8_t v___x_884_; 
v___x_884_ = l_Lean_Exception_isInterrupt(v_a_841_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; 
lean_inc(v_a_841_);
v___x_885_ = l_Lean_Exception_isRuntime(v_a_841_);
v___y_846_ = v___x_885_;
goto v___jp_845_;
}
else
{
v___y_846_ = v___x_884_;
goto v___jp_845_;
}
v___jp_845_:
{
if (v___y_846_ == 0)
{
lean_object* v_toCold_847_; lean_object* v_options_848_; uint8_t v_hasTrace_849_; 
v_toCold_847_ = lean_ctor_get(v___y_782_, 0);
v_options_848_ = lean_ctor_get(v_toCold_847_, 2);
v_hasTrace_849_ = lean_ctor_get_uint8(v_options_848_, sizeof(void*)*1);
if (v_hasTrace_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_852_; 
lean_dec(v_a_841_);
v___x_850_ = lean_box(v___x_775_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 0);
lean_ctor_set(v___x_843_, 0, v___x_850_);
v___x_852_ = v___x_843_;
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
else
{
lean_object* v_inheritedTraceOptions_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_inheritedTraceOptions_854_ = lean_ctor_get(v_toCold_847_, 11);
v___x_855_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_856_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_857_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_854_, v_options_848_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v_a_841_);
v___x_858_ = lean_box(v___x_775_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 0);
lean_ctor_set(v___x_843_, 0, v___x_858_);
v___x_860_ = v___x_843_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_del_object(v___x_843_);
v___x_862_ = l_Lean_Exception_toMessageData(v_a_841_);
v___x_863_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_855_, v___x_862_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_872_);
v___x_865_ = v___x_863_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_863_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = lean_box(v___x_775_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_867_);
v___x_869_ = v___x_865_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_863_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_863_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
else
{
lean_object* v___x_882_; 
if (v_isShared_844_ == 0)
{
v___x_882_ = v___x_843_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_841_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ElimEmptyInductive_elim___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_772_ = stack[0].m_obj;
lean_object* v_fvarId_773_ = stack[1].m_obj;
lean_object* v___x_774_ = stack[2].m_obj;
uint8_t v___x_775_ = stack[3].m_num;
lean_object* v___x_776_ = stack[4].m_obj;
lean_object* v_val_777_ = stack[5].m_obj;
uint8_t v___x_778_ = stack[6].m_num;
lean_object* v___y_779_ = stack[7].m_obj;
lean_object* v___y_780_ = stack[8].m_obj;
lean_object* v___y_781_ = stack[9].m_obj;
lean_object* v___y_782_ = stack[10].m_obj;
lean_object* v___y_783_ = stack[11].m_obj;
lean_object* v_res_887_;
v_res_887_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_772_, v_fvarId_773_, v___x_774_, v___x_775_, v___x_776_, v_val_777_, v___x_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_888_, lean_object* v_fvarId_889_, lean_object* v___x_890_, lean_object* v___x_891_, lean_object* v___x_892_, lean_object* v_val_893_, lean_object* v___x_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
uint8_t v___x_16346__boxed_901_; uint8_t v___x_16349__boxed_902_; lean_object* v_res_903_; 
v___x_16346__boxed_901_ = lean_unbox(v___x_891_);
v___x_16349__boxed_902_ = lean_unbox(v___x_894_);
v_res_903_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_888_, v_fvarId_889_, v___x_890_, v___x_16346__boxed_901_, v___x_892_, v_val_893_, v___x_16349__boxed_902_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec(v_val_893_);
return v_res_903_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_907_, lean_object* v_fvarId_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_919_ = lean_st_ref_get(v_a_909_);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_nat_dec_eq(v___x_919_, v___x_920_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___f_931_; lean_object* v___x_932_; 
v___x_922_ = 1;
v___x_923_ = lean_st_ref_take(v_a_909_);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_sub(v___x_923_, v___x_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_st_ref_put(v_a_909_, v___x_925_);
v___x_927_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_928_ = lean_box(0);
v___x_929_ = lean_box(v___x_921_);
v___x_930_ = lean_box(v___x_922_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_931_, 0, v_mvarId_907_);
lean_closure_set(v___f_931_, 1, v_fvarId_908_);
lean_closure_set(v___f_931_, 2, v___x_927_);
lean_closure_set(v___f_931_, 3, v___x_929_);
lean_closure_set(v___f_931_, 4, v___x_928_);
lean_closure_set(v___f_931_, 5, v___x_919_);
lean_closure_set(v___f_931_, 6, v___x_930_);
v___x_932_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_931_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
return v___x_932_;
}
else
{
lean_object* v_toCold_933_; lean_object* v_options_934_; uint8_t v_hasTrace_935_; 
lean_dec(v___x_919_);
lean_dec(v_fvarId_908_);
lean_dec(v_mvarId_907_);
v_toCold_933_ = lean_ctor_get(v_a_912_, 0);
v_options_934_ = lean_ctor_get(v_toCold_933_, 2);
v_hasTrace_935_ = lean_ctor_get_uint8(v_options_934_, sizeof(void*)*1);
if (v_hasTrace_935_ == 0)
{
goto v___jp_915_;
}
else
{
lean_object* v_inheritedTraceOptions_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_inheritedTraceOptions_936_ = lean_ctor_get(v_toCold_933_, 11);
v___x_937_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_938_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_939_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_936_, v_options_934_, v___x_938_);
if (v___x_939_ == 0)
{
goto v___jp_915_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_941_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_937_, v___x_940_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_dec_ref_known(v___x_941_, 1);
goto v___jp_915_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
v___jp_915_:
{
uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = 0;
v___x_917_ = lean_box(v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ElimEmptyInductive_elim_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_907_ = stack[0].m_obj;
lean_object* v_fvarId_908_ = stack[1].m_obj;
lean_object* v_a_909_ = stack[2].m_obj;
lean_object* v_a_910_ = stack[3].m_obj;
lean_object* v_a_911_ = stack[4].m_obj;
lean_object* v_a_912_ = stack[5].m_obj;
lean_object* v_a_913_ = stack[6].m_obj;
lean_object* v_res_950_;
v_res_950_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_907_, v_fvarId_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
stack->m_obj
 = v_res_950_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_951_, lean_object* v___x_952_, lean_object* v_as_953_, size_t v_sz_954_, size_t v_i_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_a_964_; uint8_t v___x_968_; 
v___x_968_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
lean_dec(v___x_952_);
lean_dec_ref(v___x_951_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v_b_956_);
return v___x_969_;
}
else
{
lean_object* v_subst_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
lean_dec_ref(v_b_956_);
v_subst_970_ = lean_ctor_get(v___x_951_, 2);
v___x_971_ = lean_box(0);
v___x_972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_973_ = lean_array_uget_borrowed(v_as_953_, v_i_955_);
lean_inc(v_subst_970_);
v___x_974_ = l_Lean_Meta_FVarSubst_apply(v_subst_970_, v_a_973_);
v___x_975_ = l_Lean_Expr_isFVar(v___x_974_);
if (v___x_975_ == 0)
{
lean_dec_ref(v___x_974_);
v_a_964_ = v___x_972_;
goto v___jp_963_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = l_Lean_Expr_fvarId_x21(v___x_974_);
lean_dec_ref(v___x_974_);
lean_inc(v___x_976_);
v___x_977_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_976_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; uint8_t v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = lean_unbox(v_a_978_);
lean_dec(v_a_978_);
if (v___x_979_ == 0)
{
lean_dec(v___x_976_);
v_a_964_ = v___x_972_;
goto v___jp_963_;
}
else
{
lean_object* v___x_980_; 
lean_inc(v___x_952_);
v___x_980_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_952_, v___x_976_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_992_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_992_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
uint8_t v___x_985_; 
v___x_985_ = lean_unbox(v_a_981_);
lean_dec(v_a_981_);
if (v___x_985_ == 0)
{
lean_del_object(v___x_983_);
v_a_964_ = v___x_972_;
goto v___jp_963_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
lean_dec(v___x_952_);
lean_dec_ref(v___x_951_);
v___x_986_ = lean_box(v___x_975_);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_971_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_988_);
v___x_990_ = v___x_983_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v___x_952_);
lean_dec_ref(v___x_951_);
v_a_993_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_980_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_980_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v___x_976_);
lean_dec(v___x_952_);
lean_dec_ref(v___x_951_);
v_a_1001_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_977_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_977_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
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
}
v___jp_963_:
{
size_t v___x_965_; size_t v___x_966_; 
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_add(v_i_955_, v___x_965_);
lean_inc_ref(v_a_964_);
v_i_955_ = v___x_966_;
v_b_956_ = v_a_964_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_951_ = stack[0].m_obj;
lean_object* v___x_952_ = stack[1].m_obj;
lean_object* v_as_953_ = stack[2].m_obj;
size_t v_sz_954_ = stack[3].m_num;
size_t v_i_955_ = stack[4].m_num;
lean_object* v_b_956_ = stack[5].m_obj;
lean_object* v___y_957_ = stack[6].m_obj;
lean_object* v___y_958_ = stack[7].m_obj;
lean_object* v___y_959_ = stack[8].m_obj;
lean_object* v___y_960_ = stack[9].m_obj;
lean_object* v___y_961_ = stack[10].m_obj;
lean_object* v_res_1009_;
v_res_1009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_951_, v___x_952_, v_as_953_, v_sz_954_, v_i_955_, v_b_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
stack->m_obj
 = v_res_1009_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_1010_, lean_object* v_mvarId_1011_, lean_object* v_fields_1012_, size_t v_sz_1013_, size_t v___x_1014_, lean_object* v___x_1015_, uint8_t v___x_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_1010_, v_mvarId_1011_, v_fields_1012_, v_sz_1013_, v___x_1014_, v___x_1015_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1037_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1037_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1037_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_fst_1028_; 
v_fst_1028_ = lean_ctor_get(v_a_1024_, 0);
lean_inc(v_fst_1028_);
lean_dec(v_a_1024_);
if (lean_obj_tag(v_fst_1028_) == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(v___x_1016_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1029_);
v___x_1031_ = v___x_1026_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_object* v_val_1033_; lean_object* v___x_1035_; 
v_val_1033_ = lean_ctor_get(v_fst_1028_, 0);
lean_inc(v_val_1033_);
lean_dec_ref_known(v_fst_1028_, 1);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v_val_1033_);
v___x_1035_ = v___x_1026_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_val_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
v_a_1038_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1023_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1023_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toInductionSubgoal_1010_ = stack[0].m_obj;
lean_object* v_mvarId_1011_ = stack[1].m_obj;
lean_object* v_fields_1012_ = stack[2].m_obj;
size_t v_sz_1013_ = stack[3].m_num;
size_t v___x_1014_ = stack[4].m_num;
lean_object* v___x_1015_ = stack[5].m_obj;
uint8_t v___x_1016_ = stack[6].m_num;
lean_object* v___y_1017_ = stack[7].m_obj;
lean_object* v___y_1018_ = stack[8].m_obj;
lean_object* v___y_1019_ = stack[9].m_obj;
lean_object* v___y_1020_ = stack[10].m_obj;
lean_object* v___y_1021_ = stack[11].m_obj;
lean_object* v_res_1046_;
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_1010_, v_mvarId_1011_, v_fields_1012_, v_sz_1013_, v___x_1014_, v___x_1015_, v___x_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
stack->m_obj
 = v_res_1046_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1047_, lean_object* v_as_1048_, lean_object* v_sz_1049_, lean_object* v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
size_t v_sz_boxed_1058_; size_t v_i_boxed_1059_; lean_object* v_res_1060_; 
v_sz_boxed_1058_ = lean_unbox_usize(v_sz_1049_);
lean_dec(v_sz_1049_);
v_i_boxed_1059_ = lean_unbox_usize(v_i_1050_);
lean_dec(v_i_1050_);
v_res_1060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1047_, v_as_1048_, v_sz_boxed_1058_, v_i_boxed_1059_, v_b_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v_as_1048_);
lean_dec(v_val_1047_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1061_, lean_object* v___x_1062_, lean_object* v_as_1063_, lean_object* v_sz_1064_, lean_object* v_i_1065_, lean_object* v_b_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
size_t v_sz_boxed_1073_; size_t v_i_boxed_1074_; lean_object* v_res_1075_; 
v_sz_boxed_1073_ = lean_unbox_usize(v_sz_1064_);
lean_dec(v_sz_1064_);
v_i_boxed_1074_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_res_1075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1061_, v___x_1062_, v_as_1063_, v_sz_boxed_1073_, v_i_boxed_1074_, v_b_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v_as_1063_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1076_, lean_object* v_fvarId_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1076_, v_fvarId_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
return v_res_1084_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1085_, lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1085_, v_msg_1086_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1085_ = stack[0].m_obj;
lean_object* v_msg_1086_ = stack[1].m_obj;
lean_object* v___y_1087_ = stack[2].m_obj;
lean_object* v___y_1088_ = stack[3].m_obj;
lean_object* v___y_1089_ = stack[4].m_obj;
lean_object* v___y_1090_ = stack[5].m_obj;
lean_object* v___y_1091_ = stack[6].m_obj;
lean_object* v_res_1094_;
v_res_1094_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1085_, v_msg_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
stack->m_obj
 = v_res_1094_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1095_, lean_object* v_msg_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1095_, v_msg_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
return v_res_1103_;
}
}
lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Meta_saveState___redArg(v___y_1106_, v___y_1108_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___y_1113_; lean_object* v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1134_; lean_object* v_a_1135_; lean_object* v___x_1138_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
lean_inc(v___y_1108_);
lean_inc_ref(v___y_1107_);
lean_inc(v___y_1106_);
lean_inc_ref(v___y_1105_);
v___x_1138_ = lean_apply_5(v_x_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, lean_box(0));
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; uint8_t v___x_1140_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
v___x_1140_ = lean_unbox(v_a_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref_known(v___x_1138_, 1);
lean_inc(v_a_1111_);
v___x_1141_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1111_, v___y_1106_, v___y_1108_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_a_1111_);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v___x_1141_, 0);
lean_dec(v_unused_1149_);
v___x_1143_ = v___x_1141_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_dec(v___x_1141_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v_a_1139_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1139_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_a_1139_);
v_a_1150_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1141_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1141_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
lean_inc(v_a_1150_);
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
v___y_1134_ = v___x_1155_;
v_a_1135_ = v_a_1150_;
goto v___jp_1133_;
}
}
}
}
else
{
lean_dec(v_a_1139_);
lean_dec(v_a_1111_);
return v___x_1138_;
}
}
else
{
lean_object* v_a_1158_; 
v_a_1158_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1158_);
v___y_1134_ = v___x_1138_;
v_a_1135_ = v_a_1158_;
goto v___jp_1133_;
}
v___jp_1112_:
{
if (v___y_1115_ == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref(v___y_1114_);
v___x_1116_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1111_, v___y_1106_, v___y_1108_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v___x_1116_, 0);
lean_dec(v_unused_1124_);
v___x_1118_ = v___x_1116_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_dec(v___x_1116_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v___y_1113_);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___y_1113_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v___y_1113_);
v_a_1125_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1116_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1116_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_dec_ref(v___y_1113_);
lean_dec(v_a_1111_);
return v___y_1114_;
}
}
v___jp_1133_:
{
uint8_t v___x_1136_; 
v___x_1136_ = l_Lean_Exception_isInterrupt(v_a_1135_);
if (v___x_1136_ == 0)
{
uint8_t v___x_1137_; 
lean_inc_ref(v_a_1135_);
v___x_1137_ = l_Lean_Exception_isRuntime(v_a_1135_);
v___y_1113_ = v_a_1135_;
v___y_1114_ = v___y_1134_;
v___y_1115_ = v___x_1137_;
goto v___jp_1112_;
}
else
{
v___y_1113_ = v_a_1135_;
v___y_1114_ = v___y_1134_;
v___y_1115_ = v___x_1136_;
goto v___jp_1112_;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_x_1104_);
v_a_1159_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1110_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1110_);
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
LEAN_EXPORT void l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1104_ = stack[0].m_obj;
lean_object* v___y_1105_ = stack[1].m_obj;
lean_object* v___y_1106_ = stack[2].m_obj;
lean_object* v___y_1107_ = stack[3].m_obj;
lean_object* v___y_1108_ = stack[4].m_obj;
lean_object* v_res_1167_;
v_res_1167_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1174_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1175_, v_x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v_a_1191_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1182_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1182_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1175_ = stack[0].m_obj;
lean_object* v_x_1176_ = stack[1].m_obj;
lean_object* v___y_1177_ = stack[2].m_obj;
lean_object* v___y_1178_ = stack[3].m_obj;
lean_object* v___y_1179_ = stack[4].m_obj;
lean_object* v___y_1180_ = stack[5].m_obj;
lean_object* v_res_1199_;
v_res_1199_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1175_, v_x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
stack->m_obj
 = v_res_1199_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1200_, v_x_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1208_, lean_object* v_mvarId_1209_, lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1209_, v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1209_ = stack[1].m_obj;
lean_object* v_x_1210_ = stack[2].m_obj;
lean_object* v___y_1211_ = stack[3].m_obj;
lean_object* v___y_1212_ = stack[4].m_obj;
lean_object* v___y_1213_ = stack[5].m_obj;
lean_object* v___y_1214_ = stack[6].m_obj;
lean_object* v_res_1217_;
v_res_1217_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_box(0), v_mvarId_1209_, v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
stack->m_obj
 = v_res_1217_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1218_, lean_object* v_mvarId_1219_, lean_object* v_x_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1218_, v_mvarId_1219_, v_x_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1226_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1227_, lean_object* v_fuel_1228_, lean_object* v_fvarId_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_MVarId_exfalso(v_mvarId_1227_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1237_ = lean_st_mk_ref(v_fuel_1228_);
v___x_1238_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1236_, v_fvarId_1229_, v___x_1237_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1247_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = lean_st_ref_get(v___x_1237_);
lean_dec(v___x_1237_);
lean_dec(v___x_1243_);
if (v_isShared_1242_ == 0)
{
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1239_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_dec(v___x_1237_);
return v___x_1238_;
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_fvarId_1229_);
lean_dec(v_fuel_1228_);
v_a_1248_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1235_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1235_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1227_ = stack[0].m_obj;
lean_object* v_fuel_1228_ = stack[1].m_obj;
lean_object* v_fvarId_1229_ = stack[2].m_obj;
lean_object* v___y_1230_ = stack[3].m_obj;
lean_object* v___y_1231_ = stack[4].m_obj;
lean_object* v___y_1232_ = stack[5].m_obj;
lean_object* v___y_1233_ = stack[6].m_obj;
lean_object* v_res_1256_;
v_res_1256_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1227_, v_fuel_1228_, v_fvarId_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1257_, lean_object* v_fuel_1258_, lean_object* v_fvarId_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1257_, v_fuel_1258_, v_fvarId_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1265_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1266_, lean_object* v___f_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1266_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; uint8_t v___x_1275_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v___x_1275_ = lean_unbox(v_a_1274_);
if (v___x_1275_ == 0)
{
lean_dec_ref(v___f_1267_);
return v___x_1273_;
}
else
{
lean_object* v___x_1276_; 
lean_dec_ref_known(v___x_1273_, 1);
v___x_1276_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1276_;
}
}
else
{
lean_dec_ref(v___f_1267_);
return v___x_1273_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1266_ = stack[0].m_obj;
lean_object* v___f_1267_ = stack[1].m_obj;
lean_object* v___y_1268_ = stack[2].m_obj;
lean_object* v___y_1269_ = stack[3].m_obj;
lean_object* v___y_1270_ = stack[4].m_obj;
lean_object* v___y_1271_ = stack[5].m_obj;
lean_object* v_res_1277_;
v_res_1277_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1266_, v___f_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
stack->m_obj
 = v_res_1277_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1278_, lean_object* v___f_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1278_, v___f_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
return v_res_1285_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1286_, lean_object* v_fvarId_1287_, lean_object* v_fuel_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v___f_1294_; lean_object* v___f_1295_; lean_object* v___x_1296_; 
lean_inc(v_fvarId_1287_);
lean_inc(v_mvarId_1286_);
v___f_1294_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1294_, 0, v_mvarId_1286_);
lean_closure_set(v___f_1294_, 1, v_fuel_1288_);
lean_closure_set(v___f_1294_, 2, v_fvarId_1287_);
v___f_1295_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1295_, 0, v_fvarId_1287_);
lean_closure_set(v___f_1295_, 1, v___f_1294_);
v___x_1296_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1286_, v___f_1295_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
return v___x_1296_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1286_ = stack[0].m_obj;
lean_object* v_fvarId_1287_ = stack[1].m_obj;
lean_object* v_fuel_1288_ = stack[2].m_obj;
lean_object* v_a_1289_ = stack[3].m_obj;
lean_object* v_a_1290_ = stack[4].m_obj;
lean_object* v_a_1291_ = stack[5].m_obj;
lean_object* v_a_1292_ = stack[6].m_obj;
lean_object* v_res_1297_;
v_res_1297_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1286_, v_fvarId_1287_, v_fuel_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
stack->m_obj
 = v_res_1297_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1298_, lean_object* v_fvarId_1299_, lean_object* v_fuel_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1298_, v_fvarId_1299_, v_fuel_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
return v_res_1306_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1307_){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1307_ = stack[0].m_obj;
uint8_t v_res_1309_;
v_res_1309_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1307_);
stack->m_num = v_res_1309_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1310_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1313_, lean_object* v_acc_1314_){
_start:
{
if (lean_obj_tag(v_e_1313_) == 7)
{
lean_object* v_binderType_1315_; lean_object* v_body_1316_; uint8_t v___y_1318_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_binderType_1315_ = lean_ctor_get(v_e_1313_, 1);
v_body_1316_ = lean_ctor_get(v_e_1313_, 2);
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = lean_expr_has_loose_bvar(v_body_1316_, v___x_1322_);
if (v___x_1323_ == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = l_Lean_Expr_isEq(v_binderType_1315_);
if (v___x_1324_ == 0)
{
uint8_t v___x_1325_; 
v___x_1325_ = l_Lean_Expr_isHEq(v_binderType_1315_);
v___y_1318_ = v___x_1325_;
goto v___jp_1317_;
}
else
{
v___y_1318_ = v___x_1324_;
goto v___jp_1317_;
}
}
else
{
uint8_t v___x_1326_; 
v___x_1326_ = 0;
v___y_1318_ = v___x_1326_;
goto v___jp_1317_;
}
v___jp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_box(v___y_1318_);
v___x_1320_ = lean_array_push(v_acc_1314_, v___x_1319_);
v_e_1313_ = v_body_1316_;
v_acc_1314_ = v___x_1320_;
goto _start;
}
}
else
{
return v_acc_1314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1327_, lean_object* v_acc_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1327_, v_acc_1328_);
lean_dec_ref(v_e_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1332_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1334_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1332_, v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Meta_mkGenDiseqMask(v_e_1335_);
lean_dec_ref(v_e_1335_);
return v_res_1336_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___f_1344_; lean_object* v___x_4344__overap_1345_; lean_object* v___x_1346_; 
v___f_1344_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1345_ = lean_panic_fn_borrowed(v___f_1344_, v_msg_1338_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
v___x_1346_ = lean_apply_5(v___x_4344__overap_1345_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, lean_box(0));
return v___x_1346_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1338_ = stack[0].m_obj;
lean_object* v___y_1339_ = stack[1].m_obj;
lean_object* v___y_1340_ = stack[2].m_obj;
lean_object* v___y_1341_ = stack[3].m_obj;
lean_object* v___y_1342_ = stack[4].m_obj;
lean_object* v_res_1347_;
v_res_1347_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
stack->m_obj
 = v_res_1347_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1354_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v___x_1358_; 
v___x_1358_ = l_Lean_Expr_hasMVar(v_e_1355_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_e_1355_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; lean_object* v_mctx_1361_; lean_object* v___x_1362_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; lean_object* v___x_1365_; lean_object* v_cache_1366_; lean_object* v_zetaDeltaFVarIds_1367_; lean_object* v_postponed_1368_; lean_object* v_diag_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1378_; 
v___x_1360_ = lean_st_ref_get(v___y_1356_);
v_mctx_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc_ref(v_mctx_1361_);
lean_dec(v___x_1360_);
v___x_1362_ = l_Lean_instantiateMVarsCore(v_mctx_1361_, v_e_1355_);
v_fst_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_fst_1363_);
v_snd_1364_ = lean_ctor_get(v___x_1362_, 1);
lean_inc(v_snd_1364_);
lean_dec_ref(v___x_1362_);
v___x_1365_ = lean_st_ref_take(v___y_1356_);
v_cache_1366_ = lean_ctor_get(v___x_1365_, 1);
v_zetaDeltaFVarIds_1367_ = lean_ctor_get(v___x_1365_, 2);
v_postponed_1368_ = lean_ctor_get(v___x_1365_, 3);
v_diag_1369_ = lean_ctor_get(v___x_1365_, 4);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1365_, 0);
lean_dec(v_unused_1379_);
v___x_1371_ = v___x_1365_;
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_diag_1369_);
lean_inc(v_postponed_1368_);
lean_inc(v_zetaDeltaFVarIds_1367_);
lean_inc(v_cache_1366_);
lean_dec(v___x_1365_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_snd_1364_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_snd_1364_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_cache_1366_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_zetaDeltaFVarIds_1367_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_postponed_1368_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_diag_1369_);
v___x_1374_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_st_ref_put(v___y_1356_, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_fst_1363_);
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1355_ = stack[0].m_obj;
lean_object* v___y_1356_ = stack[1].m_obj;
lean_object* v_res_1380_;
v_res_1380_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1355_, v___y_1356_);
stack->m_obj
 = v_res_1380_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1381_, v___y_1382_);
lean_dec(v___y_1382_);
return v_res_1384_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1385_, v___y_1387_);
return v___x_1391_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1385_ = stack[0].m_obj;
lean_object* v___y_1386_ = stack[1].m_obj;
lean_object* v___y_1387_ = stack[2].m_obj;
lean_object* v___y_1388_ = stack[3].m_obj;
lean_object* v___y_1389_ = stack[4].m_obj;
lean_object* v_res_1392_;
v_res_1392_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
stack->m_obj
 = v_res_1392_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1400_, uint8_t v_allowLevelAssignments_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1401_, v_k_1400_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
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
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_a_1416_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1407_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1407_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1400_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_1401_ = stack[1].m_num;
lean_object* v___y_1402_ = stack[2].m_obj;
lean_object* v___y_1403_ = stack[3].m_obj;
lean_object* v___y_1404_ = stack[4].m_obj;
lean_object* v___y_1405_ = stack[5].m_obj;
lean_object* v_res_1424_;
v_res_1424_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1400_, v_allowLevelAssignments_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
stack->m_obj
 = v_res_1424_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1425_, lean_object* v_allowLevelAssignments_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1432_; lean_object* v_res_1433_; 
v_allowLevelAssignments_boxed_1432_ = lean_unbox(v_allowLevelAssignments_1426_);
v_res_1433_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1425_, v_allowLevelAssignments_boxed_1432_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1433_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1434_, lean_object* v_k_1435_, uint8_t v_allowLevelAssignments_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1435_, v_allowLevelAssignments_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1435_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_1436_ = stack[2].m_num;
lean_object* v___y_1437_ = stack[3].m_obj;
lean_object* v___y_1438_ = stack[4].m_obj;
lean_object* v___y_1439_ = stack[5].m_obj;
lean_object* v___y_1440_ = stack[6].m_obj;
lean_object* v_res_1443_;
v_res_1443_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_box(0), v_k_1435_, v_allowLevelAssignments_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
stack->m_obj
 = v_res_1443_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_k_1445_, lean_object* v_allowLevelAssignments_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1452_; lean_object* v_res_1453_; 
v_allowLevelAssignments_boxed_1452_ = lean_unbox(v_allowLevelAssignments_1446_);
v_res_1453_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1444_, v_k_1445_, v_allowLevelAssignments_boxed_1452_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1453_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1456_, size_t v_sz_1457_, size_t v_i_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_a_1466_; uint8_t v___x_1470_; 
v___x_1470_ = lean_usize_dec_lt(v_i_1458_, v_sz_1457_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_b_1459_);
return v___x_1471_;
}
else
{
lean_object* v_snd_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1634_; 
v_snd_1472_ = lean_ctor_get(v_b_1459_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_b_1459_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v_b_1459_, 0);
lean_dec(v_unused_1635_);
v___x_1474_ = v_b_1459_;
v_isShared_1475_ = v_isSharedCheck_1634_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_snd_1472_);
lean_dec(v_b_1459_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1634_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_array_1476_; lean_object* v_start_1477_; lean_object* v_stop_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_array_1476_ = lean_ctor_get(v_snd_1472_, 0);
v_start_1477_ = lean_ctor_get(v_snd_1472_, 1);
v_stop_1478_ = lean_ctor_get(v_snd_1472_, 2);
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_nat_dec_lt(v_start_1477_, v_stop_1478_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1482_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1479_);
v___x_1482_ = v___x_1474_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_snd_1472_);
v___x_1482_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
else
{
lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1630_; 
lean_inc(v_stop_1478_);
lean_inc(v_start_1477_);
lean_inc_ref(v_array_1476_);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_snd_1472_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; lean_object* v_unused_1632_; lean_object* v_unused_1633_; 
v_unused_1631_ = lean_ctor_get(v_snd_1472_, 2);
lean_dec(v_unused_1631_);
v_unused_1632_ = lean_ctor_get(v_snd_1472_, 1);
lean_dec(v_unused_1632_);
v_unused_1633_ = lean_ctor_get(v_snd_1472_, 0);
lean_dec(v_unused_1633_);
v___x_1486_ = v_snd_1472_;
v_isShared_1487_ = v_isSharedCheck_1630_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v_snd_1472_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1630_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1488_ = lean_array_fget(v_array_1476_, v_start_1477_);
v___x_1489_ = lean_unsigned_to_nat(1u);
v___x_1490_ = lean_nat_add(v_start_1477_, v___x_1489_);
lean_dec(v_start_1477_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v___x_1490_);
v___x_1492_ = v___x_1486_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_array_1476_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_stop_1478_);
v___x_1492_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
uint8_t v___x_1493_; 
v___x_1493_ = lean_unbox(v___x_1488_);
lean_dec(v___x_1488_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1495_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1492_);
lean_ctor_set(v___x_1474_, 0, v___x_1479_);
v___x_1495_ = v___x_1474_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___x_1492_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
v_a_1466_ = v___x_1495_;
goto v___jp_1465_;
}
}
else
{
lean_object* v_a_1497_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___x_1569_; 
v_a_1497_ = lean_array_uget_borrowed(v_as_1456_, v_i_1458_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v_a_1497_);
v___x_1569_ = lean_infer_type(v_a_1497_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = l_Lean_Meta_matchEq_x3f(v_a_1570_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
if (lean_obj_tag(v_a_1572_) == 1)
{
lean_object* v_val_1573_; lean_object* v_snd_1574_; lean_object* v_fst_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1611_; 
v_val_1573_ = lean_ctor_get(v_a_1572_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v_a_1572_, 1);
v_snd_1574_ = lean_ctor_get(v_val_1573_, 1);
lean_inc(v_snd_1574_);
lean_dec(v_val_1573_);
v_fst_1575_ = lean_ctor_get(v_snd_1574_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_snd_1574_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v_snd_1574_, 1);
lean_dec(v_unused_1612_);
v___x_1577_ = v_snd_1574_;
v_isShared_1578_ = v_isSharedCheck_1611_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_fst_1575_);
lean_dec(v_snd_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1611_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Meta_mkEqRefl(v_fst_1575_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
lean_inc(v_a_1497_);
v___x_1581_ = l_Lean_Meta_isExprDefEq(v_a_1497_, v_a_1580_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1594_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1594_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1594_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_unbox(v_a_1582_);
lean_dec(v_a_1582_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_del_object(v___x_1474_);
v___x_1587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v___x_1492_);
lean_ctor_set(v___x_1577_, 0, v___x_1587_);
v___x_1589_ = v___x_1577_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1492_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1589_);
v___x_1591_ = v___x_1584_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
lean_del_object(v___x_1584_);
lean_del_object(v___x_1577_);
v___y_1499_ = v___y_1460_;
v___y_1500_ = v___y_1461_;
v___y_1501_ = v___y_1462_;
v___y_1502_ = v___y_1463_;
goto v___jp_1498_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_del_object(v___x_1577_);
lean_dec_ref(v___x_1492_);
lean_del_object(v___x_1474_);
v_a_1595_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1581_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1581_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_del_object(v___x_1577_);
lean_dec_ref(v___x_1492_);
lean_del_object(v___x_1474_);
v_a_1603_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1579_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1579_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_dec(v_a_1572_);
v___y_1499_ = v___y_1460_;
v___y_1500_ = v___y_1461_;
v___y_1501_ = v___y_1462_;
v___y_1502_ = v___y_1463_;
goto v___jp_1498_;
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v___x_1492_);
lean_del_object(v___x_1474_);
v_a_1613_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1571_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1571_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v___x_1492_);
lean_del_object(v___x_1474_);
v_a_1621_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1569_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1569_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
v___jp_1498_:
{
lean_object* v___x_1503_; 
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
lean_inc(v_a_1497_);
v___x_1503_ = lean_infer_type(v_a_1497_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = l_Lean_Meta_matchHEq_x3f(v_a_1504_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
if (lean_obj_tag(v_a_1506_) == 1)
{
lean_object* v_val_1507_; lean_object* v_snd_1508_; lean_object* v_fst_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1548_; 
lean_del_object(v___x_1474_);
v_val_1507_ = lean_ctor_get(v_a_1506_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v_a_1506_, 1);
v_snd_1508_ = lean_ctor_get(v_val_1507_, 1);
lean_inc(v_snd_1508_);
lean_dec(v_val_1507_);
v_fst_1509_ = lean_ctor_get(v_snd_1508_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_snd_1508_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_snd_1508_, 1);
lean_dec(v_unused_1549_);
v___x_1511_ = v_snd_1508_;
v_isShared_1512_ = v_isSharedCheck_1548_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_fst_1509_);
lean_dec(v_snd_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1548_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Meta_mkHEqRefl(v_fst_1509_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
lean_inc(v_a_1497_);
v___x_1515_ = l_Lean_Meta_isExprDefEq(v_a_1497_, v_a_1514_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1531_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1531_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1531_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint8_t v___x_1520_; 
v___x_1520_ = lean_unbox(v_a_1516_);
lean_dec(v_a_1516_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1492_);
lean_ctor_set(v___x_1511_, 0, v___x_1521_);
v___x_1523_ = v___x_1511_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1492_);
v___x_1523_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1523_);
v___x_1525_ = v___x_1518_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
lean_object* v___x_1529_; 
lean_del_object(v___x_1518_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1492_);
lean_ctor_set(v___x_1511_, 0, v___x_1479_);
v___x_1529_ = v___x_1511_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1492_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
v_a_1466_ = v___x_1529_;
goto v___jp_1465_;
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_del_object(v___x_1511_);
lean_dec_ref(v___x_1492_);
v_a_1532_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1515_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1515_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_del_object(v___x_1511_);
lean_dec_ref(v___x_1492_);
v_a_1540_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1513_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1513_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
else
{
lean_object* v___x_1551_; 
lean_dec(v_a_1506_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1492_);
lean_ctor_set(v___x_1474_, 0, v___x_1479_);
v___x_1551_ = v___x_1474_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1492_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
v_a_1466_ = v___x_1551_;
goto v___jp_1465_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v___x_1492_);
lean_del_object(v___x_1474_);
v_a_1553_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1505_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1505_);
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
lean_dec_ref(v___x_1492_);
lean_del_object(v___x_1474_);
v_a_1561_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1503_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1503_);
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
}
}
}
}
}
v___jp_1465_:
{
size_t v___x_1467_; size_t v___x_1468_; 
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = lean_usize_add(v_i_1458_, v___x_1467_);
v_i_1458_ = v___x_1468_;
v_b_1459_ = v_a_1466_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1456_ = stack[0].m_obj;
size_t v_sz_1457_ = stack[1].m_num;
size_t v_i_1458_ = stack[2].m_num;
lean_object* v_b_1459_ = stack[3].m_obj;
lean_object* v___y_1460_ = stack[4].m_obj;
lean_object* v___y_1461_ = stack[5].m_obj;
lean_object* v___y_1462_ = stack[6].m_obj;
lean_object* v___y_1463_ = stack[7].m_obj;
lean_object* v_res_1636_;
v_res_1636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1456_, v_sz_1457_, v_i_1458_, v_b_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
stack->m_obj
 = v_res_1636_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1637_, lean_object* v_sz_1638_, lean_object* v_i_1639_, lean_object* v_b_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
size_t v_sz_boxed_1646_; size_t v_i_boxed_1647_; lean_object* v_res_1648_; 
v_sz_boxed_1646_ = lean_unbox_usize(v_sz_1638_);
lean_dec(v_sz_1638_);
v_i_boxed_1647_ = lean_unbox_usize(v_i_1639_);
lean_dec(v_i_1639_);
v_res_1648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1637_, v_sz_boxed_1646_, v_i_boxed_1647_, v_b_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v_as_1637_);
return v_res_1648_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1649_, uint8_t v___x_1650_, lean_object* v_localDecl_1651_, lean_object* v_mvarId_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; 
lean_inc_ref(v___x_1649_);
v___x_1658_ = l_Lean_Meta_forallMetaTelescope(v___x_1649_, v___x_1650_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_fst_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1749_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v_fst_1660_ = lean_ctor_get(v_a_1659_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_a_1659_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v_a_1659_, 1);
lean_dec(v_unused_1750_);
v___x_1662_ = v_a_1659_;
v_isShared_1663_ = v_isSharedCheck_1749_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_fst_1660_);
lean_dec(v_a_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1749_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1664_ = l_Lean_Meta_mkGenDiseqMask(v___x_1649_);
lean_dec_ref(v___x_1649_);
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = lean_array_get_size(v___x_1664_);
v___x_1667_ = l_Array_toSubarray___redArg(v___x_1664_, v___x_1665_, v___x_1666_);
v___x_1668_ = lean_box(0);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1667_);
lean_ctor_set(v___x_1662_, 0, v___x_1668_);
v___x_1670_ = v___x_1662_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___x_1667_);
v___x_1670_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
size_t v_sz_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
v_sz_1671_ = lean_array_size(v_fst_1660_);
v___x_1672_ = ((size_t)0ULL);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1660_, v_sz_1671_, v___x_1672_, v___x_1670_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1739_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1739_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1739_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v_fst_1678_; 
v_fst_1678_ = lean_ctor_get(v_a_1674_, 0);
lean_inc(v_fst_1678_);
lean_dec(v_a_1674_);
if (lean_obj_tag(v_fst_1678_) == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1734_; 
lean_del_object(v___x_1676_);
v___x_1679_ = l_Lean_LocalDecl_toExpr(v_localDecl_1651_);
v___x_1680_ = l_Lean_mkAppN(v___x_1679_, v_fst_1660_);
lean_dec(v_fst_1660_);
v___x_1681_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1680_, v___y_1654_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1734_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1734_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; 
lean_inc(v_a_1682_);
v___x_1686_ = l_Lean_Meta_hasAssignableMVar(v_a_1682_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1725_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1725_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1725_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_unbox(v_a_1687_);
lean_dec(v_a_1687_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
lean_del_object(v___x_1689_);
v___x_1692_ = l_Lean_MVarId_getType(v_mvarId_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = l_Lean_Meta_mkFalseElim(v_a_1693_, v_a_1682_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1705_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1705_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1705_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 1);
lean_ctor_set(v___x_1684_, 0, v_a_1695_);
v___x_1700_ = v___x_1684_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1700_);
v___x_1702_ = v___x_1697_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
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
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_del_object(v___x_1684_);
v_a_1706_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1694_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1694_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_del_object(v___x_1684_);
lean_dec(v_a_1682_);
v_a_1714_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1692_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1692_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v___x_1723_; 
lean_del_object(v___x_1684_);
lean_dec(v_a_1682_);
lean_dec(v_mvarId_1652_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1668_);
v___x_1723_ = v___x_1689_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1668_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_del_object(v___x_1684_);
lean_dec(v_a_1682_);
lean_dec(v_mvarId_1652_);
v_a_1726_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1686_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1686_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
else
{
lean_object* v_val_1735_; lean_object* v___x_1737_; 
lean_dec(v_fst_1660_);
lean_dec(v_mvarId_1652_);
lean_dec_ref(v_localDecl_1651_);
v_val_1735_ = lean_ctor_get(v_fst_1678_, 0);
lean_inc(v_val_1735_);
lean_dec_ref_known(v_fst_1678_, 1);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v_val_1735_);
v___x_1737_ = v___x_1676_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_val_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_fst_1660_);
lean_dec(v_mvarId_1652_);
lean_dec_ref(v_localDecl_1651_);
v_a_1740_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1673_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1673_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_mvarId_1652_);
lean_dec_ref(v_localDecl_1651_);
lean_dec_ref(v___x_1649_);
v_a_1751_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1658_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1658_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1649_ = stack[0].m_obj;
uint8_t v___x_1650_ = stack[1].m_num;
lean_object* v_localDecl_1651_ = stack[2].m_obj;
lean_object* v_mvarId_1652_ = stack[3].m_obj;
lean_object* v___y_1653_ = stack[4].m_obj;
lean_object* v___y_1654_ = stack[5].m_obj;
lean_object* v___y_1655_ = stack[6].m_obj;
lean_object* v___y_1656_ = stack[7].m_obj;
lean_object* v_res_1759_;
v_res_1759_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1649_, v___x_1650_, v_localDecl_1651_, v_mvarId_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
stack->m_obj
 = v_res_1759_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1760_, lean_object* v___x_1761_, lean_object* v_localDecl_1762_, lean_object* v_mvarId_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v___x_6339__boxed_1769_; lean_object* v_res_1770_; 
v___x_6339__boxed_1769_ = lean_unbox(v___x_1761_);
v_res_1770_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1760_, v___x_6339__boxed_1769_, v_localDecl_1762_, v_mvarId_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1775_ = lean_unsigned_to_nat(2u);
v___x_1776_ = lean_unsigned_to_nat(120u);
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1779_ = l_mkPanicMessageWithDecl(v___x_1778_, v___x_1777_, v___x_1776_, v___x_1775_, v___x_1774_);
return v___x_1779_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1780_, lean_object* v_localDecl_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = l_Lean_LocalDecl_type(v_localDecl_1781_);
lean_inc_ref(v___x_1787_);
v___x_1788_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_localDecl_1781_);
lean_dec(v_mvarId_1780_);
v___x_1789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1790_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1789_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
return v___x_1790_;
}
else
{
uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___f_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1791_ = 0;
v___x_1792_ = lean_box(v___x_1791_);
lean_inc(v_mvarId_1780_);
v___f_1793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1793_, 0, v___x_1787_);
lean_closure_set(v___f_1793_, 1, v___x_1792_);
lean_closure_set(v___f_1793_, 2, v_localDecl_1781_);
lean_closure_set(v___f_1793_, 3, v_mvarId_1780_);
v___x_1794_ = 0;
v___x_1795_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1793_, v___x_1794_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1815_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1815_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1815_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
if (lean_obj_tag(v_a_1796_) == 1)
{
lean_object* v_val_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1809_; 
lean_del_object(v___x_1798_);
v_val_1800_ = lean_ctor_get(v_a_1796_, 0);
lean_inc(v_val_1800_);
lean_dec_ref_known(v_a_1796_, 1);
v___x_1801_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1780_, v_val_1800_, v_a_1783_);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v___x_1801_, 0);
lean_dec(v_unused_1810_);
v___x_1803_ = v___x_1801_;
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
else
{
lean_dec(v___x_1801_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = lean_box(v___x_1788_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1805_);
v___x_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
lean_dec(v_a_1796_);
lean_dec(v_mvarId_1780_);
v___x_1811_ = lean_box(v___x_1794_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1811_);
v___x_1813_ = v___x_1798_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec(v_mvarId_1780_);
v_a_1816_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1795_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1795_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1780_ = stack[0].m_obj;
lean_object* v_localDecl_1781_ = stack[1].m_obj;
lean_object* v_a_1782_ = stack[2].m_obj;
lean_object* v_a_1783_ = stack[3].m_obj;
lean_object* v_a_1784_ = stack[4].m_obj;
lean_object* v_a_1785_ = stack[5].m_obj;
lean_object* v_res_1824_;
v_res_1824_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1780_, v_localDecl_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
stack->m_obj
 = v_res_1824_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1825_, lean_object* v_localDecl_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1825_, v_localDecl_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
return v_res_1832_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_box(0);
v___x_1845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1846_ = l_Lean_mkConst(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1847_; lean_object* v_dummy_1848_; 
v___x_1847_ = lean_box(0);
v_dummy_1848_ = l_Lean_Expr_sort___override(v___x_1847_);
return v_dummy_1848_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1849_, lean_object* v_mvarId_1850_, lean_object* v_as_1851_, size_t v_sz_1852_, size_t v_i_1853_, lean_object* v_b_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_usize_dec_lt(v_i_1853_, v_sz_1852_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_b_1854_);
return v___x_1861_;
}
else
{
lean_object* v_snd_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_2512_; 
v_snd_1862_ = lean_ctor_get(v_b_1854_, 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_b_1854_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v_b_1854_, 0);
lean_dec(v_unused_2513_);
v___x_1864_ = v_b_1854_;
v_isShared_1865_ = v_isSharedCheck_2512_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_snd_1862_);
lean_dec(v_b_1854_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_2512_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_a_1867_; lean_object* v___x_1873_; lean_object* v_a_1875_; lean_object* v_a_1880_; 
v___x_1873_ = lean_box(0);
v_a_1880_ = lean_array_uget(v_as_1851_, v_i_1853_);
if (lean_obj_tag(v_a_1880_) == 0)
{
lean_del_object(v___x_1864_);
v_a_1875_ = v_snd_1862_;
goto v___jp_1874_;
}
else
{
lean_object* v_val_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_2511_; 
v_val_1881_ = lean_ctor_get(v_a_1880_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_a_1880_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_1883_ = v_a_1880_;
v_isShared_1884_ = v_isSharedCheck_2511_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_val_1881_);
lean_dec(v_a_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_2511_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___x_1926_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; uint8_t v___y_1953_; uint8_t v___x_1954_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; uint8_t v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1962_; lean_object* v___y_1963_; uint8_t v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; uint8_t v___y_1967_; uint8_t v___y_1969_; uint8_t v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1977_; uint8_t v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1981_; lean_object* v___y_1982_; uint8_t v___y_1983_; 
v___x_1885_ = lean_box(0);
v___x_1926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1954_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1881_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1998_; uint8_t v___y_2000_; uint8_t v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2015_; uint8_t v___y_2016_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v___y_2023_; uint8_t v___y_2024_; lean_object* v_a_2025_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; uint8_t v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; uint8_t v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; uint8_t v___y_2076_; lean_object* v___y_2077_; uint8_t v___y_2078_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; uint8_t v___y_2108_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; uint8_t v___y_2113_; lean_object* v___y_2114_; uint8_t v___y_2115_; lean_object* v___y_2116_; uint8_t v___y_2117_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; uint8_t v___y_2123_; lean_object* v___y_2124_; uint8_t v___y_2125_; uint8_t v___y_2126_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; uint8_t v___y_2142_; lean_object* v___y_2143_; uint8_t v___y_2144_; uint8_t v___y_2145_; uint8_t v___y_2147_; uint8_t v_isHEq_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; uint8_t v___y_2162_; uint8_t v_isEq_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___x_2448_; 
v___x_1998_ = l_Lean_LocalDecl_type(v_val_1881_);
lean_inc_ref(v___x_1998_);
v___x_2448_ = l_Lean_Meta_matchNot_x3f(v___x_1998_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
if (lean_obj_tag(v_a_2449_) == 1)
{
lean_object* v_val_2450_; lean_object* v___x_2451_; 
v_val_2450_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_val_2450_);
lean_dec_ref_known(v_a_2449_, 1);
v___x_2451_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2450_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
if (lean_obj_tag(v_a_2452_) == 1)
{
lean_object* v_val_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2494_; 
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec_ref(v_config_1849_);
v_val_2453_ = lean_ctor_get(v_a_2452_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_a_2452_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2455_ = v_a_2452_;
v_isShared_2456_ = v_isSharedCheck_2494_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_val_2453_);
lean_dec(v_a_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2494_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; 
lean_inc(v_mvarId_1850_);
v___x_2457_ = l_Lean_MVarId_getType(v_mvarId_1850_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = l_Lean_LocalDecl_toExpr(v_val_1881_);
v___x_2460_ = l_Lean_mkFVar(v_val_2453_);
v___x_2461_ = l_Lean_Expr_app___override(v___x_2459_, v___x_2460_);
v___x_2462_ = l_Lean_Meta_mkFalseElim(v_a_2458_, v___x_2461_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1850_, v_a_2463_, v___y_1856_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_dec_ref_known(v___x_2464_, 1);
v___x_2465_ = lean_box(v___x_1860_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2465_);
v___x_2467_ = v___x_2455_;
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
lean_ctor_set(v___x_2468_, 1, v___x_1885_);
v_a_1867_ = v___x_2468_;
goto v___jp_1866_;
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_del_object(v___x_2455_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
v_a_2470_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2464_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2464_);
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
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_del_object(v___x_2455_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2478_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2462_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2462_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_del_object(v___x_2455_);
lean_dec(v_val_2453_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2486_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2457_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2457_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
else
{
lean_dec(v_a_2452_);
v___y_2314_ = v___y_1855_;
v___y_2315_ = v___y_1856_;
v___y_2316_ = v___y_1857_;
v___y_2317_ = v___y_1858_;
goto v___jp_2313_;
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2495_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2451_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2451_);
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
else
{
lean_dec(v_a_2449_);
v___y_2314_ = v___y_1855_;
v___y_2315_ = v___y_1856_;
v___y_2316_ = v___y_1857_;
v___y_2317_ = v___y_1858_;
goto v___jp_2313_;
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2503_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2448_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2448_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
v___jp_1999_:
{
uint8_t v_genDiseq_2006_; 
v_genDiseq_2006_ = lean_ctor_get_uint8(v_config_1849_, sizeof(void*)*1 + 2);
if (v_genDiseq_2006_ == 0)
{
lean_dec_ref(v___x_1998_);
v___y_1977_ = v___y_2003_;
v___y_1978_ = v___y_2000_;
v___y_1979_ = v___y_2004_;
v___y_1980_ = v___y_2005_;
v___y_1981_ = v___y_2001_;
v___y_1982_ = v___y_2002_;
v___y_1983_ = v___x_1954_;
goto v___jp_1976_;
}
else
{
uint8_t v___x_2007_; 
v___x_2007_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1998_);
v___y_1977_ = v___y_2003_;
v___y_1978_ = v___y_2000_;
v___y_1979_ = v___y_2004_;
v___y_1980_ = v___y_2005_;
v___y_1981_ = v___y_2001_;
v___y_1982_ = v___y_2002_;
v___y_1983_ = v___x_2007_;
goto v___jp_1976_;
}
}
v___jp_2008_:
{
if (v___y_2016_ == 0)
{
lean_dec_ref(v___y_2014_);
v___y_2000_ = v___y_2012_;
v___y_2001_ = v___y_2015_;
v___y_2002_ = v___y_2010_;
v___y_2003_ = v___y_2009_;
v___y_2004_ = v___y_2011_;
v___y_2005_ = v___y_2013_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2017_; 
lean_dec_ref(v___x_1998_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___y_2014_);
return v___x_2017_;
}
}
v___jp_2018_:
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lean_Exception_isInterrupt(v_a_2025_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2027_; 
lean_inc_ref(v_a_2025_);
v___x_2027_ = l_Lean_Exception_isRuntime(v_a_2025_);
v___y_2009_ = v___y_2019_;
v___y_2010_ = v___y_2020_;
v___y_2011_ = v___y_2021_;
v___y_2012_ = v___y_2022_;
v___y_2013_ = v___y_2023_;
v___y_2014_ = v_a_2025_;
v___y_2015_ = v___y_2024_;
v___y_2016_ = v___x_2027_;
goto v___jp_2008_;
}
else
{
v___y_2009_ = v___y_2019_;
v___y_2010_ = v___y_2020_;
v___y_2011_ = v___y_2021_;
v___y_2012_ = v___y_2022_;
v___y_2013_ = v___y_2023_;
v___y_2014_ = v_a_2025_;
v___y_2015_ = v___y_2024_;
v___y_2016_ = v___x_2026_;
goto v___jp_2008_;
}
}
v___jp_2028_:
{
if (lean_obj_tag(v___y_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v_a_2037_ = lean_ctor_get(v___y_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___y_2036_, 1);
v___x_2038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2039_ = l_Lean_Expr_isConstOf(v_a_2037_, v___x_2038_);
lean_dec(v_a_2037_);
if (v___x_2039_ == 0)
{
lean_dec_ref(v___y_2034_);
v___y_2000_ = v___y_2032_;
v___y_2001_ = v___y_2035_;
v___y_2002_ = v___y_2030_;
v___y_2003_ = v___y_2029_;
v___y_2004_ = v___y_2031_;
v___y_2005_ = v___y_2033_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2040_; 
lean_inc_ref(v___y_2034_);
v___x_2040_ = l_Lean_Meta_mkEqRefl(v___y_2034_, v___y_2030_, v___y_2029_, v___y_2031_, v___y_2033_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; lean_object* v_dummy_2043_; lean_object* v_nargs_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2043_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2044_ = l_Lean_Expr_getAppNumArgs(v___y_2034_);
lean_inc(v_nargs_2044_);
v___x_2045_ = lean_mk_array(v_nargs_2044_, v_dummy_2043_);
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_sub(v_nargs_2044_, v___x_2046_);
lean_dec(v_nargs_2044_);
v___x_2048_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2034_, v___x_2045_, v___x_2047_);
v___x_2049_ = lean_array_push(v___x_2048_, v_a_2041_);
v___x_2050_ = l_Lean_mkAppN(v___x_2042_, v___x_2049_);
lean_dec_ref(v___x_2049_);
lean_inc(v_mvarId_1850_);
v___x_2051_ = l_Lean_MVarId_getType(v_mvarId_1850_, v___y_2030_, v___y_2029_, v___y_2031_, v___y_2033_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
lean_inc(v_val_1881_);
v___x_2053_ = l_Lean_LocalDecl_toExpr(v_val_1881_);
v___x_2054_ = l_Lean_Meta_mkAbsurd(v_a_2052_, v___x_2053_, v___x_2050_, v___y_2030_, v___y_2029_, v___y_2031_, v___y_2033_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
lean_inc(v_mvarId_1850_);
v___x_2056_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1850_, v_a_2055_, v___y_2029_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v___x_1998_);
lean_dec(v_val_1881_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v___x_2056_, 0);
lean_dec(v_unused_2066_);
v___x_2058_ = v___x_2056_;
v_isShared_2059_ = v_isSharedCheck_2065_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v___x_2056_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2065_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_box(v___x_1860_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set_tag(v___x_2058_, 1);
lean_ctor_set(v___x_2058_, 0, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v___x_1885_);
v_a_1867_ = v___x_2063_;
goto v___jp_1866_;
}
}
}
else
{
lean_object* v_a_2067_; 
v_a_2067_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2056_, 1);
v___y_2019_ = v___y_2029_;
v___y_2020_ = v___y_2030_;
v___y_2021_ = v___y_2031_;
v___y_2022_ = v___y_2032_;
v___y_2023_ = v___y_2033_;
v___y_2024_ = v___y_2035_;
v_a_2025_ = v_a_2067_;
goto v___jp_2018_;
}
}
else
{
lean_object* v_a_2068_; 
v_a_2068_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2054_, 1);
v___y_2019_ = v___y_2029_;
v___y_2020_ = v___y_2030_;
v___y_2021_ = v___y_2031_;
v___y_2022_ = v___y_2032_;
v___y_2023_ = v___y_2033_;
v___y_2024_ = v___y_2035_;
v_a_2025_ = v_a_2068_;
goto v___jp_2018_;
}
}
else
{
lean_object* v_a_2069_; 
lean_dec_ref(v___x_2050_);
v_a_2069_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2051_, 1);
v___y_2019_ = v___y_2029_;
v___y_2020_ = v___y_2030_;
v___y_2021_ = v___y_2031_;
v___y_2022_ = v___y_2032_;
v___y_2023_ = v___y_2033_;
v___y_2024_ = v___y_2035_;
v_a_2025_ = v_a_2069_;
goto v___jp_2018_;
}
}
else
{
lean_object* v_a_2070_; 
lean_dec_ref(v___y_2034_);
v_a_2070_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2040_, 1);
v___y_2019_ = v___y_2029_;
v___y_2020_ = v___y_2030_;
v___y_2021_ = v___y_2031_;
v___y_2022_ = v___y_2032_;
v___y_2023_ = v___y_2033_;
v___y_2024_ = v___y_2035_;
v_a_2025_ = v_a_2070_;
goto v___jp_2018_;
}
}
}
else
{
lean_object* v_a_2071_; 
lean_dec_ref(v___y_2034_);
v_a_2071_ = lean_ctor_get(v___y_2036_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___y_2036_, 1);
v___y_2019_ = v___y_2029_;
v___y_2020_ = v___y_2030_;
v___y_2021_ = v___y_2031_;
v___y_2022_ = v___y_2032_;
v___y_2023_ = v___y_2033_;
v___y_2024_ = v___y_2035_;
v_a_2025_ = v_a_2071_;
goto v___jp_2018_;
}
}
v___jp_2072_:
{
lean_object* v___x_2079_; 
lean_inc_ref(v___x_1998_);
v___x_2079_ = l_Lean_Meta_mkDecide(v___x_1998_, v___y_2074_, v___y_2073_, v___y_2075_, v___y_2077_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; uint8_t v_transparency_2082_; uint8_t v___x_2083_; uint8_t v___x_2084_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2079_, 1);
v___x_2081_ = l_Lean_Meta_Context_config(v___y_2074_);
v_transparency_2082_ = lean_ctor_get_uint8(v___x_2081_, 9);
lean_dec_ref(v___x_2081_);
v___x_2083_ = 1;
v___x_2084_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v_keyedConfig_2085_; uint8_t v_trackZetaDelta_2086_; lean_object* v_zetaDeltaSet_2087_; lean_object* v_lctx_2088_; lean_object* v_localInstances_2089_; lean_object* v_defEqCtx_x3f_2090_; lean_object* v_synthPendingDepth_2091_; lean_object* v_customCanUnfoldPredicate_x3f_2092_; uint8_t v_univApprox_2093_; uint8_t v_inTypeClassResolution_2094_; uint8_t v_cacheInferType_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_keyedConfig_2085_ = lean_ctor_get(v___y_2074_, 0);
v_trackZetaDelta_2086_ = lean_ctor_get_uint8(v___y_2074_, sizeof(void*)*7);
v_zetaDeltaSet_2087_ = lean_ctor_get(v___y_2074_, 1);
v_lctx_2088_ = lean_ctor_get(v___y_2074_, 2);
v_localInstances_2089_ = lean_ctor_get(v___y_2074_, 3);
v_defEqCtx_x3f_2090_ = lean_ctor_get(v___y_2074_, 4);
v_synthPendingDepth_2091_ = lean_ctor_get(v___y_2074_, 5);
v_customCanUnfoldPredicate_x3f_2092_ = lean_ctor_get(v___y_2074_, 6);
v_univApprox_2093_ = lean_ctor_get_uint8(v___y_2074_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2094_ = lean_ctor_get_uint8(v___y_2074_, sizeof(void*)*7 + 2);
v_cacheInferType_2095_ = lean_ctor_get_uint8(v___y_2074_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2085_);
v___x_2096_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2083_, v_keyedConfig_2085_);
lean_inc(v_customCanUnfoldPredicate_x3f_2092_);
lean_inc(v_synthPendingDepth_2091_);
lean_inc(v_defEqCtx_x3f_2090_);
lean_inc_ref(v_localInstances_2089_);
lean_inc_ref(v_lctx_2088_);
lean_inc(v_zetaDeltaSet_2087_);
v___x_2097_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v_zetaDeltaSet_2087_);
lean_ctor_set(v___x_2097_, 2, v_lctx_2088_);
lean_ctor_set(v___x_2097_, 3, v_localInstances_2089_);
lean_ctor_set(v___x_2097_, 4, v_defEqCtx_x3f_2090_);
lean_ctor_set(v___x_2097_, 5, v_synthPendingDepth_2091_);
lean_ctor_set(v___x_2097_, 6, v_customCanUnfoldPredicate_x3f_2092_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*7, v_trackZetaDelta_2086_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*7 + 1, v_univApprox_2093_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2094_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*7 + 3, v_cacheInferType_2095_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2075_);
lean_inc(v___y_2073_);
lean_inc(v_a_2080_);
v___x_2098_ = lean_whnf(v_a_2080_, v___x_2097_, v___y_2073_, v___y_2075_, v___y_2077_);
v___y_2029_ = v___y_2073_;
v___y_2030_ = v___y_2074_;
v___y_2031_ = v___y_2075_;
v___y_2032_ = v___y_2076_;
v___y_2033_ = v___y_2077_;
v___y_2034_ = v_a_2080_;
v___y_2035_ = v___y_2078_;
v___y_2036_ = v___x_2098_;
goto v___jp_2028_;
}
else
{
lean_object* v___x_2099_; 
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2075_);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2074_);
lean_inc(v_a_2080_);
v___x_2099_ = lean_whnf(v_a_2080_, v___y_2074_, v___y_2073_, v___y_2075_, v___y_2077_);
v___y_2029_ = v___y_2073_;
v___y_2030_ = v___y_2074_;
v___y_2031_ = v___y_2075_;
v___y_2032_ = v___y_2076_;
v___y_2033_ = v___y_2077_;
v___y_2034_ = v_a_2080_;
v___y_2035_ = v___y_2078_;
v___y_2036_ = v___x_2099_;
goto v___jp_2028_;
}
}
else
{
lean_object* v_a_2100_; 
v_a_2100_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2079_, 1);
v___y_2019_ = v___y_2073_;
v___y_2020_ = v___y_2074_;
v___y_2021_ = v___y_2075_;
v___y_2022_ = v___y_2076_;
v___y_2023_ = v___y_2077_;
v___y_2024_ = v___y_2078_;
v_a_2025_ = v_a_2100_;
goto v___jp_2018_;
}
}
v___jp_2101_:
{
if (v___y_2108_ == 0)
{
v___y_2000_ = v___y_2105_;
v___y_2001_ = v___y_2107_;
v___y_2002_ = v___y_2103_;
v___y_2003_ = v___y_2102_;
v___y_2004_ = v___y_2104_;
v___y_2005_ = v___y_2106_;
goto v___jp_1999_;
}
else
{
v___y_2073_ = v___y_2102_;
v___y_2074_ = v___y_2103_;
v___y_2075_ = v___y_2104_;
v___y_2076_ = v___y_2105_;
v___y_2077_ = v___y_2106_;
v___y_2078_ = v___y_2107_;
goto v___jp_2072_;
}
}
v___jp_2109_:
{
if (v___y_2117_ == 0)
{
lean_dec_ref(v___y_2116_);
v___y_2102_ = v___y_2110_;
v___y_2103_ = v___y_2111_;
v___y_2104_ = v___y_2112_;
v___y_2105_ = v___y_2113_;
v___y_2106_ = v___y_2114_;
v___y_2107_ = v___y_2115_;
v___y_2108_ = v___x_1954_;
goto v___jp_2101_;
}
else
{
uint8_t v___x_2118_; 
v___x_2118_ = l_Lean_Expr_hasFVar(v___y_2116_);
lean_dec_ref(v___y_2116_);
if (v___x_2118_ == 0)
{
v___y_2073_ = v___y_2110_;
v___y_2074_ = v___y_2111_;
v___y_2075_ = v___y_2112_;
v___y_2076_ = v___y_2113_;
v___y_2077_ = v___y_2114_;
v___y_2078_ = v___y_2115_;
goto v___jp_2072_;
}
else
{
v___y_2102_ = v___y_2110_;
v___y_2103_ = v___y_2111_;
v___y_2104_ = v___y_2112_;
v___y_2105_ = v___y_2113_;
v___y_2106_ = v___y_2114_;
v___y_2107_ = v___y_2115_;
v___y_2108_ = v___x_1954_;
goto v___jp_2101_;
}
}
}
v___jp_2119_:
{
lean_object* v___x_2127_; 
lean_inc_ref(v___x_1998_);
v___x_2127_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1998_, v___y_2120_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; uint8_t v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = l_Lean_Expr_hasMVar(v_a_2128_);
if (v___x_2129_ == 0)
{
v___y_2110_ = v___y_2120_;
v___y_2111_ = v___y_2121_;
v___y_2112_ = v___y_2122_;
v___y_2113_ = v___y_2123_;
v___y_2114_ = v___y_2124_;
v___y_2115_ = v___y_2125_;
v___y_2116_ = v_a_2128_;
v___y_2117_ = v___y_2126_;
goto v___jp_2109_;
}
else
{
v___y_2110_ = v___y_2120_;
v___y_2111_ = v___y_2121_;
v___y_2112_ = v___y_2122_;
v___y_2113_ = v___y_2123_;
v___y_2114_ = v___y_2124_;
v___y_2115_ = v___y_2125_;
v___y_2116_ = v_a_2128_;
v___y_2117_ = v___x_1954_;
goto v___jp_2109_;
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v___x_1998_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2130_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2127_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2127_);
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
v___jp_2138_:
{
if (v___y_2145_ == 0)
{
v___y_2000_ = v___y_2142_;
v___y_2001_ = v___y_2144_;
v___y_2002_ = v___y_2140_;
v___y_2003_ = v___y_2139_;
v___y_2004_ = v___y_2141_;
v___y_2005_ = v___y_2143_;
goto v___jp_1999_;
}
else
{
v___y_2120_ = v___y_2139_;
v___y_2121_ = v___y_2140_;
v___y_2122_ = v___y_2141_;
v___y_2123_ = v___y_2142_;
v___y_2124_ = v___y_2143_;
v___y_2125_ = v___y_2144_;
v___y_2126_ = v___y_2145_;
goto v___jp_2119_;
}
}
v___jp_2146_:
{
uint8_t v_useDecide_2153_; 
v_useDecide_2153_ = lean_ctor_get_uint8(v_config_1849_, sizeof(void*)*1);
if (v_useDecide_2153_ == 0)
{
v___y_2139_ = v___y_2150_;
v___y_2140_ = v___y_2149_;
v___y_2141_ = v___y_2151_;
v___y_2142_ = v_isHEq_2148_;
v___y_2143_ = v___y_2152_;
v___y_2144_ = v___y_2147_;
v___y_2145_ = v___x_1954_;
goto v___jp_2138_;
}
else
{
uint8_t v___x_2154_; 
v___x_2154_ = l_Lean_Expr_hasFVar(v___x_1998_);
if (v___x_2154_ == 0)
{
v___y_2120_ = v___y_2150_;
v___y_2121_ = v___y_2149_;
v___y_2122_ = v___y_2151_;
v___y_2123_ = v_isHEq_2148_;
v___y_2124_ = v___y_2152_;
v___y_2125_ = v___y_2147_;
v___y_2126_ = v_useDecide_2153_;
goto v___jp_2119_;
}
else
{
v___y_2139_ = v___y_2150_;
v___y_2140_ = v___y_2149_;
v___y_2141_ = v___y_2151_;
v___y_2142_ = v_isHEq_2148_;
v___y_2143_ = v___y_2152_;
v___y_2144_ = v___y_2147_;
v___y_2145_ = v___x_1954_;
goto v___jp_2138_;
}
}
}
v___jp_2155_:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Meta_isExprDefEq(v___y_2160_, v___y_2156_, v___y_2161_, v___y_2158_, v___y_2159_, v___y_2157_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; uint8_t v___x_2165_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v___x_2165_ = lean_unbox(v_a_2164_);
lean_dec(v_a_2164_);
if (v___x_2165_ == 0)
{
v___y_2147_ = v___y_2162_;
v_isHEq_2148_ = v___x_1860_;
v___y_2149_ = v___y_2161_;
v___y_2150_ = v___y_2158_;
v___y_2151_ = v___y_2159_;
v___y_2152_ = v___y_2157_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2166_; 
lean_dec_ref(v___x_1998_);
lean_dec_ref(v_config_1849_);
lean_inc(v_mvarId_1850_);
v___x_2166_ = l_Lean_MVarId_getType(v_mvarId_1850_, v___y_2161_, v___y_2158_, v___y_2159_, v___y_2157_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2168_ = l_Lean_LocalDecl_toExpr(v_val_1881_);
v___x_2169_ = l_Lean_Meta_mkEqOfHEq(v___x_2168_, v___x_1860_, v___y_2161_, v___y_2158_, v___y_2159_, v___y_2157_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = l_Lean_Meta_mkNoConfusion(v_a_2167_, v_a_2170_, v___y_2161_, v___y_2158_, v___y_2159_, v___y_2157_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1850_, v_a_2172_, v___y_2158_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref_known(v___x_2173_, 1);
v___x_2174_ = lean_box(v___x_1860_);
v___x_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
v___x_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_1885_);
v_a_1867_ = v___x_2176_;
goto v___jp_1866_;
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
v_a_2177_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2173_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2173_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2185_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2171_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2171_);
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
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_a_2167_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2193_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2169_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2169_);
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
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2201_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2166_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2166_);
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
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v___x_1998_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2209_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2163_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2163_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
v___jp_2217_:
{
lean_object* v___x_2223_; 
lean_inc_ref(v___x_1998_);
v___x_2223_ = l_Lean_Meta_matchHEq_x3f(v___x_1998_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
if (lean_obj_tag(v_a_2224_) == 1)
{
lean_object* v_val_2225_; lean_object* v_snd_2226_; lean_object* v_snd_2227_; lean_object* v_fst_2228_; lean_object* v_fst_2229_; lean_object* v_fst_2230_; lean_object* v_snd_2231_; lean_object* v___x_2232_; 
v_val_2225_ = lean_ctor_get(v_a_2224_, 0);
lean_inc(v_val_2225_);
lean_dec_ref_known(v_a_2224_, 1);
v_snd_2226_ = lean_ctor_get(v_val_2225_, 1);
lean_inc(v_snd_2226_);
v_snd_2227_ = lean_ctor_get(v_snd_2226_, 1);
lean_inc(v_snd_2227_);
v_fst_2228_ = lean_ctor_get(v_val_2225_, 0);
lean_inc(v_fst_2228_);
lean_dec(v_val_2225_);
v_fst_2229_ = lean_ctor_get(v_snd_2226_, 0);
lean_inc(v_fst_2229_);
lean_dec(v_snd_2226_);
v_fst_2230_ = lean_ctor_get(v_snd_2227_, 0);
lean_inc(v_fst_2230_);
v_snd_2231_ = lean_ctor_get(v_snd_2227_, 1);
lean_inc(v_snd_2231_);
lean_dec(v_snd_2227_);
v___x_2232_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2229_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
if (lean_obj_tag(v_a_2233_) == 1)
{
lean_object* v_val_2234_; lean_object* v___x_2235_; 
v_val_2234_ = lean_ctor_get(v_a_2233_, 0);
lean_inc(v_val_2234_);
lean_dec_ref_known(v_a_2233_, 1);
v___x_2235_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2231_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
if (lean_obj_tag(v_a_2236_) == 1)
{
lean_object* v_toConstantVal_2237_; lean_object* v_val_2238_; lean_object* v_toConstantVal_2239_; lean_object* v_name_2240_; lean_object* v_name_2241_; uint8_t v___x_2242_; 
v_toConstantVal_2237_ = lean_ctor_get(v_val_2234_, 0);
lean_inc_ref(v_toConstantVal_2237_);
lean_dec(v_val_2234_);
v_val_2238_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v_a_2236_, 1);
v_toConstantVal_2239_ = lean_ctor_get(v_val_2238_, 0);
lean_inc_ref(v_toConstantVal_2239_);
lean_dec(v_val_2238_);
v_name_2240_ = lean_ctor_get(v_toConstantVal_2237_, 0);
lean_inc(v_name_2240_);
lean_dec_ref(v_toConstantVal_2237_);
v_name_2241_ = lean_ctor_get(v_toConstantVal_2239_, 0);
lean_inc(v_name_2241_);
lean_dec_ref(v_toConstantVal_2239_);
v___x_2242_ = lean_name_eq(v_name_2240_, v_name_2241_);
lean_dec(v_name_2241_);
lean_dec(v_name_2240_);
if (v___x_2242_ == 0)
{
v___y_2156_ = v_fst_2230_;
v___y_2157_ = v___y_2222_;
v___y_2158_ = v___y_2220_;
v___y_2159_ = v___y_2221_;
v___y_2160_ = v_fst_2228_;
v___y_2161_ = v___y_2219_;
v___y_2162_ = v_isEq_2218_;
goto v___jp_2155_;
}
else
{
if (v___x_1954_ == 0)
{
lean_dec(v_fst_2230_);
lean_dec(v_fst_2228_);
v___y_2147_ = v_isEq_2218_;
v_isHEq_2148_ = v___x_1860_;
v___y_2149_ = v___y_2219_;
v___y_2150_ = v___y_2220_;
v___y_2151_ = v___y_2221_;
v___y_2152_ = v___y_2222_;
goto v___jp_2146_;
}
else
{
v___y_2156_ = v_fst_2230_;
v___y_2157_ = v___y_2222_;
v___y_2158_ = v___y_2220_;
v___y_2159_ = v___y_2221_;
v___y_2160_ = v_fst_2228_;
v___y_2161_ = v___y_2219_;
v___y_2162_ = v_isEq_2218_;
goto v___jp_2155_;
}
}
}
else
{
lean_dec(v_a_2236_);
lean_dec(v_val_2234_);
lean_dec(v_fst_2230_);
lean_dec(v_fst_2228_);
v___y_2147_ = v_isEq_2218_;
v_isHEq_2148_ = v___x_1860_;
v___y_2149_ = v___y_2219_;
v___y_2150_ = v___y_2220_;
v___y_2151_ = v___y_2221_;
v___y_2152_ = v___y_2222_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_val_2234_);
lean_dec(v_fst_2230_);
lean_dec(v_fst_2228_);
lean_dec_ref(v___x_1998_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2243_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2235_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2235_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_dec(v_a_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_fst_2230_);
lean_dec(v_fst_2228_);
v___y_2147_ = v_isEq_2218_;
v_isHEq_2148_ = v___x_1860_;
v___y_2149_ = v___y_2219_;
v___y_2150_ = v___y_2220_;
v___y_2151_ = v___y_2221_;
v___y_2152_ = v___y_2222_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_snd_2231_);
lean_dec(v_fst_2230_);
lean_dec(v_fst_2228_);
lean_dec_ref(v___x_1998_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2251_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2232_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2232_);
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
lean_dec(v_a_2224_);
v___y_2147_ = v_isEq_2218_;
v_isHEq_2148_ = v___x_1954_;
v___y_2149_ = v___y_2219_;
v___y_2150_ = v___y_2220_;
v___y_2151_ = v___y_2221_;
v___y_2152_ = v___y_2222_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec_ref(v___x_1998_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2259_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2223_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2223_);
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
v___jp_2267_:
{
lean_object* v___x_2272_; 
lean_inc_ref(v___x_1998_);
v___x_2272_ = l_Lean_Meta_matchEq_x3f(v___x_1998_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
if (lean_obj_tag(v_a_2273_) == 1)
{
lean_object* v_val_2274_; lean_object* v_snd_2275_; lean_object* v_fst_2276_; lean_object* v_snd_2277_; lean_object* v___x_2278_; 
v_val_2274_ = lean_ctor_get(v_a_2273_, 0);
lean_inc(v_val_2274_);
lean_dec_ref_known(v_a_2273_, 1);
v_snd_2275_ = lean_ctor_get(v_val_2274_, 1);
lean_inc(v_snd_2275_);
lean_dec(v_val_2274_);
v_fst_2276_ = lean_ctor_get(v_snd_2275_, 0);
lean_inc(v_fst_2276_);
v_snd_2277_ = lean_ctor_get(v_snd_2275_, 1);
lean_inc(v_snd_2277_);
lean_dec(v_snd_2275_);
v___x_2278_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2276_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
if (lean_obj_tag(v_a_2279_) == 1)
{
lean_object* v_val_2280_; lean_object* v___x_2281_; 
v_val_2280_ = lean_ctor_get(v_a_2279_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v_a_2279_, 1);
v___x_2281_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2277_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
if (lean_obj_tag(v_a_2282_) == 1)
{
lean_object* v_toConstantVal_2283_; lean_object* v_val_2284_; lean_object* v_toConstantVal_2285_; lean_object* v_name_2286_; lean_object* v_name_2287_; uint8_t v___x_2288_; 
v_toConstantVal_2283_ = lean_ctor_get(v_val_2280_, 0);
lean_inc_ref(v_toConstantVal_2283_);
lean_dec(v_val_2280_);
v_val_2284_ = lean_ctor_get(v_a_2282_, 0);
lean_inc(v_val_2284_);
lean_dec_ref_known(v_a_2282_, 1);
v_toConstantVal_2285_ = lean_ctor_get(v_val_2284_, 0);
lean_inc_ref(v_toConstantVal_2285_);
lean_dec(v_val_2284_);
v_name_2286_ = lean_ctor_get(v_toConstantVal_2283_, 0);
lean_inc(v_name_2286_);
lean_dec_ref(v_toConstantVal_2283_);
v_name_2287_ = lean_ctor_get(v_toConstantVal_2285_, 0);
lean_inc(v_name_2287_);
lean_dec_ref(v_toConstantVal_2285_);
v___x_2288_ = lean_name_eq(v_name_2286_, v_name_2287_);
lean_dec(v_name_2287_);
lean_dec(v_name_2286_);
if (v___x_2288_ == 0)
{
lean_dec_ref(v___x_1998_);
lean_dec_ref(v_config_1849_);
v___y_1887_ = v___y_2268_;
v___y_1888_ = v___y_2269_;
v___y_1889_ = v___y_2271_;
v___y_1890_ = v___y_2270_;
goto v___jp_1886_;
}
else
{
if (v___x_1954_ == 0)
{
lean_del_object(v___x_1883_);
v_isEq_2218_ = v___x_1860_;
v___y_2219_ = v___y_2268_;
v___y_2220_ = v___y_2269_;
v___y_2221_ = v___y_2270_;
v___y_2222_ = v___y_2271_;
goto v___jp_2217_;
}
else
{
lean_dec_ref(v___x_1998_);
lean_dec_ref(v_config_1849_);
v___y_1887_ = v___y_2268_;
v___y_1888_ = v___y_2269_;
v___y_1889_ = v___y_2271_;
v___y_1890_ = v___y_2270_;
goto v___jp_1886_;
}
}
}
else
{
lean_dec(v_a_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_1883_);
v_isEq_2218_ = v___x_1860_;
v___y_2219_ = v___y_2268_;
v___y_2220_ = v___y_2269_;
v___y_2221_ = v___y_2270_;
v___y_2222_ = v___y_2271_;
goto v___jp_2217_;
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_val_2280_);
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2289_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2281_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2281_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_dec(v_a_2279_);
lean_dec(v_snd_2277_);
lean_del_object(v___x_1883_);
v_isEq_2218_ = v___x_1860_;
v___y_2219_ = v___y_2268_;
v___y_2220_ = v___y_2269_;
v___y_2221_ = v___y_2270_;
v___y_2222_ = v___y_2271_;
goto v___jp_2217_;
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_snd_2277_);
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2297_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2278_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2278_);
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
lean_dec(v_a_2273_);
lean_del_object(v___x_1883_);
v_isEq_2218_ = v___x_1954_;
v___y_2219_ = v___y_2268_;
v___y_2220_ = v___y_2269_;
v___y_2221_ = v___y_2270_;
v___y_2222_ = v___y_2271_;
goto v___jp_2217_;
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2305_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2272_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2272_);
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
v___jp_2313_:
{
lean_object* v___x_2318_; 
lean_inc_ref(v___x_1998_);
v___x_2318_ = l_Lean_refutableHasNotBit_x3f(v___x_1998_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
if (lean_obj_tag(v_a_2319_) == 1)
{
lean_object* v_val_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec_ref(v_config_1849_);
v_val_2320_ = lean_ctor_get(v_a_2319_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_a_2319_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2322_ = v_a_2319_;
v_isShared_2323_ = v_isSharedCheck_2359_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_val_2320_);
lean_dec(v_a_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2359_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; 
lean_inc(v_mvarId_1850_);
v___x_2324_ = l_Lean_MVarId_getType(v_mvarId_1850_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = l_Lean_LocalDecl_toExpr(v_val_1881_);
v___x_2327_ = l_Lean_Meta_mkAbsurd(v_a_2325_, v_val_2320_, v___x_2326_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1850_, v_a_2328_, v___y_2315_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec_ref_known(v___x_2329_, 1);
v___x_2330_ = lean_box(v___x_1860_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2330_);
v___x_2332_ = v___x_2322_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v___x_1885_);
v_a_1867_ = v___x_2333_;
goto v___jp_1866_;
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_del_object(v___x_2322_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
v_a_2335_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2329_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2329_);
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
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_del_object(v___x_2322_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2343_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2327_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2327_);
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
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_del_object(v___x_2322_);
lean_dec(v_val_2320_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2351_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2324_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2324_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
else
{
lean_object* v___x_2360_; 
lean_dec(v_a_2319_);
lean_inc_ref(v___x_1998_);
v___x_2360_ = l_Lean_Meta_matchNe_x3f(v___x_1998_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
if (lean_obj_tag(v_a_2361_) == 1)
{
lean_object* v_val_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2431_; 
v_val_2362_ = lean_ctor_get(v_a_2361_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_a_2361_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2364_ = v_a_2361_;
v_isShared_2365_ = v_isSharedCheck_2431_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_val_2362_);
lean_dec(v_a_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2431_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_snd_2366_; lean_object* v_fst_2367_; lean_object* v_snd_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2430_; 
v_snd_2366_ = lean_ctor_get(v_val_2362_, 1);
lean_inc(v_snd_2366_);
lean_dec(v_val_2362_);
v_fst_2367_ = lean_ctor_get(v_snd_2366_, 0);
v_snd_2368_ = lean_ctor_get(v_snd_2366_, 1);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_snd_2366_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2370_ = v_snd_2366_;
v_isShared_2371_ = v_isSharedCheck_2430_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_snd_2368_);
lean_inc(v_fst_2367_);
lean_dec(v_snd_2366_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2430_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; 
lean_inc(v_fst_2367_);
v___x_2372_ = l_Lean_Meta_isExprDefEq(v_fst_2367_, v_snd_2368_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; uint8_t v___x_2374_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___x_2374_ = lean_unbox(v_a_2373_);
lean_dec(v_a_2373_);
if (v___x_2374_ == 0)
{
lean_del_object(v___x_2370_);
lean_dec(v_fst_2367_);
lean_del_object(v___x_2364_);
v___y_2268_ = v___y_2314_;
v___y_2269_ = v___y_2315_;
v___y_2270_ = v___y_2316_;
v___y_2271_ = v___y_2317_;
goto v___jp_2267_;
}
else
{
lean_object* v___x_2375_; 
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec_ref(v_config_1849_);
lean_inc(v_mvarId_1850_);
v___x_2375_ = l_Lean_MVarId_getType(v_mvarId_1850_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = l_Lean_Meta_mkEqRefl(v_fst_2367_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
v___x_2379_ = l_Lean_LocalDecl_toExpr(v_val_1881_);
v___x_2380_ = l_Lean_Meta_mkAbsurd(v_a_2376_, v_a_2378_, v___x_2379_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1850_, v_a_2381_, v___y_2315_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
lean_dec_ref_known(v___x_2382_, 1);
v___x_2383_ = lean_box(v___x_1860_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2383_);
v___x_2385_ = v___x_2364_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2387_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v___x_1885_);
lean_ctor_set(v___x_2370_, 0, v___x_2385_);
v___x_2387_ = v___x_2370_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___x_1885_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
v_a_1867_ = v___x_2387_;
goto v___jp_1866_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_del_object(v___x_2370_);
lean_del_object(v___x_2364_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
v_a_2390_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2382_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2382_);
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
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_del_object(v___x_2370_);
lean_del_object(v___x_2364_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2398_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2380_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2380_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_a_2376_);
lean_del_object(v___x_2370_);
lean_del_object(v___x_2364_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2406_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2377_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2377_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_del_object(v___x_2370_);
lean_dec(v_fst_2367_);
lean_del_object(v___x_2364_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_2414_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2375_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2375_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_del_object(v___x_2370_);
lean_dec(v_fst_2367_);
lean_del_object(v___x_2364_);
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2422_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2372_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2372_);
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
}
}
else
{
lean_dec(v_a_2361_);
v___y_2268_ = v___y_2314_;
v___y_2269_ = v___y_2315_;
v___y_2270_ = v___y_2316_;
v___y_2271_ = v___y_2317_;
goto v___jp_2267_;
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2432_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2360_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2360_);
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
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec_ref(v___x_1998_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_2440_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2318_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2318_);
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
}
else
{
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
v_a_1875_ = v___x_1926_;
goto v___jp_1874_;
}
v___jp_1886_:
{
lean_object* v___x_1891_; 
lean_inc(v_mvarId_1850_);
v___x_1891_ = l_Lean_MVarId_getType(v_mvarId_1850_, v___y_1887_, v___y_1888_, v___y_1890_, v___y_1889_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v___x_1893_ = l_Lean_LocalDecl_toExpr(v_val_1881_);
v___x_1894_ = l_Lean_Meta_mkNoConfusion(v_a_1892_, v___x_1893_, v___y_1887_, v___y_1888_, v___y_1890_, v___y_1889_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1850_, v_a_1895_, v___y_1888_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_dec_ref_known(v___x_1896_, 1);
v___x_1897_ = lean_box(v___x_1860_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1897_);
v___x_1899_ = v___x_1883_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1885_);
v_a_1867_ = v___x_1900_;
goto v___jp_1866_;
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_del_object(v___x_1883_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
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
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_del_object(v___x_1883_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_1910_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1894_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1894_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
v_a_1918_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1891_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1891_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
v___jp_1927_:
{
lean_object* v_searchFuel_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_searchFuel_1932_ = lean_ctor_get(v_config_1849_, 0);
v___x_1933_ = l_Lean_LocalDecl_fvarId(v_val_1881_);
lean_dec(v_val_1881_);
lean_inc(v_searchFuel_1932_);
lean_inc(v_mvarId_1850_);
v___x_1934_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1850_, v___x_1933_, v_searchFuel_1932_, v___y_1929_, v___y_1931_, v___y_1928_, v___y_1930_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; uint8_t v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = lean_unbox(v_a_1935_);
lean_dec(v_a_1935_);
if (v___x_1936_ == 0)
{
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
v_a_1875_ = v___x_1926_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v___x_1937_ = lean_box(v___x_1860_);
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___x_1885_);
v_a_1867_ = v___x_1939_;
goto v___jp_1866_;
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_1940_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1934_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1934_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
v___jp_1948_:
{
if (v___y_1953_ == 0)
{
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
v_a_1875_ = v___x_1926_;
goto v___jp_1874_;
}
else
{
v___y_1928_ = v___y_1949_;
v___y_1929_ = v___y_1950_;
v___y_1930_ = v___y_1951_;
v___y_1931_ = v___y_1952_;
goto v___jp_1927_;
}
}
v___jp_1955_:
{
if (v___y_1959_ == 0)
{
v___y_1928_ = v___y_1956_;
v___y_1929_ = v___y_1957_;
v___y_1930_ = v___y_1958_;
v___y_1931_ = v___y_1960_;
goto v___jp_1927_;
}
else
{
v___y_1949_ = v___y_1956_;
v___y_1950_ = v___y_1957_;
v___y_1951_ = v___y_1958_;
v___y_1952_ = v___y_1960_;
v___y_1953_ = v___x_1954_;
goto v___jp_1948_;
}
}
v___jp_1961_:
{
if (v___y_1967_ == 0)
{
v___y_1949_ = v___y_1962_;
v___y_1950_ = v___y_1963_;
v___y_1951_ = v___y_1965_;
v___y_1952_ = v___y_1966_;
v___y_1953_ = v___x_1954_;
goto v___jp_1948_;
}
else
{
v___y_1956_ = v___y_1962_;
v___y_1957_ = v___y_1963_;
v___y_1958_ = v___y_1965_;
v___y_1959_ = v___y_1964_;
v___y_1960_ = v___y_1966_;
goto v___jp_1955_;
}
}
v___jp_1968_:
{
uint8_t v_emptyType_1975_; 
v_emptyType_1975_ = lean_ctor_get_uint8(v_config_1849_, sizeof(void*)*1 + 1);
if (v_emptyType_1975_ == 0)
{
v___y_1962_ = v___y_1973_;
v___y_1963_ = v___y_1971_;
v___y_1964_ = v___y_1969_;
v___y_1965_ = v___y_1974_;
v___y_1966_ = v___y_1972_;
v___y_1967_ = v___x_1954_;
goto v___jp_1961_;
}
else
{
if (v___y_1970_ == 0)
{
v___y_1956_ = v___y_1973_;
v___y_1957_ = v___y_1971_;
v___y_1958_ = v___y_1974_;
v___y_1959_ = v___y_1969_;
v___y_1960_ = v___y_1972_;
goto v___jp_1955_;
}
else
{
v___y_1962_ = v___y_1973_;
v___y_1963_ = v___y_1971_;
v___y_1964_ = v___y_1969_;
v___y_1965_ = v___y_1974_;
v___y_1966_ = v___y_1972_;
v___y_1967_ = v___x_1954_;
goto v___jp_1961_;
}
}
}
v___jp_1976_:
{
if (v___y_1983_ == 0)
{
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1981_;
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1977_;
v___y_1973_ = v___y_1979_;
v___y_1974_ = v___y_1980_;
goto v___jp_1968_;
}
else
{
lean_object* v___x_1984_; 
lean_inc(v_val_1881_);
lean_inc(v_mvarId_1850_);
v___x_1984_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1850_, v_val_1881_, v___y_1982_, v___y_1977_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; uint8_t v___x_1986_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = lean_unbox(v_a_1985_);
lean_dec(v_a_1985_);
if (v___x_1986_ == 0)
{
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1981_;
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1977_;
v___y_1973_ = v___y_1979_;
v___y_1974_ = v___y_1980_;
goto v___jp_1968_;
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_dec(v_val_1881_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v___x_1987_ = lean_box(v___x_1860_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v___x_1885_);
v_a_1867_ = v___x_1989_;
goto v___jp_1866_;
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_val_1881_);
lean_del_object(v___x_1864_);
lean_dec(v_snd_1862_);
lean_dec(v_mvarId_1850_);
lean_dec_ref(v_config_1849_);
v_a_1990_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1984_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1984_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
}
}
v___jp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_a_1867_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1868_);
v___x_1870_ = v___x_1864_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_snd_1862_);
v___x_1870_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
}
v___jp_1874_:
{
lean_object* v___x_1876_; size_t v___x_1877_; size_t v___x_1878_; 
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1873_);
lean_ctor_set(v___x_1876_, 1, v_a_1875_);
v___x_1877_ = ((size_t)1ULL);
v___x_1878_ = lean_usize_add(v_i_1853_, v___x_1877_);
v_i_1853_ = v___x_1878_;
v_b_1854_ = v___x_1876_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1849_ = stack[0].m_obj;
lean_object* v_mvarId_1850_ = stack[1].m_obj;
lean_object* v_as_1851_ = stack[2].m_obj;
size_t v_sz_1852_ = stack[3].m_num;
size_t v_i_1853_ = stack[4].m_num;
lean_object* v_b_1854_ = stack[5].m_obj;
lean_object* v___y_1855_ = stack[6].m_obj;
lean_object* v___y_1856_ = stack[7].m_obj;
lean_object* v___y_1857_ = stack[8].m_obj;
lean_object* v___y_1858_ = stack[9].m_obj;
lean_object* v_res_2514_;
v_res_2514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_1849_, v_mvarId_1850_, v_as_1851_, v_sz_1852_, v_i_1853_, v_b_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
stack->m_obj
 = v_res_2514_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2515_, lean_object* v_mvarId_2516_, lean_object* v_as_2517_, lean_object* v_sz_2518_, lean_object* v_i_2519_, lean_object* v_b_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
size_t v_sz_boxed_2526_; size_t v_i_boxed_2527_; lean_object* v_res_2528_; 
v_sz_boxed_2526_ = lean_unbox_usize(v_sz_2518_);
lean_dec(v_sz_2518_);
v_i_boxed_2527_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_res_2528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2515_, v_mvarId_2516_, v_as_2517_, v_sz_boxed_2526_, v_i_boxed_2527_, v_b_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec_ref(v_as_2517_);
return v_res_2528_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2529_, lean_object* v_mvarId_2530_, lean_object* v_as_2531_, size_t v_sz_2532_, size_t v_i_2533_, lean_object* v_b_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_usize_dec_lt(v_i_2533_, v_sz_2532_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; 
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_b_2534_);
return v___x_2541_;
}
else
{
lean_object* v_snd_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_3192_; 
v_snd_2542_ = lean_ctor_get(v_b_2534_, 1);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_b_2534_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v_b_2534_, 0);
lean_dec(v_unused_3193_);
v___x_2544_ = v_b_2534_;
v_isShared_2545_ = v_isSharedCheck_3192_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_snd_2542_);
lean_dec(v_b_2534_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_3192_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v_a_2547_; lean_object* v___x_2553_; lean_object* v_a_2555_; lean_object* v_a_2560_; 
v___x_2553_ = lean_box(0);
v_a_2560_ = lean_array_uget(v_as_2531_, v_i_2533_);
if (lean_obj_tag(v_a_2560_) == 0)
{
lean_del_object(v___x_2544_);
v_a_2555_ = v_snd_2542_;
goto v___jp_2554_;
}
else
{
lean_object* v_val_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_3191_; 
v_val_2561_ = lean_ctor_get(v_a_2560_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_a_2560_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_2563_ = v_a_2560_;
v_isShared_2564_ = v_isSharedCheck_3191_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_val_2561_);
lean_dec(v_a_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_3191_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___x_2606_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; uint8_t v___y_2633_; uint8_t v___x_2634_; lean_object* v___y_2636_; uint8_t v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; uint8_t v___y_2647_; uint8_t v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2657_; uint8_t v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; uint8_t v___y_2661_; lean_object* v___y_2662_; uint8_t v___y_2663_; 
v___x_2565_ = lean_box(0);
v___x_2606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2634_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2561_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2678_; uint8_t v___y_2680_; uint8_t v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2689_; uint8_t v___y_2690_; lean_object* v___y_2691_; uint8_t v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; uint8_t v___y_2696_; lean_object* v___y_2699_; uint8_t v___y_2700_; uint8_t v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v_a_2705_; lean_object* v___y_2709_; uint8_t v___y_2710_; uint8_t v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2753_; uint8_t v___y_2754_; uint8_t v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2782_; uint8_t v___y_2783_; uint8_t v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; uint8_t v___y_2788_; lean_object* v___y_2790_; uint8_t v___y_2791_; lean_object* v___y_2792_; uint8_t v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; uint8_t v___y_2797_; lean_object* v___y_2800_; uint8_t v___y_2801_; uint8_t v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; uint8_t v___y_2806_; lean_object* v___y_2819_; uint8_t v___y_2820_; uint8_t v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; uint8_t v___y_2825_; uint8_t v___y_2827_; uint8_t v_isHEq_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; uint8_t v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; uint8_t v_isEq_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___x_3128_; 
v___x_2678_ = l_Lean_LocalDecl_type(v_val_2561_);
lean_inc_ref(v___x_2678_);
v___x_3128_ = l_Lean_Meta_matchNot_x3f(v___x_2678_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3128_, 1);
if (lean_obj_tag(v_a_3129_) == 1)
{
lean_object* v_val_3130_; lean_object* v___x_3131_; 
v_val_3130_ = lean_ctor_get(v_a_3129_, 0);
lean_inc(v_val_3130_);
lean_dec_ref_known(v_a_3129_, 1);
v___x_3131_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3130_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
if (lean_obj_tag(v_a_3132_) == 1)
{
lean_object* v_val_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3174_; 
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec_ref(v_config_2529_);
v_val_3133_ = lean_ctor_get(v_a_3132_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_a_3132_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3135_ = v_a_3132_;
v_isShared_3136_ = v_isSharedCheck_3174_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_val_3133_);
lean_dec(v_a_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3174_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; 
lean_inc(v_mvarId_2530_);
v___x_3137_ = l_Lean_MVarId_getType(v_mvarId_2530_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3139_ = l_Lean_LocalDecl_toExpr(v_val_2561_);
v___x_3140_ = l_Lean_mkFVar(v_val_3133_);
v___x_3141_ = l_Lean_Expr_app___override(v___x_3139_, v___x_3140_);
v___x_3142_ = l_Lean_Meta_mkFalseElim(v_a_3138_, v___x_3141_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3144_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v___x_3144_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2530_, v_a_3143_, v___y_2536_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
lean_dec_ref_known(v___x_3144_, 1);
v___x_3145_ = lean_box(v___x_2540_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3145_);
v___x_3147_ = v___x_3135_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___x_2565_);
v_a_2547_ = v___x_3148_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_del_object(v___x_3135_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
v_a_3150_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3144_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3144_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_del_object(v___x_3135_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_3158_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3142_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3142_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_del_object(v___x_3135_);
lean_dec(v_val_3133_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_3166_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3137_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3137_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
else
{
lean_dec(v_a_3132_);
v___y_2994_ = v___y_2535_;
v___y_2995_ = v___y_2536_;
v___y_2996_ = v___y_2537_;
v___y_2997_ = v___y_2538_;
goto v___jp_2993_;
}
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_3175_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3131_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3131_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
else
{
lean_dec(v_a_3129_);
v___y_2994_ = v___y_2535_;
v___y_2995_ = v___y_2536_;
v___y_2996_ = v___y_2537_;
v___y_2997_ = v___y_2538_;
goto v___jp_2993_;
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_3183_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3128_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3128_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
v___jp_2679_:
{
uint8_t v_genDiseq_2686_; 
v_genDiseq_2686_ = lean_ctor_get_uint8(v_config_2529_, sizeof(void*)*1 + 2);
if (v_genDiseq_2686_ == 0)
{
lean_dec_ref(v___x_2678_);
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2680_;
v___y_2659_ = v___y_2685_;
v___y_2660_ = v___y_2684_;
v___y_2661_ = v___y_2681_;
v___y_2662_ = v___y_2682_;
v___y_2663_ = v___x_2634_;
goto v___jp_2656_;
}
else
{
uint8_t v___x_2687_; 
v___x_2687_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2678_);
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2680_;
v___y_2659_ = v___y_2685_;
v___y_2660_ = v___y_2684_;
v___y_2661_ = v___y_2681_;
v___y_2662_ = v___y_2682_;
v___y_2663_ = v___x_2687_;
goto v___jp_2656_;
}
}
v___jp_2688_:
{
if (v___y_2696_ == 0)
{
lean_dec_ref(v___y_2691_);
v___y_2680_ = v___y_2690_;
v___y_2681_ = v___y_2692_;
v___y_2682_ = v___y_2694_;
v___y_2683_ = v___y_2689_;
v___y_2684_ = v___y_2693_;
v___y_2685_ = v___y_2695_;
goto v___jp_2679_;
}
else
{
lean_object* v___x_2697_; 
lean_dec_ref(v___x_2678_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v___x_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___y_2691_);
return v___x_2697_;
}
}
v___jp_2698_:
{
uint8_t v___x_2706_; 
v___x_2706_ = l_Lean_Exception_isInterrupt(v_a_2705_);
if (v___x_2706_ == 0)
{
uint8_t v___x_2707_; 
lean_inc_ref(v_a_2705_);
v___x_2707_ = l_Lean_Exception_isRuntime(v_a_2705_);
v___y_2689_ = v___y_2699_;
v___y_2690_ = v___y_2700_;
v___y_2691_ = v_a_2705_;
v___y_2692_ = v___y_2701_;
v___y_2693_ = v___y_2702_;
v___y_2694_ = v___y_2703_;
v___y_2695_ = v___y_2704_;
v___y_2696_ = v___x_2707_;
goto v___jp_2688_;
}
else
{
v___y_2689_ = v___y_2699_;
v___y_2690_ = v___y_2700_;
v___y_2691_ = v_a_2705_;
v___y_2692_ = v___y_2701_;
v___y_2693_ = v___y_2702_;
v___y_2694_ = v___y_2703_;
v___y_2695_ = v___y_2704_;
v___y_2696_ = v___x_2706_;
goto v___jp_2688_;
}
}
v___jp_2708_:
{
if (lean_obj_tag(v___y_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v_a_2717_ = lean_ctor_get(v___y_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___y_2716_, 1);
v___x_2718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2719_ = l_Lean_Expr_isConstOf(v_a_2717_, v___x_2718_);
lean_dec(v_a_2717_);
if (v___x_2719_ == 0)
{
lean_dec_ref(v___y_2713_);
v___y_2680_ = v___y_2710_;
v___y_2681_ = v___y_2711_;
v___y_2682_ = v___y_2714_;
v___y_2683_ = v___y_2709_;
v___y_2684_ = v___y_2712_;
v___y_2685_ = v___y_2715_;
goto v___jp_2679_;
}
else
{
lean_object* v___x_2720_; 
lean_inc_ref(v___y_2713_);
v___x_2720_ = l_Lean_Meta_mkEqRefl(v___y_2713_, v___y_2714_, v___y_2709_, v___y_2712_, v___y_2715_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; lean_object* v_dummy_2723_; lean_object* v_nargs_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2722_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2723_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2724_ = l_Lean_Expr_getAppNumArgs(v___y_2713_);
lean_inc(v_nargs_2724_);
v___x_2725_ = lean_mk_array(v_nargs_2724_, v_dummy_2723_);
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_sub(v_nargs_2724_, v___x_2726_);
lean_dec(v_nargs_2724_);
v___x_2728_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2713_, v___x_2725_, v___x_2727_);
v___x_2729_ = lean_array_push(v___x_2728_, v_a_2721_);
v___x_2730_ = l_Lean_mkAppN(v___x_2722_, v___x_2729_);
lean_dec_ref(v___x_2729_);
lean_inc(v_mvarId_2530_);
v___x_2731_ = l_Lean_MVarId_getType(v_mvarId_2530_, v___y_2714_, v___y_2709_, v___y_2712_, v___y_2715_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
lean_inc(v_val_2561_);
v___x_2733_ = l_Lean_LocalDecl_toExpr(v_val_2561_);
v___x_2734_ = l_Lean_Meta_mkAbsurd(v_a_2732_, v___x_2733_, v___x_2730_, v___y_2714_, v___y_2709_, v___y_2712_, v___y_2715_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
lean_inc(v_mvarId_2530_);
v___x_2736_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2530_, v_a_2735_, v___y_2709_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v___x_2678_);
lean_dec(v_val_2561_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; 
v_unused_2746_ = lean_ctor_get(v___x_2736_, 0);
lean_dec(v_unused_2746_);
v___x_2738_ = v___x_2736_;
v_isShared_2739_ = v_isSharedCheck_2745_;
goto v_resetjp_2737_;
}
else
{
lean_dec(v___x_2736_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2745_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = lean_box(v___x_2540_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set_tag(v___x_2738_, 1);
lean_ctor_set(v___x_2738_, 0, v___x_2740_);
v___x_2742_ = v___x_2738_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; 
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
lean_ctor_set(v___x_2743_, 1, v___x_2565_);
v_a_2547_ = v___x_2743_;
goto v___jp_2546_;
}
}
}
else
{
lean_object* v_a_2747_; 
v_a_2747_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2736_, 1);
v___y_2699_ = v___y_2709_;
v___y_2700_ = v___y_2710_;
v___y_2701_ = v___y_2711_;
v___y_2702_ = v___y_2712_;
v___y_2703_ = v___y_2714_;
v___y_2704_ = v___y_2715_;
v_a_2705_ = v_a_2747_;
goto v___jp_2698_;
}
}
else
{
lean_object* v_a_2748_; 
v_a_2748_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2734_, 1);
v___y_2699_ = v___y_2709_;
v___y_2700_ = v___y_2710_;
v___y_2701_ = v___y_2711_;
v___y_2702_ = v___y_2712_;
v___y_2703_ = v___y_2714_;
v___y_2704_ = v___y_2715_;
v_a_2705_ = v_a_2748_;
goto v___jp_2698_;
}
}
else
{
lean_object* v_a_2749_; 
lean_dec_ref(v___x_2730_);
v_a_2749_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2731_, 1);
v___y_2699_ = v___y_2709_;
v___y_2700_ = v___y_2710_;
v___y_2701_ = v___y_2711_;
v___y_2702_ = v___y_2712_;
v___y_2703_ = v___y_2714_;
v___y_2704_ = v___y_2715_;
v_a_2705_ = v_a_2749_;
goto v___jp_2698_;
}
}
else
{
lean_object* v_a_2750_; 
lean_dec_ref(v___y_2713_);
v_a_2750_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2720_, 1);
v___y_2699_ = v___y_2709_;
v___y_2700_ = v___y_2710_;
v___y_2701_ = v___y_2711_;
v___y_2702_ = v___y_2712_;
v___y_2703_ = v___y_2714_;
v___y_2704_ = v___y_2715_;
v_a_2705_ = v_a_2750_;
goto v___jp_2698_;
}
}
}
else
{
lean_object* v_a_2751_; 
lean_dec_ref(v___y_2713_);
v_a_2751_ = lean_ctor_get(v___y_2716_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___y_2716_, 1);
v___y_2699_ = v___y_2709_;
v___y_2700_ = v___y_2710_;
v___y_2701_ = v___y_2711_;
v___y_2702_ = v___y_2712_;
v___y_2703_ = v___y_2714_;
v___y_2704_ = v___y_2715_;
v_a_2705_ = v_a_2751_;
goto v___jp_2698_;
}
}
v___jp_2752_:
{
lean_object* v___x_2759_; 
lean_inc_ref(v___x_2678_);
v___x_2759_ = l_Lean_Meta_mkDecide(v___x_2678_, v___y_2757_, v___y_2753_, v___y_2756_, v___y_2758_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; uint8_t v_transparency_2762_; uint8_t v___x_2763_; uint8_t v___x_2764_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v___x_2761_ = l_Lean_Meta_Context_config(v___y_2757_);
v_transparency_2762_ = lean_ctor_get_uint8(v___x_2761_, 9);
lean_dec_ref(v___x_2761_);
v___x_2763_ = 1;
v___x_2764_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2762_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v_keyedConfig_2765_; uint8_t v_trackZetaDelta_2766_; lean_object* v_zetaDeltaSet_2767_; lean_object* v_lctx_2768_; lean_object* v_localInstances_2769_; lean_object* v_defEqCtx_x3f_2770_; lean_object* v_synthPendingDepth_2771_; lean_object* v_customCanUnfoldPredicate_x3f_2772_; uint8_t v_univApprox_2773_; uint8_t v_inTypeClassResolution_2774_; uint8_t v_cacheInferType_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_keyedConfig_2765_ = lean_ctor_get(v___y_2757_, 0);
v_trackZetaDelta_2766_ = lean_ctor_get_uint8(v___y_2757_, sizeof(void*)*7);
v_zetaDeltaSet_2767_ = lean_ctor_get(v___y_2757_, 1);
v_lctx_2768_ = lean_ctor_get(v___y_2757_, 2);
v_localInstances_2769_ = lean_ctor_get(v___y_2757_, 3);
v_defEqCtx_x3f_2770_ = lean_ctor_get(v___y_2757_, 4);
v_synthPendingDepth_2771_ = lean_ctor_get(v___y_2757_, 5);
v_customCanUnfoldPredicate_x3f_2772_ = lean_ctor_get(v___y_2757_, 6);
v_univApprox_2773_ = lean_ctor_get_uint8(v___y_2757_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2774_ = lean_ctor_get_uint8(v___y_2757_, sizeof(void*)*7 + 2);
v_cacheInferType_2775_ = lean_ctor_get_uint8(v___y_2757_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2765_);
v___x_2776_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2763_, v_keyedConfig_2765_);
lean_inc(v_customCanUnfoldPredicate_x3f_2772_);
lean_inc(v_synthPendingDepth_2771_);
lean_inc(v_defEqCtx_x3f_2770_);
lean_inc_ref(v_localInstances_2769_);
lean_inc_ref(v_lctx_2768_);
lean_inc(v_zetaDeltaSet_2767_);
v___x_2777_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v_zetaDeltaSet_2767_);
lean_ctor_set(v___x_2777_, 2, v_lctx_2768_);
lean_ctor_set(v___x_2777_, 3, v_localInstances_2769_);
lean_ctor_set(v___x_2777_, 4, v_defEqCtx_x3f_2770_);
lean_ctor_set(v___x_2777_, 5, v_synthPendingDepth_2771_);
lean_ctor_set(v___x_2777_, 6, v_customCanUnfoldPredicate_x3f_2772_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*7, v_trackZetaDelta_2766_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*7 + 1, v_univApprox_2773_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2774_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*7 + 3, v_cacheInferType_2775_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2753_);
lean_inc(v_a_2760_);
v___x_2778_ = lean_whnf(v_a_2760_, v___x_2777_, v___y_2753_, v___y_2756_, v___y_2758_);
v___y_2709_ = v___y_2753_;
v___y_2710_ = v___y_2754_;
v___y_2711_ = v___y_2755_;
v___y_2712_ = v___y_2756_;
v___y_2713_ = v_a_2760_;
v___y_2714_ = v___y_2757_;
v___y_2715_ = v___y_2758_;
v___y_2716_ = v___x_2778_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2779_; 
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2757_);
lean_inc(v_a_2760_);
v___x_2779_ = lean_whnf(v_a_2760_, v___y_2757_, v___y_2753_, v___y_2756_, v___y_2758_);
v___y_2709_ = v___y_2753_;
v___y_2710_ = v___y_2754_;
v___y_2711_ = v___y_2755_;
v___y_2712_ = v___y_2756_;
v___y_2713_ = v_a_2760_;
v___y_2714_ = v___y_2757_;
v___y_2715_ = v___y_2758_;
v___y_2716_ = v___x_2779_;
goto v___jp_2708_;
}
}
else
{
lean_object* v_a_2780_; 
v_a_2780_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2759_, 1);
v___y_2699_ = v___y_2753_;
v___y_2700_ = v___y_2754_;
v___y_2701_ = v___y_2755_;
v___y_2702_ = v___y_2756_;
v___y_2703_ = v___y_2757_;
v___y_2704_ = v___y_2758_;
v_a_2705_ = v_a_2780_;
goto v___jp_2698_;
}
}
v___jp_2781_:
{
if (v___y_2788_ == 0)
{
v___y_2680_ = v___y_2783_;
v___y_2681_ = v___y_2784_;
v___y_2682_ = v___y_2786_;
v___y_2683_ = v___y_2782_;
v___y_2684_ = v___y_2785_;
v___y_2685_ = v___y_2787_;
goto v___jp_2679_;
}
else
{
v___y_2753_ = v___y_2782_;
v___y_2754_ = v___y_2783_;
v___y_2755_ = v___y_2784_;
v___y_2756_ = v___y_2785_;
v___y_2757_ = v___y_2786_;
v___y_2758_ = v___y_2787_;
goto v___jp_2752_;
}
}
v___jp_2789_:
{
if (v___y_2797_ == 0)
{
lean_dec_ref(v___y_2792_);
v___y_2782_ = v___y_2790_;
v___y_2783_ = v___y_2791_;
v___y_2784_ = v___y_2793_;
v___y_2785_ = v___y_2794_;
v___y_2786_ = v___y_2795_;
v___y_2787_ = v___y_2796_;
v___y_2788_ = v___x_2634_;
goto v___jp_2781_;
}
else
{
uint8_t v___x_2798_; 
v___x_2798_ = l_Lean_Expr_hasFVar(v___y_2792_);
lean_dec_ref(v___y_2792_);
if (v___x_2798_ == 0)
{
v___y_2753_ = v___y_2790_;
v___y_2754_ = v___y_2791_;
v___y_2755_ = v___y_2793_;
v___y_2756_ = v___y_2794_;
v___y_2757_ = v___y_2795_;
v___y_2758_ = v___y_2796_;
goto v___jp_2752_;
}
else
{
v___y_2782_ = v___y_2790_;
v___y_2783_ = v___y_2791_;
v___y_2784_ = v___y_2793_;
v___y_2785_ = v___y_2794_;
v___y_2786_ = v___y_2795_;
v___y_2787_ = v___y_2796_;
v___y_2788_ = v___x_2634_;
goto v___jp_2781_;
}
}
}
v___jp_2799_:
{
lean_object* v___x_2807_; 
lean_inc_ref(v___x_2678_);
v___x_2807_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2678_, v___y_2800_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; uint8_t v___x_2809_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = l_Lean_Expr_hasMVar(v_a_2808_);
if (v___x_2809_ == 0)
{
v___y_2790_ = v___y_2800_;
v___y_2791_ = v___y_2801_;
v___y_2792_ = v_a_2808_;
v___y_2793_ = v___y_2802_;
v___y_2794_ = v___y_2803_;
v___y_2795_ = v___y_2804_;
v___y_2796_ = v___y_2805_;
v___y_2797_ = v___y_2806_;
goto v___jp_2789_;
}
else
{
v___y_2790_ = v___y_2800_;
v___y_2791_ = v___y_2801_;
v___y_2792_ = v_a_2808_;
v___y_2793_ = v___y_2802_;
v___y_2794_ = v___y_2803_;
v___y_2795_ = v___y_2804_;
v___y_2796_ = v___y_2805_;
v___y_2797_ = v___x_2634_;
goto v___jp_2789_;
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec_ref(v___x_2678_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2810_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2807_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2807_);
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
v___jp_2818_:
{
if (v___y_2825_ == 0)
{
v___y_2680_ = v___y_2820_;
v___y_2681_ = v___y_2821_;
v___y_2682_ = v___y_2823_;
v___y_2683_ = v___y_2819_;
v___y_2684_ = v___y_2822_;
v___y_2685_ = v___y_2824_;
goto v___jp_2679_;
}
else
{
v___y_2800_ = v___y_2819_;
v___y_2801_ = v___y_2820_;
v___y_2802_ = v___y_2821_;
v___y_2803_ = v___y_2822_;
v___y_2804_ = v___y_2823_;
v___y_2805_ = v___y_2824_;
v___y_2806_ = v___y_2825_;
goto v___jp_2799_;
}
}
v___jp_2826_:
{
uint8_t v_useDecide_2833_; 
v_useDecide_2833_ = lean_ctor_get_uint8(v_config_2529_, sizeof(void*)*1);
if (v_useDecide_2833_ == 0)
{
v___y_2819_ = v___y_2830_;
v___y_2820_ = v_isHEq_2828_;
v___y_2821_ = v___y_2827_;
v___y_2822_ = v___y_2831_;
v___y_2823_ = v___y_2829_;
v___y_2824_ = v___y_2832_;
v___y_2825_ = v___x_2634_;
goto v___jp_2818_;
}
else
{
uint8_t v___x_2834_; 
v___x_2834_ = l_Lean_Expr_hasFVar(v___x_2678_);
if (v___x_2834_ == 0)
{
v___y_2800_ = v___y_2830_;
v___y_2801_ = v_isHEq_2828_;
v___y_2802_ = v___y_2827_;
v___y_2803_ = v___y_2831_;
v___y_2804_ = v___y_2829_;
v___y_2805_ = v___y_2832_;
v___y_2806_ = v_useDecide_2833_;
goto v___jp_2799_;
}
else
{
v___y_2819_ = v___y_2830_;
v___y_2820_ = v_isHEq_2828_;
v___y_2821_ = v___y_2827_;
v___y_2822_ = v___y_2831_;
v___y_2823_ = v___y_2829_;
v___y_2824_ = v___y_2832_;
v___y_2825_ = v___x_2634_;
goto v___jp_2818_;
}
}
}
v___jp_2835_:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_Meta_isExprDefEq(v___y_2837_, v___y_2841_, v___y_2840_, v___y_2838_, v___y_2836_, v___y_2842_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; uint8_t v___x_2845_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = lean_unbox(v_a_2844_);
lean_dec(v_a_2844_);
if (v___x_2845_ == 0)
{
v___y_2827_ = v___y_2839_;
v_isHEq_2828_ = v___x_2540_;
v___y_2829_ = v___y_2840_;
v___y_2830_ = v___y_2838_;
v___y_2831_ = v___y_2836_;
v___y_2832_ = v___y_2842_;
goto v___jp_2826_;
}
else
{
lean_object* v___x_2846_; 
lean_dec_ref(v___x_2678_);
lean_dec_ref(v_config_2529_);
lean_inc(v_mvarId_2530_);
v___x_2846_ = l_Lean_MVarId_getType(v_mvarId_2530_, v___y_2840_, v___y_2838_, v___y_2836_, v___y_2842_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = l_Lean_LocalDecl_toExpr(v_val_2561_);
v___x_2849_ = l_Lean_Meta_mkEqOfHEq(v___x_2848_, v___x_2540_, v___y_2840_, v___y_2838_, v___y_2836_, v___y_2842_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = l_Lean_Meta_mkNoConfusion(v_a_2847_, v_a_2850_, v___y_2840_, v___y_2838_, v___y_2836_, v___y_2842_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2853_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2851_, 1);
v___x_2853_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2530_, v_a_2852_, v___y_2838_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec_ref_known(v___x_2853_, 1);
v___x_2854_ = lean_box(v___x_2540_);
v___x_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2565_);
v_a_2547_ = v___x_2856_;
goto v___jp_2546_;
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
v_a_2857_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2853_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2853_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_2865_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2851_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2851_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v_a_2847_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_2873_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2849_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2849_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_2881_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2846_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2846_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec_ref(v___x_2678_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2889_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2843_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2843_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
v___jp_2897_:
{
lean_object* v___x_2903_; 
lean_inc_ref(v___x_2678_);
v___x_2903_ = l_Lean_Meta_matchHEq_x3f(v___x_2678_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
if (lean_obj_tag(v_a_2904_) == 1)
{
lean_object* v_val_2905_; lean_object* v_snd_2906_; lean_object* v_snd_2907_; lean_object* v_fst_2908_; lean_object* v_fst_2909_; lean_object* v_fst_2910_; lean_object* v_snd_2911_; lean_object* v___x_2912_; 
v_val_2905_ = lean_ctor_get(v_a_2904_, 0);
lean_inc(v_val_2905_);
lean_dec_ref_known(v_a_2904_, 1);
v_snd_2906_ = lean_ctor_get(v_val_2905_, 1);
lean_inc(v_snd_2906_);
v_snd_2907_ = lean_ctor_get(v_snd_2906_, 1);
lean_inc(v_snd_2907_);
v_fst_2908_ = lean_ctor_get(v_val_2905_, 0);
lean_inc(v_fst_2908_);
lean_dec(v_val_2905_);
v_fst_2909_ = lean_ctor_get(v_snd_2906_, 0);
lean_inc(v_fst_2909_);
lean_dec(v_snd_2906_);
v_fst_2910_ = lean_ctor_get(v_snd_2907_, 0);
lean_inc(v_fst_2910_);
v_snd_2911_ = lean_ctor_get(v_snd_2907_, 1);
lean_inc(v_snd_2911_);
lean_dec(v_snd_2907_);
v___x_2912_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2909_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
if (lean_obj_tag(v_a_2913_) == 1)
{
lean_object* v_val_2914_; lean_object* v___x_2915_; 
v_val_2914_ = lean_ctor_get(v_a_2913_, 0);
lean_inc(v_val_2914_);
lean_dec_ref_known(v_a_2913_, 1);
v___x_2915_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2911_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
if (lean_obj_tag(v_a_2916_) == 1)
{
lean_object* v_toConstantVal_2917_; lean_object* v_val_2918_; lean_object* v_toConstantVal_2919_; lean_object* v_name_2920_; lean_object* v_name_2921_; uint8_t v___x_2922_; 
v_toConstantVal_2917_ = lean_ctor_get(v_val_2914_, 0);
lean_inc_ref(v_toConstantVal_2917_);
lean_dec(v_val_2914_);
v_val_2918_ = lean_ctor_get(v_a_2916_, 0);
lean_inc(v_val_2918_);
lean_dec_ref_known(v_a_2916_, 1);
v_toConstantVal_2919_ = lean_ctor_get(v_val_2918_, 0);
lean_inc_ref(v_toConstantVal_2919_);
lean_dec(v_val_2918_);
v_name_2920_ = lean_ctor_get(v_toConstantVal_2917_, 0);
lean_inc(v_name_2920_);
lean_dec_ref(v_toConstantVal_2917_);
v_name_2921_ = lean_ctor_get(v_toConstantVal_2919_, 0);
lean_inc(v_name_2921_);
lean_dec_ref(v_toConstantVal_2919_);
v___x_2922_ = lean_name_eq(v_name_2920_, v_name_2921_);
lean_dec(v_name_2921_);
lean_dec(v_name_2920_);
if (v___x_2922_ == 0)
{
v___y_2836_ = v___y_2901_;
v___y_2837_ = v_fst_2908_;
v___y_2838_ = v___y_2900_;
v___y_2839_ = v_isEq_2898_;
v___y_2840_ = v___y_2899_;
v___y_2841_ = v_fst_2910_;
v___y_2842_ = v___y_2902_;
goto v___jp_2835_;
}
else
{
if (v___x_2634_ == 0)
{
lean_dec(v_fst_2910_);
lean_dec(v_fst_2908_);
v___y_2827_ = v_isEq_2898_;
v_isHEq_2828_ = v___x_2540_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
v___y_2831_ = v___y_2901_;
v___y_2832_ = v___y_2902_;
goto v___jp_2826_;
}
else
{
v___y_2836_ = v___y_2901_;
v___y_2837_ = v_fst_2908_;
v___y_2838_ = v___y_2900_;
v___y_2839_ = v_isEq_2898_;
v___y_2840_ = v___y_2899_;
v___y_2841_ = v_fst_2910_;
v___y_2842_ = v___y_2902_;
goto v___jp_2835_;
}
}
}
else
{
lean_dec(v_a_2916_);
lean_dec(v_val_2914_);
lean_dec(v_fst_2910_);
lean_dec(v_fst_2908_);
v___y_2827_ = v_isEq_2898_;
v_isHEq_2828_ = v___x_2540_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
v___y_2831_ = v___y_2901_;
v___y_2832_ = v___y_2902_;
goto v___jp_2826_;
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_val_2914_);
lean_dec(v_fst_2910_);
lean_dec(v_fst_2908_);
lean_dec_ref(v___x_2678_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2923_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2915_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2915_);
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
else
{
lean_dec(v_a_2913_);
lean_dec(v_snd_2911_);
lean_dec(v_fst_2910_);
lean_dec(v_fst_2908_);
v___y_2827_ = v_isEq_2898_;
v_isHEq_2828_ = v___x_2540_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
v___y_2831_ = v___y_2901_;
v___y_2832_ = v___y_2902_;
goto v___jp_2826_;
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v_snd_2911_);
lean_dec(v_fst_2910_);
lean_dec(v_fst_2908_);
lean_dec_ref(v___x_2678_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2931_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2912_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2912_);
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
lean_dec(v_a_2904_);
v___y_2827_ = v_isEq_2898_;
v_isHEq_2828_ = v___x_2634_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
v___y_2831_ = v___y_2901_;
v___y_2832_ = v___y_2902_;
goto v___jp_2826_;
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec_ref(v___x_2678_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2939_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2903_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2903_);
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
v___jp_2947_:
{
lean_object* v___x_2952_; 
lean_inc_ref(v___x_2678_);
v___x_2952_ = l_Lean_Meta_matchEq_x3f(v___x_2678_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
if (lean_obj_tag(v_a_2953_) == 1)
{
lean_object* v_val_2954_; lean_object* v_snd_2955_; lean_object* v_fst_2956_; lean_object* v_snd_2957_; lean_object* v___x_2958_; 
v_val_2954_ = lean_ctor_get(v_a_2953_, 0);
lean_inc(v_val_2954_);
lean_dec_ref_known(v_a_2953_, 1);
v_snd_2955_ = lean_ctor_get(v_val_2954_, 1);
lean_inc(v_snd_2955_);
lean_dec(v_val_2954_);
v_fst_2956_ = lean_ctor_get(v_snd_2955_, 0);
lean_inc(v_fst_2956_);
v_snd_2957_ = lean_ctor_get(v_snd_2955_, 1);
lean_inc(v_snd_2957_);
lean_dec(v_snd_2955_);
v___x_2958_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2956_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
if (lean_obj_tag(v_a_2959_) == 1)
{
lean_object* v_val_2960_; lean_object* v___x_2961_; 
v_val_2960_ = lean_ctor_get(v_a_2959_, 0);
lean_inc(v_val_2960_);
lean_dec_ref_known(v_a_2959_, 1);
v___x_2961_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2957_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
if (lean_obj_tag(v_a_2962_) == 1)
{
lean_object* v_toConstantVal_2963_; lean_object* v_val_2964_; lean_object* v_toConstantVal_2965_; lean_object* v_name_2966_; lean_object* v_name_2967_; uint8_t v___x_2968_; 
v_toConstantVal_2963_ = lean_ctor_get(v_val_2960_, 0);
lean_inc_ref(v_toConstantVal_2963_);
lean_dec(v_val_2960_);
v_val_2964_ = lean_ctor_get(v_a_2962_, 0);
lean_inc(v_val_2964_);
lean_dec_ref_known(v_a_2962_, 1);
v_toConstantVal_2965_ = lean_ctor_get(v_val_2964_, 0);
lean_inc_ref(v_toConstantVal_2965_);
lean_dec(v_val_2964_);
v_name_2966_ = lean_ctor_get(v_toConstantVal_2963_, 0);
lean_inc(v_name_2966_);
lean_dec_ref(v_toConstantVal_2963_);
v_name_2967_ = lean_ctor_get(v_toConstantVal_2965_, 0);
lean_inc(v_name_2967_);
lean_dec_ref(v_toConstantVal_2965_);
v___x_2968_ = lean_name_eq(v_name_2966_, v_name_2967_);
lean_dec(v_name_2967_);
lean_dec(v_name_2966_);
if (v___x_2968_ == 0)
{
lean_dec_ref(v___x_2678_);
lean_dec_ref(v_config_2529_);
v___y_2567_ = v___y_2951_;
v___y_2568_ = v___y_2949_;
v___y_2569_ = v___y_2948_;
v___y_2570_ = v___y_2950_;
goto v___jp_2566_;
}
else
{
if (v___x_2634_ == 0)
{
lean_del_object(v___x_2563_);
v_isEq_2898_ = v___x_2540_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
v___y_2901_ = v___y_2950_;
v___y_2902_ = v___y_2951_;
goto v___jp_2897_;
}
else
{
lean_dec_ref(v___x_2678_);
lean_dec_ref(v_config_2529_);
v___y_2567_ = v___y_2951_;
v___y_2568_ = v___y_2949_;
v___y_2569_ = v___y_2948_;
v___y_2570_ = v___y_2950_;
goto v___jp_2566_;
}
}
}
else
{
lean_dec(v_a_2962_);
lean_dec(v_val_2960_);
lean_del_object(v___x_2563_);
v_isEq_2898_ = v___x_2540_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
v___y_2901_ = v___y_2950_;
v___y_2902_ = v___y_2951_;
goto v___jp_2897_;
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_val_2960_);
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2969_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2961_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2961_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_dec(v_a_2959_);
lean_dec(v_snd_2957_);
lean_del_object(v___x_2563_);
v_isEq_2898_ = v___x_2540_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
v___y_2901_ = v___y_2950_;
v___y_2902_ = v___y_2951_;
goto v___jp_2897_;
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v_snd_2957_);
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2977_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2958_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2958_);
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
lean_dec(v_a_2953_);
lean_del_object(v___x_2563_);
v_isEq_2898_ = v___x_2634_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
v___y_2901_ = v___y_2950_;
v___y_2902_ = v___y_2951_;
goto v___jp_2897_;
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2985_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2952_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2952_);
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
v___jp_2993_:
{
lean_object* v___x_2998_; 
lean_inc_ref(v___x_2678_);
v___x_2998_ = l_Lean_refutableHasNotBit_x3f(v___x_2678_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
if (lean_obj_tag(v_a_2999_) == 1)
{
lean_object* v_val_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec_ref(v_config_2529_);
v_val_3000_ = lean_ctor_get(v_a_2999_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_a_2999_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3002_ = v_a_2999_;
v_isShared_3003_ = v_isSharedCheck_3039_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_val_3000_);
lean_dec(v_a_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3039_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; 
lean_inc(v_mvarId_2530_);
v___x_3004_ = l_Lean_MVarId_getType(v_mvarId_2530_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = l_Lean_LocalDecl_toExpr(v_val_2561_);
v___x_3007_ = l_Lean_Meta_mkAbsurd(v_a_3005_, v_val_3000_, v___x_3006_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3009_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3007_, 1);
v___x_3009_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2530_, v_a_3008_, v___y_2995_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
lean_dec_ref_known(v___x_3009_, 1);
v___x_3010_ = lean_box(v___x_2540_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_3010_);
v___x_3012_ = v___x_3002_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_2565_);
v_a_2547_ = v___x_3013_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_del_object(v___x_3002_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
v_a_3015_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3009_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3009_);
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
lean_del_object(v___x_3002_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_3023_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3007_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3007_);
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
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_del_object(v___x_3002_);
lean_dec(v_val_3000_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_3031_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3004_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3004_);
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
else
{
lean_object* v___x_3040_; 
lean_dec(v_a_2999_);
lean_inc_ref(v___x_2678_);
v___x_3040_ = l_Lean_Meta_matchNe_x3f(v___x_2678_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
if (lean_obj_tag(v_a_3041_) == 1)
{
lean_object* v_val_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3111_; 
v_val_3042_ = lean_ctor_get(v_a_3041_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_a_3041_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3044_ = v_a_3041_;
v_isShared_3045_ = v_isSharedCheck_3111_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_val_3042_);
lean_dec(v_a_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3111_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v_snd_3046_; lean_object* v_fst_3047_; lean_object* v_snd_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3110_; 
v_snd_3046_ = lean_ctor_get(v_val_3042_, 1);
lean_inc(v_snd_3046_);
lean_dec(v_val_3042_);
v_fst_3047_ = lean_ctor_get(v_snd_3046_, 0);
v_snd_3048_ = lean_ctor_get(v_snd_3046_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_snd_3046_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3050_ = v_snd_3046_;
v_isShared_3051_ = v_isSharedCheck_3110_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_snd_3048_);
lean_inc(v_fst_3047_);
lean_dec(v_snd_3046_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3110_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; 
lean_inc(v_fst_3047_);
v___x_3052_ = l_Lean_Meta_isExprDefEq(v_fst_3047_, v_snd_3048_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; uint8_t v___x_3054_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3054_ = lean_unbox(v_a_3053_);
lean_dec(v_a_3053_);
if (v___x_3054_ == 0)
{
lean_del_object(v___x_3050_);
lean_dec(v_fst_3047_);
lean_del_object(v___x_3044_);
v___y_2948_ = v___y_2994_;
v___y_2949_ = v___y_2995_;
v___y_2950_ = v___y_2996_;
v___y_2951_ = v___y_2997_;
goto v___jp_2947_;
}
else
{
lean_object* v___x_3055_; 
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec_ref(v_config_2529_);
lean_inc(v_mvarId_2530_);
v___x_3055_ = l_Lean_MVarId_getType(v_mvarId_2530_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3057_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
v___x_3057_ = l_Lean_Meta_mkEqRefl(v_fst_3047_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
v___x_3059_ = l_Lean_LocalDecl_toExpr(v_val_2561_);
v___x_3060_ = l_Lean_Meta_mkAbsurd(v_a_3056_, v_a_3058_, v___x_3059_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3062_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2530_, v_a_3061_, v___y_2995_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
lean_dec_ref_known(v___x_3062_, 1);
v___x_3063_ = lean_box(v___x_2540_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v___x_3063_);
v___x_3065_ = v___x_3044_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3067_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 1, v___x_2565_);
lean_ctor_set(v___x_3050_, 0, v___x_3065_);
v___x_3067_ = v___x_3050_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3065_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_2565_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
v_a_2547_ = v___x_3067_;
goto v___jp_2546_;
}
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_del_object(v___x_3050_);
lean_del_object(v___x_3044_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
v_a_3070_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3062_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3062_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_del_object(v___x_3050_);
lean_del_object(v___x_3044_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_3078_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3060_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3060_);
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
lean_dec(v_a_3056_);
lean_del_object(v___x_3050_);
lean_del_object(v___x_3044_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_3086_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3057_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3057_);
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
lean_del_object(v___x_3050_);
lean_dec(v_fst_3047_);
lean_del_object(v___x_3044_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_3094_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3055_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3055_);
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
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_del_object(v___x_3050_);
lean_dec(v_fst_3047_);
lean_del_object(v___x_3044_);
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_3102_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3052_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3052_);
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
}
}
else
{
lean_dec(v_a_3041_);
v___y_2948_ = v___y_2994_;
v___y_2949_ = v___y_2995_;
v___y_2950_ = v___y_2996_;
v___y_2951_ = v___y_2997_;
goto v___jp_2947_;
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_3112_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3040_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3040_);
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
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v___x_2678_);
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_3120_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_2998_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_2998_);
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
}
else
{
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
v_a_2555_ = v___x_2606_;
goto v___jp_2554_;
}
v___jp_2566_:
{
lean_object* v___x_2571_; 
lean_inc(v_mvarId_2530_);
v___x_2571_ = l_Lean_MVarId_getType(v_mvarId_2530_, v___y_2569_, v___y_2568_, v___y_2570_, v___y_2567_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2573_ = l_Lean_LocalDecl_toExpr(v_val_2561_);
v___x_2574_ = l_Lean_Meta_mkNoConfusion(v_a_2572_, v___x_2573_, v___y_2569_, v___y_2568_, v___y_2570_, v___y_2567_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2530_, v_a_2575_, v___y_2568_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec_ref_known(v___x_2576_, 1);
v___x_2577_ = lean_box(v___x_2540_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2577_);
v___x_2579_ = v___x_2563_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2565_);
v_a_2547_ = v___x_2580_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_del_object(v___x_2563_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
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
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_del_object(v___x_2563_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_2590_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2574_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2574_);
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
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_del_object(v___x_2563_);
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
v_a_2598_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2571_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2571_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
v___jp_2607_:
{
lean_object* v_searchFuel_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_searchFuel_2612_ = lean_ctor_get(v_config_2529_, 0);
v___x_2613_ = l_Lean_LocalDecl_fvarId(v_val_2561_);
lean_dec(v_val_2561_);
lean_inc(v_searchFuel_2612_);
lean_inc(v_mvarId_2530_);
v___x_2614_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2530_, v___x_2613_, v_searchFuel_2612_, v___y_2608_, v___y_2610_, v___y_2611_, v___y_2609_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; uint8_t v___x_2616_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = lean_unbox(v_a_2615_);
lean_dec(v_a_2615_);
if (v___x_2616_ == 0)
{
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
v_a_2555_ = v___x_2606_;
goto v___jp_2554_;
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v___x_2617_ = lean_box(v___x_2540_);
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v___x_2565_);
v_a_2547_ = v___x_2619_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2620_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2614_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2614_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
v___jp_2628_:
{
if (v___y_2633_ == 0)
{
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
v_a_2555_ = v___x_2606_;
goto v___jp_2554_;
}
else
{
v___y_2608_ = v___y_2629_;
v___y_2609_ = v___y_2630_;
v___y_2610_ = v___y_2631_;
v___y_2611_ = v___y_2632_;
goto v___jp_2607_;
}
}
v___jp_2635_:
{
if (v___y_2637_ == 0)
{
v___y_2608_ = v___y_2636_;
v___y_2609_ = v___y_2638_;
v___y_2610_ = v___y_2639_;
v___y_2611_ = v___y_2640_;
goto v___jp_2607_;
}
else
{
v___y_2629_ = v___y_2636_;
v___y_2630_ = v___y_2638_;
v___y_2631_ = v___y_2639_;
v___y_2632_ = v___y_2640_;
v___y_2633_ = v___x_2634_;
goto v___jp_2628_;
}
}
v___jp_2641_:
{
if (v___y_2647_ == 0)
{
v___y_2629_ = v___y_2642_;
v___y_2630_ = v___y_2644_;
v___y_2631_ = v___y_2645_;
v___y_2632_ = v___y_2646_;
v___y_2633_ = v___x_2634_;
goto v___jp_2628_;
}
else
{
v___y_2636_ = v___y_2642_;
v___y_2637_ = v___y_2643_;
v___y_2638_ = v___y_2644_;
v___y_2639_ = v___y_2645_;
v___y_2640_ = v___y_2646_;
goto v___jp_2635_;
}
}
v___jp_2648_:
{
uint8_t v_emptyType_2655_; 
v_emptyType_2655_ = lean_ctor_get_uint8(v_config_2529_, sizeof(void*)*1 + 1);
if (v_emptyType_2655_ == 0)
{
v___y_2642_ = v___y_2651_;
v___y_2643_ = v___y_2649_;
v___y_2644_ = v___y_2654_;
v___y_2645_ = v___y_2652_;
v___y_2646_ = v___y_2653_;
v___y_2647_ = v___x_2634_;
goto v___jp_2641_;
}
else
{
if (v___y_2650_ == 0)
{
v___y_2636_ = v___y_2651_;
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2654_;
v___y_2639_ = v___y_2652_;
v___y_2640_ = v___y_2653_;
goto v___jp_2635_;
}
else
{
v___y_2642_ = v___y_2651_;
v___y_2643_ = v___y_2649_;
v___y_2644_ = v___y_2654_;
v___y_2645_ = v___y_2652_;
v___y_2646_ = v___y_2653_;
v___y_2647_ = v___x_2634_;
goto v___jp_2641_;
}
}
}
v___jp_2656_:
{
if (v___y_2663_ == 0)
{
v___y_2649_ = v___y_2658_;
v___y_2650_ = v___y_2661_;
v___y_2651_ = v___y_2662_;
v___y_2652_ = v___y_2657_;
v___y_2653_ = v___y_2660_;
v___y_2654_ = v___y_2659_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2664_; 
lean_inc(v_val_2561_);
lean_inc(v_mvarId_2530_);
v___x_2664_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2530_, v_val_2561_, v___y_2662_, v___y_2657_, v___y_2660_, v___y_2659_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; uint8_t v___x_2666_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2666_ = lean_unbox(v_a_2665_);
lean_dec(v_a_2665_);
if (v___x_2666_ == 0)
{
v___y_2649_ = v___y_2658_;
v___y_2650_ = v___y_2661_;
v___y_2651_ = v___y_2662_;
v___y_2652_ = v___y_2657_;
v___y_2653_ = v___y_2660_;
v___y_2654_ = v___y_2659_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec(v_val_2561_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v___x_2667_ = lean_box(v___x_2540_);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
lean_ctor_set(v___x_2669_, 1, v___x_2565_);
v_a_2547_ = v___x_2669_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_val_2561_);
lean_del_object(v___x_2544_);
lean_dec(v_snd_2542_);
lean_dec(v_mvarId_2530_);
lean_dec_ref(v_config_2529_);
v_a_2670_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2664_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2664_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
}
v___jp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_a_2547_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2548_);
v___x_2550_ = v___x_2544_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_snd_2542_);
v___x_2550_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
}
v___jp_2554_:
{
lean_object* v___x_2556_; size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2553_);
lean_ctor_set(v___x_2556_, 1, v_a_2555_);
v___x_2557_ = ((size_t)1ULL);
v___x_2558_ = lean_usize_add(v_i_2533_, v___x_2557_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2529_, v_mvarId_2530_, v_as_2531_, v_sz_2532_, v___x_2558_, v___x_2556_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
return v___x_2559_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_2529_ = stack[0].m_obj;
lean_object* v_mvarId_2530_ = stack[1].m_obj;
lean_object* v_as_2531_ = stack[2].m_obj;
size_t v_sz_2532_ = stack[3].m_num;
size_t v_i_2533_ = stack[4].m_num;
lean_object* v_b_2534_ = stack[5].m_obj;
lean_object* v___y_2535_ = stack[6].m_obj;
lean_object* v___y_2536_ = stack[7].m_obj;
lean_object* v___y_2537_ = stack[8].m_obj;
lean_object* v___y_2538_ = stack[9].m_obj;
lean_object* v_res_3194_;
v_res_3194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_2529_, v_mvarId_2530_, v_as_2531_, v_sz_2532_, v_i_2533_, v_b_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
stack->m_obj
 = v_res_3194_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3195_, lean_object* v_mvarId_3196_, lean_object* v_as_3197_, lean_object* v_sz_3198_, lean_object* v_i_3199_, lean_object* v_b_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
size_t v_sz_boxed_3206_; size_t v_i_boxed_3207_; lean_object* v_res_3208_; 
v_sz_boxed_3206_ = lean_unbox_usize(v_sz_3198_);
lean_dec(v_sz_3198_);
v_i_boxed_3207_ = lean_unbox_usize(v_i_3199_);
lean_dec(v_i_3199_);
v_res_3208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3195_, v_mvarId_3196_, v_as_3197_, v_sz_boxed_3206_, v_i_boxed_3207_, v_b_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_as_3197_);
return v_res_3208_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3212_, lean_object* v_mvarId_3213_, lean_object* v_as_3214_, size_t v_sz_3215_, size_t v_i_3216_, lean_object* v_b_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_usize_dec_lt(v_i_3216_, v_sz_3215_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_b_3217_);
return v___x_3224_;
}
else
{
lean_object* v_snd_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3895_; 
v_snd_3225_ = lean_ctor_get(v_b_3217_, 1);
v_isSharedCheck_3895_ = !lean_is_exclusive(v_b_3217_);
if (v_isSharedCheck_3895_ == 0)
{
lean_object* v_unused_3896_; 
v_unused_3896_ = lean_ctor_get(v_b_3217_, 0);
lean_dec(v_unused_3896_);
v___x_3227_ = v_b_3217_;
v_isShared_3228_ = v_isSharedCheck_3895_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_snd_3225_);
lean_dec(v_b_3217_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3895_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v_a_3230_; lean_object* v___x_3236_; lean_object* v_a_3238_; lean_object* v_a_3243_; 
v___x_3236_ = lean_box(0);
v_a_3243_ = lean_array_uget(v_as_3214_, v_i_3216_);
if (lean_obj_tag(v_a_3243_) == 0)
{
lean_del_object(v___x_3227_);
v_a_3238_ = v_snd_3225_;
goto v___jp_3237_;
}
else
{
lean_object* v_val_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3894_; 
v_val_3244_ = lean_ctor_get(v_a_3243_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_a_3243_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3246_ = v_a_3243_;
v_isShared_3247_ = v_isSharedCheck_3894_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_val_3244_);
lean_dec(v_a_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3894_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___x_3290_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; uint8_t v___y_3318_; uint8_t v___x_3319_; uint8_t v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; uint8_t v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; uint8_t v___y_3332_; uint8_t v___y_3334_; uint8_t v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; uint8_t v___y_3342_; uint8_t v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; uint8_t v___y_3348_; 
v___x_3248_ = lean_box(0);
v___x_3290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3319_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3244_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3364_; uint8_t v___y_3366_; uint8_t v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3375_; uint8_t v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; uint8_t v___y_3381_; uint8_t v___y_3382_; uint8_t v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; uint8_t v___y_3390_; lean_object* v_a_3391_; lean_object* v___y_3395_; uint8_t v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; uint8_t v___y_3401_; lean_object* v___y_3402_; uint8_t v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; uint8_t v___y_3451_; uint8_t v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; uint8_t v___y_3480_; uint8_t v___y_3481_; lean_object* v___y_3483_; uint8_t v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; uint8_t v___y_3489_; uint8_t v___y_3490_; uint8_t v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; uint8_t v___y_3498_; uint8_t v___y_3499_; uint8_t v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; uint8_t v___y_3517_; uint8_t v___y_3518_; uint8_t v___y_3520_; uint8_t v_isHEq_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; uint8_t v_isEq_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___x_3824_; 
v___x_3364_ = l_Lean_LocalDecl_type(v_val_3244_);
lean_inc_ref(v___x_3364_);
v___x_3824_ = l_Lean_Meta_matchNot_x3f(v___x_3364_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
if (lean_obj_tag(v_a_3825_) == 1)
{
lean_object* v_val_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3885_; 
v_val_3826_ = lean_ctor_get(v_a_3825_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_a_3825_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3828_ = v_a_3825_;
v_isShared_3829_ = v_isSharedCheck_3885_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_val_3826_);
lean_dec(v_a_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3885_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3826_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
if (lean_obj_tag(v_a_3831_) == 1)
{
lean_object* v_val_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3876_; 
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec_ref(v_config_3212_);
v_val_3832_ = lean_ctor_get(v_a_3831_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v_a_3831_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3834_ = v_a_3831_;
v_isShared_3835_ = v_isSharedCheck_3876_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_val_3832_);
lean_dec(v_a_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3876_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; 
lean_inc(v_mvarId_3213_);
v___x_3836_ = l_Lean_MVarId_getType(v_mvarId_3213_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v___x_3836_, 1);
v___x_3838_ = l_Lean_LocalDecl_toExpr(v_val_3244_);
v___x_3839_ = l_Lean_mkFVar(v_val_3832_);
v___x_3840_ = l_Lean_Expr_app___override(v___x_3838_, v___x_3839_);
v___x_3841_ = l_Lean_Meta_mkFalseElim(v_a_3837_, v___x_3840_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; lean_object* v___x_3843_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v___x_3841_, 1);
v___x_3843_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3213_, v_a_3842_, v___y_3219_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v___x_3844_; lean_object* v___x_3846_; 
lean_dec_ref_known(v___x_3843_, 1);
v___x_3844_ = lean_box(v___x_3223_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 0, v___x_3844_);
v___x_3846_ = v___x_3834_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
lean_ctor_set(v___x_3847_, 1, v___x_3248_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set_tag(v___x_3828_, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3847_);
v___x_3849_ = v___x_3828_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
v_a_3230_ = v___x_3849_;
goto v___jp_3229_;
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_del_object(v___x_3834_);
lean_del_object(v___x_3828_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
v_a_3852_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3843_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3843_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_del_object(v___x_3834_);
lean_del_object(v___x_3828_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3860_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3841_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3841_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_del_object(v___x_3834_);
lean_dec(v_val_3832_);
lean_del_object(v___x_3828_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3868_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3836_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3836_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
}
else
{
lean_dec(v_a_3831_);
lean_del_object(v___x_3828_);
v___y_3688_ = v___y_3218_;
v___y_3689_ = v___y_3219_;
v___y_3690_ = v___y_3220_;
v___y_3691_ = v___y_3221_;
goto v___jp_3687_;
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_del_object(v___x_3828_);
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3877_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3830_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3830_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
else
{
lean_dec(v_a_3825_);
v___y_3688_ = v___y_3218_;
v___y_3689_ = v___y_3219_;
v___y_3690_ = v___y_3220_;
v___y_3691_ = v___y_3221_;
goto v___jp_3687_;
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3886_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3824_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3824_);
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
v___jp_3365_:
{
uint8_t v_genDiseq_3372_; 
v_genDiseq_3372_ = lean_ctor_get_uint8(v_config_3212_, sizeof(void*)*1 + 2);
if (v_genDiseq_3372_ == 0)
{
lean_dec_ref(v___x_3364_);
v___y_3342_ = v___y_3366_;
v___y_3343_ = v___y_3367_;
v___y_3344_ = v___y_3369_;
v___y_3345_ = v___y_3370_;
v___y_3346_ = v___y_3371_;
v___y_3347_ = v___y_3368_;
v___y_3348_ = v___x_3319_;
goto v___jp_3341_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3364_);
v___y_3342_ = v___y_3366_;
v___y_3343_ = v___y_3367_;
v___y_3344_ = v___y_3369_;
v___y_3345_ = v___y_3370_;
v___y_3346_ = v___y_3371_;
v___y_3347_ = v___y_3368_;
v___y_3348_ = v___x_3373_;
goto v___jp_3341_;
}
}
v___jp_3374_:
{
if (v___y_3382_ == 0)
{
lean_dec_ref(v___y_3375_);
v___y_3366_ = v___y_3376_;
v___y_3367_ = v___y_3381_;
v___y_3368_ = v___y_3377_;
v___y_3369_ = v___y_3380_;
v___y_3370_ = v___y_3379_;
v___y_3371_ = v___y_3378_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3383_; 
lean_dec_ref(v___x_3364_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v___x_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3383_, 0, v___y_3375_);
return v___x_3383_;
}
}
v___jp_3384_:
{
uint8_t v___x_3392_; 
v___x_3392_ = l_Lean_Exception_isInterrupt(v_a_3391_);
if (v___x_3392_ == 0)
{
uint8_t v___x_3393_; 
lean_inc_ref(v_a_3391_);
v___x_3393_ = l_Lean_Exception_isRuntime(v_a_3391_);
v___y_3375_ = v_a_3391_;
v___y_3376_ = v___y_3385_;
v___y_3377_ = v___y_3386_;
v___y_3378_ = v___y_3387_;
v___y_3379_ = v___y_3389_;
v___y_3380_ = v___y_3388_;
v___y_3381_ = v___y_3390_;
v___y_3382_ = v___x_3393_;
goto v___jp_3374_;
}
else
{
v___y_3375_ = v_a_3391_;
v___y_3376_ = v___y_3385_;
v___y_3377_ = v___y_3386_;
v___y_3378_ = v___y_3387_;
v___y_3379_ = v___y_3389_;
v___y_3380_ = v___y_3388_;
v___y_3381_ = v___y_3390_;
v___y_3382_ = v___x_3392_;
goto v___jp_3374_;
}
}
v___jp_3394_:
{
if (lean_obj_tag(v___y_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v_a_3403_ = lean_ctor_get(v___y_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___y_3402_, 1);
v___x_3404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3405_ = l_Lean_Expr_isConstOf(v_a_3403_, v___x_3404_);
lean_dec(v_a_3403_);
if (v___x_3405_ == 0)
{
lean_dec_ref(v___y_3395_);
v___y_3366_ = v___y_3396_;
v___y_3367_ = v___y_3401_;
v___y_3368_ = v___y_3397_;
v___y_3369_ = v___y_3400_;
v___y_3370_ = v___y_3399_;
v___y_3371_ = v___y_3398_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3406_; 
lean_inc_ref(v___y_3395_);
v___x_3406_ = l_Lean_Meta_mkEqRefl(v___y_3395_, v___y_3397_, v___y_3400_, v___y_3399_, v___y_3398_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3408_; lean_object* v_dummy_3409_; lean_object* v_nargs_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v___x_3408_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3409_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3410_ = l_Lean_Expr_getAppNumArgs(v___y_3395_);
lean_inc(v_nargs_3410_);
v___x_3411_ = lean_mk_array(v_nargs_3410_, v_dummy_3409_);
v___x_3412_ = lean_unsigned_to_nat(1u);
v___x_3413_ = lean_nat_sub(v_nargs_3410_, v___x_3412_);
lean_dec(v_nargs_3410_);
v___x_3414_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3395_, v___x_3411_, v___x_3413_);
v___x_3415_ = lean_array_push(v___x_3414_, v_a_3407_);
v___x_3416_ = l_Lean_mkAppN(v___x_3408_, v___x_3415_);
lean_dec_ref(v___x_3415_);
lean_inc(v_mvarId_3213_);
v___x_3417_ = l_Lean_MVarId_getType(v_mvarId_3213_, v___y_3397_, v___y_3400_, v___y_3399_, v___y_3398_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3417_, 1);
lean_inc(v_val_3244_);
v___x_3419_ = l_Lean_LocalDecl_toExpr(v_val_3244_);
v___x_3420_ = l_Lean_Meta_mkAbsurd(v_a_3418_, v___x_3419_, v___x_3416_, v___y_3397_, v___y_3400_, v___y_3399_, v___y_3398_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3440_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3423_ = v___x_3420_;
v_isShared_3424_ = v_isSharedCheck_3440_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3420_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3440_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; 
lean_inc(v_mvarId_3213_);
v___x_3425_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3213_, v_a_3421_, v___y_3400_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v___x_3364_);
lean_dec(v_val_3244_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3437_ == 0)
{
lean_object* v_unused_3438_; 
v_unused_3438_ = lean_ctor_get(v___x_3425_, 0);
lean_dec(v_unused_3438_);
v___x_3427_ = v___x_3425_;
v_isShared_3428_ = v_isSharedCheck_3437_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v___x_3425_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3437_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_box(v___x_3223_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 1);
lean_ctor_set(v___x_3427_, 0, v___x_3429_);
v___x_3431_ = v___x_3427_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
lean_ctor_set(v___x_3432_, 1, v___x_3248_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v___x_3432_);
v___x_3434_ = v___x_3423_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
v_a_3230_ = v___x_3434_;
goto v___jp_3229_;
}
}
}
}
else
{
lean_object* v_a_3439_; 
lean_del_object(v___x_3423_);
v_a_3439_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3425_, 1);
v___y_3385_ = v___y_3396_;
v___y_3386_ = v___y_3397_;
v___y_3387_ = v___y_3398_;
v___y_3388_ = v___y_3400_;
v___y_3389_ = v___y_3399_;
v___y_3390_ = v___y_3401_;
v_a_3391_ = v_a_3439_;
goto v___jp_3384_;
}
}
}
else
{
lean_object* v_a_3441_; 
v_a_3441_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3420_, 1);
v___y_3385_ = v___y_3396_;
v___y_3386_ = v___y_3397_;
v___y_3387_ = v___y_3398_;
v___y_3388_ = v___y_3400_;
v___y_3389_ = v___y_3399_;
v___y_3390_ = v___y_3401_;
v_a_3391_ = v_a_3441_;
goto v___jp_3384_;
}
}
else
{
lean_object* v_a_3442_; 
lean_dec_ref(v___x_3416_);
v_a_3442_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3417_, 1);
v___y_3385_ = v___y_3396_;
v___y_3386_ = v___y_3397_;
v___y_3387_ = v___y_3398_;
v___y_3388_ = v___y_3400_;
v___y_3389_ = v___y_3399_;
v___y_3390_ = v___y_3401_;
v_a_3391_ = v_a_3442_;
goto v___jp_3384_;
}
}
else
{
lean_object* v_a_3443_; 
lean_dec_ref(v___y_3395_);
v_a_3443_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3406_, 1);
v___y_3385_ = v___y_3396_;
v___y_3386_ = v___y_3397_;
v___y_3387_ = v___y_3398_;
v___y_3388_ = v___y_3400_;
v___y_3389_ = v___y_3399_;
v___y_3390_ = v___y_3401_;
v_a_3391_ = v_a_3443_;
goto v___jp_3384_;
}
}
}
else
{
lean_object* v_a_3444_; 
lean_dec_ref(v___y_3395_);
v_a_3444_ = lean_ctor_get(v___y_3402_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v___y_3402_, 1);
v___y_3385_ = v___y_3396_;
v___y_3386_ = v___y_3397_;
v___y_3387_ = v___y_3398_;
v___y_3388_ = v___y_3400_;
v___y_3389_ = v___y_3399_;
v___y_3390_ = v___y_3401_;
v_a_3391_ = v_a_3444_;
goto v___jp_3384_;
}
}
v___jp_3445_:
{
lean_object* v___x_3452_; 
lean_inc_ref(v___x_3364_);
v___x_3452_ = l_Lean_Meta_mkDecide(v___x_3364_, v___y_3447_, v___y_3450_, v___y_3449_, v___y_3448_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; uint8_t v_transparency_3455_; uint8_t v___x_3456_; uint8_t v___x_3457_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___x_3454_ = l_Lean_Meta_Context_config(v___y_3447_);
v_transparency_3455_ = lean_ctor_get_uint8(v___x_3454_, 9);
lean_dec_ref(v___x_3454_);
v___x_3456_ = 1;
v___x_3457_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3455_, v___x_3456_);
if (v___x_3457_ == 0)
{
lean_object* v_keyedConfig_3458_; uint8_t v_trackZetaDelta_3459_; lean_object* v_zetaDeltaSet_3460_; lean_object* v_lctx_3461_; lean_object* v_localInstances_3462_; lean_object* v_defEqCtx_x3f_3463_; lean_object* v_synthPendingDepth_3464_; lean_object* v_customCanUnfoldPredicate_x3f_3465_; uint8_t v_univApprox_3466_; uint8_t v_inTypeClassResolution_3467_; uint8_t v_cacheInferType_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v_keyedConfig_3458_ = lean_ctor_get(v___y_3447_, 0);
v_trackZetaDelta_3459_ = lean_ctor_get_uint8(v___y_3447_, sizeof(void*)*7);
v_zetaDeltaSet_3460_ = lean_ctor_get(v___y_3447_, 1);
v_lctx_3461_ = lean_ctor_get(v___y_3447_, 2);
v_localInstances_3462_ = lean_ctor_get(v___y_3447_, 3);
v_defEqCtx_x3f_3463_ = lean_ctor_get(v___y_3447_, 4);
v_synthPendingDepth_3464_ = lean_ctor_get(v___y_3447_, 5);
v_customCanUnfoldPredicate_x3f_3465_ = lean_ctor_get(v___y_3447_, 6);
v_univApprox_3466_ = lean_ctor_get_uint8(v___y_3447_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3467_ = lean_ctor_get_uint8(v___y_3447_, sizeof(void*)*7 + 2);
v_cacheInferType_3468_ = lean_ctor_get_uint8(v___y_3447_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3458_);
v___x_3469_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3456_, v_keyedConfig_3458_);
lean_inc(v_customCanUnfoldPredicate_x3f_3465_);
lean_inc(v_synthPendingDepth_3464_);
lean_inc(v_defEqCtx_x3f_3463_);
lean_inc_ref(v_localInstances_3462_);
lean_inc_ref(v_lctx_3461_);
lean_inc(v_zetaDeltaSet_3460_);
v___x_3470_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v_zetaDeltaSet_3460_);
lean_ctor_set(v___x_3470_, 2, v_lctx_3461_);
lean_ctor_set(v___x_3470_, 3, v_localInstances_3462_);
lean_ctor_set(v___x_3470_, 4, v_defEqCtx_x3f_3463_);
lean_ctor_set(v___x_3470_, 5, v_synthPendingDepth_3464_);
lean_ctor_set(v___x_3470_, 6, v_customCanUnfoldPredicate_x3f_3465_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*7, v_trackZetaDelta_3459_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*7 + 1, v_univApprox_3466_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3467_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*7 + 3, v_cacheInferType_3468_);
lean_inc(v___y_3448_);
lean_inc_ref(v___y_3449_);
lean_inc(v___y_3450_);
lean_inc(v_a_3453_);
v___x_3471_ = lean_whnf(v_a_3453_, v___x_3470_, v___y_3450_, v___y_3449_, v___y_3448_);
v___y_3395_ = v_a_3453_;
v___y_3396_ = v___y_3446_;
v___y_3397_ = v___y_3447_;
v___y_3398_ = v___y_3448_;
v___y_3399_ = v___y_3449_;
v___y_3400_ = v___y_3450_;
v___y_3401_ = v___y_3451_;
v___y_3402_ = v___x_3471_;
goto v___jp_3394_;
}
else
{
lean_object* v___x_3472_; 
lean_inc(v___y_3448_);
lean_inc_ref(v___y_3449_);
lean_inc(v___y_3450_);
lean_inc_ref(v___y_3447_);
lean_inc(v_a_3453_);
v___x_3472_ = lean_whnf(v_a_3453_, v___y_3447_, v___y_3450_, v___y_3449_, v___y_3448_);
v___y_3395_ = v_a_3453_;
v___y_3396_ = v___y_3446_;
v___y_3397_ = v___y_3447_;
v___y_3398_ = v___y_3448_;
v___y_3399_ = v___y_3449_;
v___y_3400_ = v___y_3450_;
v___y_3401_ = v___y_3451_;
v___y_3402_ = v___x_3472_;
goto v___jp_3394_;
}
}
else
{
lean_object* v_a_3473_; 
v_a_3473_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3452_, 1);
v___y_3385_ = v___y_3446_;
v___y_3386_ = v___y_3447_;
v___y_3387_ = v___y_3448_;
v___y_3388_ = v___y_3450_;
v___y_3389_ = v___y_3449_;
v___y_3390_ = v___y_3451_;
v_a_3391_ = v_a_3473_;
goto v___jp_3384_;
}
}
v___jp_3474_:
{
if (v___y_3481_ == 0)
{
v___y_3366_ = v___y_3475_;
v___y_3367_ = v___y_3480_;
v___y_3368_ = v___y_3476_;
v___y_3369_ = v___y_3479_;
v___y_3370_ = v___y_3478_;
v___y_3371_ = v___y_3477_;
goto v___jp_3365_;
}
else
{
v___y_3446_ = v___y_3475_;
v___y_3447_ = v___y_3476_;
v___y_3448_ = v___y_3477_;
v___y_3449_ = v___y_3478_;
v___y_3450_ = v___y_3479_;
v___y_3451_ = v___y_3480_;
goto v___jp_3445_;
}
}
v___jp_3482_:
{
if (v___y_3490_ == 0)
{
lean_dec_ref(v___y_3483_);
v___y_3475_ = v___y_3484_;
v___y_3476_ = v___y_3485_;
v___y_3477_ = v___y_3486_;
v___y_3478_ = v___y_3488_;
v___y_3479_ = v___y_3487_;
v___y_3480_ = v___y_3489_;
v___y_3481_ = v___x_3319_;
goto v___jp_3474_;
}
else
{
uint8_t v___x_3491_; 
v___x_3491_ = l_Lean_Expr_hasFVar(v___y_3483_);
lean_dec_ref(v___y_3483_);
if (v___x_3491_ == 0)
{
v___y_3446_ = v___y_3484_;
v___y_3447_ = v___y_3485_;
v___y_3448_ = v___y_3486_;
v___y_3449_ = v___y_3488_;
v___y_3450_ = v___y_3487_;
v___y_3451_ = v___y_3489_;
goto v___jp_3445_;
}
else
{
v___y_3475_ = v___y_3484_;
v___y_3476_ = v___y_3485_;
v___y_3477_ = v___y_3486_;
v___y_3478_ = v___y_3488_;
v___y_3479_ = v___y_3487_;
v___y_3480_ = v___y_3489_;
v___y_3481_ = v___x_3319_;
goto v___jp_3474_;
}
}
}
v___jp_3492_:
{
lean_object* v___x_3500_; 
lean_inc_ref(v___x_3364_);
v___x_3500_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3364_, v___y_3497_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; uint8_t v___x_3502_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = l_Lean_Expr_hasMVar(v_a_3501_);
if (v___x_3502_ == 0)
{
v___y_3483_ = v_a_3501_;
v___y_3484_ = v___y_3493_;
v___y_3485_ = v___y_3494_;
v___y_3486_ = v___y_3495_;
v___y_3487_ = v___y_3497_;
v___y_3488_ = v___y_3496_;
v___y_3489_ = v___y_3498_;
v___y_3490_ = v___y_3499_;
goto v___jp_3482_;
}
else
{
v___y_3483_ = v_a_3501_;
v___y_3484_ = v___y_3493_;
v___y_3485_ = v___y_3494_;
v___y_3486_ = v___y_3495_;
v___y_3487_ = v___y_3497_;
v___y_3488_ = v___y_3496_;
v___y_3489_ = v___y_3498_;
v___y_3490_ = v___x_3319_;
goto v___jp_3482_;
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref(v___x_3364_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3503_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3500_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3500_);
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
v___jp_3511_:
{
if (v___y_3518_ == 0)
{
v___y_3366_ = v___y_3512_;
v___y_3367_ = v___y_3517_;
v___y_3368_ = v___y_3513_;
v___y_3369_ = v___y_3516_;
v___y_3370_ = v___y_3515_;
v___y_3371_ = v___y_3514_;
goto v___jp_3365_;
}
else
{
v___y_3493_ = v___y_3512_;
v___y_3494_ = v___y_3513_;
v___y_3495_ = v___y_3514_;
v___y_3496_ = v___y_3515_;
v___y_3497_ = v___y_3516_;
v___y_3498_ = v___y_3517_;
v___y_3499_ = v___y_3518_;
goto v___jp_3492_;
}
}
v___jp_3519_:
{
uint8_t v_useDecide_3526_; 
v_useDecide_3526_ = lean_ctor_get_uint8(v_config_3212_, sizeof(void*)*1);
if (v_useDecide_3526_ == 0)
{
v___y_3512_ = v_isHEq_3521_;
v___y_3513_ = v___y_3522_;
v___y_3514_ = v___y_3525_;
v___y_3515_ = v___y_3524_;
v___y_3516_ = v___y_3523_;
v___y_3517_ = v___y_3520_;
v___y_3518_ = v___x_3319_;
goto v___jp_3511_;
}
else
{
uint8_t v___x_3527_; 
v___x_3527_ = l_Lean_Expr_hasFVar(v___x_3364_);
if (v___x_3527_ == 0)
{
v___y_3493_ = v_isHEq_3521_;
v___y_3494_ = v___y_3522_;
v___y_3495_ = v___y_3525_;
v___y_3496_ = v___y_3524_;
v___y_3497_ = v___y_3523_;
v___y_3498_ = v___y_3520_;
v___y_3499_ = v_useDecide_3526_;
goto v___jp_3492_;
}
else
{
v___y_3512_ = v_isHEq_3521_;
v___y_3513_ = v___y_3522_;
v___y_3514_ = v___y_3525_;
v___y_3515_ = v___y_3524_;
v___y_3516_ = v___y_3523_;
v___y_3517_ = v___y_3520_;
v___y_3518_ = v___x_3319_;
goto v___jp_3511_;
}
}
}
v___jp_3528_:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_Meta_isExprDefEq(v___y_3534_, v___y_3532_, v___y_3533_, v___y_3535_, v___y_3531_, v___y_3530_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; uint8_t v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = lean_unbox(v_a_3537_);
lean_dec(v_a_3537_);
if (v___x_3538_ == 0)
{
v___y_3520_ = v___y_3529_;
v_isHEq_3521_ = v___x_3223_;
v___y_3522_ = v___y_3533_;
v___y_3523_ = v___y_3535_;
v___y_3524_ = v___y_3531_;
v___y_3525_ = v___y_3530_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3539_; 
lean_dec_ref(v___x_3364_);
lean_dec_ref(v_config_3212_);
lean_inc(v_mvarId_3213_);
v___x_3539_ = l_Lean_MVarId_getType(v_mvarId_3213_, v___y_3533_, v___y_3535_, v___y_3531_, v___y_3530_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3539_, 1);
v___x_3541_ = l_Lean_LocalDecl_toExpr(v_val_3244_);
v___x_3542_ = l_Lean_Meta_mkEqOfHEq(v___x_3541_, v___x_3223_, v___y_3533_, v___y_3535_, v___y_3531_, v___y_3530_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3544_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3542_, 1);
v___x_3544_ = l_Lean_Meta_mkNoConfusion(v_a_3540_, v_a_3543_, v___y_3533_, v___y_3535_, v___y_3531_, v___y_3530_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3546_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v___x_3546_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3213_, v_a_3545_, v___y_3535_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec_ref_known(v___x_3546_, 1);
v___x_3547_ = lean_box(v___x_3223_);
v___x_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v___x_3248_);
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
v_a_3230_ = v___x_3550_;
goto v___jp_3229_;
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
v_a_3551_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3546_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3546_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3559_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3544_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3544_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_a_3540_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3567_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3542_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3542_);
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
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3575_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3539_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3539_);
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
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec_ref(v___x_3364_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3583_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3536_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3536_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
v___jp_3591_:
{
lean_object* v___x_3597_; 
lean_inc_ref(v___x_3364_);
v___x_3597_ = l_Lean_Meta_matchHEq_x3f(v___x_3364_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3597_, 1);
if (lean_obj_tag(v_a_3598_) == 1)
{
lean_object* v_val_3599_; lean_object* v_snd_3600_; lean_object* v_snd_3601_; lean_object* v_fst_3602_; lean_object* v_fst_3603_; lean_object* v_fst_3604_; lean_object* v_snd_3605_; lean_object* v___x_3606_; 
v_val_3599_ = lean_ctor_get(v_a_3598_, 0);
lean_inc(v_val_3599_);
lean_dec_ref_known(v_a_3598_, 1);
v_snd_3600_ = lean_ctor_get(v_val_3599_, 1);
lean_inc(v_snd_3600_);
v_snd_3601_ = lean_ctor_get(v_snd_3600_, 1);
lean_inc(v_snd_3601_);
v_fst_3602_ = lean_ctor_get(v_val_3599_, 0);
lean_inc(v_fst_3602_);
lean_dec(v_val_3599_);
v_fst_3603_ = lean_ctor_get(v_snd_3600_, 0);
lean_inc(v_fst_3603_);
lean_dec(v_snd_3600_);
v_fst_3604_ = lean_ctor_get(v_snd_3601_, 0);
lean_inc(v_fst_3604_);
v_snd_3605_ = lean_ctor_get(v_snd_3601_, 1);
lean_inc(v_snd_3605_);
lean_dec(v_snd_3601_);
v___x_3606_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3603_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
if (lean_obj_tag(v_a_3607_) == 1)
{
lean_object* v_val_3608_; lean_object* v___x_3609_; 
v_val_3608_ = lean_ctor_get(v_a_3607_, 0);
lean_inc(v_val_3608_);
lean_dec_ref_known(v_a_3607_, 1);
v___x_3609_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3605_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
if (lean_obj_tag(v_a_3610_) == 1)
{
lean_object* v_toConstantVal_3611_; lean_object* v_val_3612_; lean_object* v_toConstantVal_3613_; lean_object* v_name_3614_; lean_object* v_name_3615_; uint8_t v___x_3616_; 
v_toConstantVal_3611_ = lean_ctor_get(v_val_3608_, 0);
lean_inc_ref(v_toConstantVal_3611_);
lean_dec(v_val_3608_);
v_val_3612_ = lean_ctor_get(v_a_3610_, 0);
lean_inc(v_val_3612_);
lean_dec_ref_known(v_a_3610_, 1);
v_toConstantVal_3613_ = lean_ctor_get(v_val_3612_, 0);
lean_inc_ref(v_toConstantVal_3613_);
lean_dec(v_val_3612_);
v_name_3614_ = lean_ctor_get(v_toConstantVal_3611_, 0);
lean_inc(v_name_3614_);
lean_dec_ref(v_toConstantVal_3611_);
v_name_3615_ = lean_ctor_get(v_toConstantVal_3613_, 0);
lean_inc(v_name_3615_);
lean_dec_ref(v_toConstantVal_3613_);
v___x_3616_ = lean_name_eq(v_name_3614_, v_name_3615_);
lean_dec(v_name_3615_);
lean_dec(v_name_3614_);
if (v___x_3616_ == 0)
{
v___y_3529_ = v_isEq_3592_;
v___y_3530_ = v___y_3596_;
v___y_3531_ = v___y_3595_;
v___y_3532_ = v_fst_3604_;
v___y_3533_ = v___y_3593_;
v___y_3534_ = v_fst_3602_;
v___y_3535_ = v___y_3594_;
goto v___jp_3528_;
}
else
{
if (v___x_3319_ == 0)
{
lean_dec(v_fst_3604_);
lean_dec(v_fst_3602_);
v___y_3520_ = v_isEq_3592_;
v_isHEq_3521_ = v___x_3223_;
v___y_3522_ = v___y_3593_;
v___y_3523_ = v___y_3594_;
v___y_3524_ = v___y_3595_;
v___y_3525_ = v___y_3596_;
goto v___jp_3519_;
}
else
{
v___y_3529_ = v_isEq_3592_;
v___y_3530_ = v___y_3596_;
v___y_3531_ = v___y_3595_;
v___y_3532_ = v_fst_3604_;
v___y_3533_ = v___y_3593_;
v___y_3534_ = v_fst_3602_;
v___y_3535_ = v___y_3594_;
goto v___jp_3528_;
}
}
}
else
{
lean_dec(v_a_3610_);
lean_dec(v_val_3608_);
lean_dec(v_fst_3604_);
lean_dec(v_fst_3602_);
v___y_3520_ = v_isEq_3592_;
v_isHEq_3521_ = v___x_3223_;
v___y_3522_ = v___y_3593_;
v___y_3523_ = v___y_3594_;
v___y_3524_ = v___y_3595_;
v___y_3525_ = v___y_3596_;
goto v___jp_3519_;
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v_val_3608_);
lean_dec(v_fst_3604_);
lean_dec(v_fst_3602_);
lean_dec_ref(v___x_3364_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3617_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3609_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3609_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_dec(v_a_3607_);
lean_dec(v_snd_3605_);
lean_dec(v_fst_3604_);
lean_dec(v_fst_3602_);
v___y_3520_ = v_isEq_3592_;
v_isHEq_3521_ = v___x_3223_;
v___y_3522_ = v___y_3593_;
v___y_3523_ = v___y_3594_;
v___y_3524_ = v___y_3595_;
v___y_3525_ = v___y_3596_;
goto v___jp_3519_;
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v_snd_3605_);
lean_dec(v_fst_3604_);
lean_dec(v_fst_3602_);
lean_dec_ref(v___x_3364_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3625_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3606_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3606_);
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
lean_dec(v_a_3598_);
v___y_3520_ = v_isEq_3592_;
v_isHEq_3521_ = v___x_3319_;
v___y_3522_ = v___y_3593_;
v___y_3523_ = v___y_3594_;
v___y_3524_ = v___y_3595_;
v___y_3525_ = v___y_3596_;
goto v___jp_3519_;
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec_ref(v___x_3364_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3633_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3597_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3597_);
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
v___jp_3641_:
{
lean_object* v___x_3646_; 
lean_inc_ref(v___x_3364_);
v___x_3646_ = l_Lean_Meta_matchEq_x3f(v___x_3364_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3646_, 1);
if (lean_obj_tag(v_a_3647_) == 1)
{
lean_object* v_val_3648_; lean_object* v_snd_3649_; lean_object* v_fst_3650_; lean_object* v_snd_3651_; lean_object* v___x_3652_; 
v_val_3648_ = lean_ctor_get(v_a_3647_, 0);
lean_inc(v_val_3648_);
lean_dec_ref_known(v_a_3647_, 1);
v_snd_3649_ = lean_ctor_get(v_val_3648_, 1);
lean_inc(v_snd_3649_);
lean_dec(v_val_3648_);
v_fst_3650_ = lean_ctor_get(v_snd_3649_, 0);
lean_inc(v_fst_3650_);
v_snd_3651_ = lean_ctor_get(v_snd_3649_, 1);
lean_inc(v_snd_3651_);
lean_dec(v_snd_3649_);
v___x_3652_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3650_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3652_, 1);
if (lean_obj_tag(v_a_3653_) == 1)
{
lean_object* v_val_3654_; lean_object* v___x_3655_; 
v_val_3654_ = lean_ctor_get(v_a_3653_, 0);
lean_inc(v_val_3654_);
lean_dec_ref_known(v_a_3653_, 1);
v___x_3655_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3651_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
if (lean_obj_tag(v_a_3656_) == 1)
{
lean_object* v_toConstantVal_3657_; lean_object* v_val_3658_; lean_object* v_toConstantVal_3659_; lean_object* v_name_3660_; lean_object* v_name_3661_; uint8_t v___x_3662_; 
v_toConstantVal_3657_ = lean_ctor_get(v_val_3654_, 0);
lean_inc_ref(v_toConstantVal_3657_);
lean_dec(v_val_3654_);
v_val_3658_ = lean_ctor_get(v_a_3656_, 0);
lean_inc(v_val_3658_);
lean_dec_ref_known(v_a_3656_, 1);
v_toConstantVal_3659_ = lean_ctor_get(v_val_3658_, 0);
lean_inc_ref(v_toConstantVal_3659_);
lean_dec(v_val_3658_);
v_name_3660_ = lean_ctor_get(v_toConstantVal_3657_, 0);
lean_inc(v_name_3660_);
lean_dec_ref(v_toConstantVal_3657_);
v_name_3661_ = lean_ctor_get(v_toConstantVal_3659_, 0);
lean_inc(v_name_3661_);
lean_dec_ref(v_toConstantVal_3659_);
v___x_3662_ = lean_name_eq(v_name_3660_, v_name_3661_);
lean_dec(v_name_3661_);
lean_dec(v_name_3660_);
if (v___x_3662_ == 0)
{
lean_dec_ref(v___x_3364_);
lean_dec_ref(v_config_3212_);
v___y_3250_ = v___y_3645_;
v___y_3251_ = v___y_3644_;
v___y_3252_ = v___y_3642_;
v___y_3253_ = v___y_3643_;
goto v___jp_3249_;
}
else
{
if (v___x_3319_ == 0)
{
lean_del_object(v___x_3246_);
v_isEq_3592_ = v___x_3223_;
v___y_3593_ = v___y_3642_;
v___y_3594_ = v___y_3643_;
v___y_3595_ = v___y_3644_;
v___y_3596_ = v___y_3645_;
goto v___jp_3591_;
}
else
{
lean_dec_ref(v___x_3364_);
lean_dec_ref(v_config_3212_);
v___y_3250_ = v___y_3645_;
v___y_3251_ = v___y_3644_;
v___y_3252_ = v___y_3642_;
v___y_3253_ = v___y_3643_;
goto v___jp_3249_;
}
}
}
else
{
lean_dec(v_a_3656_);
lean_dec(v_val_3654_);
lean_del_object(v___x_3246_);
v_isEq_3592_ = v___x_3223_;
v___y_3593_ = v___y_3642_;
v___y_3594_ = v___y_3643_;
v___y_3595_ = v___y_3644_;
v___y_3596_ = v___y_3645_;
goto v___jp_3591_;
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec(v_val_3654_);
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3663_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3655_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3655_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
else
{
lean_dec(v_a_3653_);
lean_dec(v_snd_3651_);
lean_del_object(v___x_3246_);
v_isEq_3592_ = v___x_3223_;
v___y_3593_ = v___y_3642_;
v___y_3594_ = v___y_3643_;
v___y_3595_ = v___y_3644_;
v___y_3596_ = v___y_3645_;
goto v___jp_3591_;
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec(v_snd_3651_);
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3671_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3652_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3652_);
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
lean_dec(v_a_3647_);
lean_del_object(v___x_3246_);
v_isEq_3592_ = v___x_3319_;
v___y_3593_ = v___y_3642_;
v___y_3594_ = v___y_3643_;
v___y_3595_ = v___y_3644_;
v___y_3596_ = v___y_3645_;
goto v___jp_3591_;
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3679_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3646_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3646_);
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
v___jp_3687_:
{
lean_object* v___x_3692_; 
lean_inc_ref(v___x_3364_);
v___x_3692_ = l_Lean_refutableHasNotBit_x3f(v___x_3364_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
if (lean_obj_tag(v_a_3693_) == 1)
{
lean_object* v_val_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3734_; 
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec_ref(v_config_3212_);
v_val_3694_ = lean_ctor_get(v_a_3693_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_a_3693_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3696_ = v_a_3693_;
v_isShared_3697_ = v_isSharedCheck_3734_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_val_3694_);
lean_dec(v_a_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3734_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3698_; 
lean_inc(v_mvarId_3213_);
v___x_3698_ = l_Lean_MVarId_getType(v_mvarId_3213_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v___x_3700_ = l_Lean_LocalDecl_toExpr(v_val_3244_);
v___x_3701_ = l_Lean_Meta_mkAbsurd(v_a_3699_, v_val_3694_, v___x_3700_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3703_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref_known(v___x_3701_, 1);
v___x_3703_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3213_, v_a_3702_, v___y_3689_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
lean_dec_ref_known(v___x_3703_, 1);
v___x_3704_ = lean_box(v___x_3223_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3704_);
v___x_3706_ = v___x_3696_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
lean_ctor_set(v___x_3707_, 1, v___x_3248_);
v___x_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
v_a_3230_ = v___x_3708_;
goto v___jp_3229_;
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_del_object(v___x_3696_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
v_a_3710_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3703_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3703_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_del_object(v___x_3696_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3718_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3701_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3701_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_del_object(v___x_3696_);
lean_dec(v_val_3694_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3726_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3698_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3698_);
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
}
else
{
lean_object* v___x_3735_; 
lean_dec(v_a_3693_);
lean_inc_ref(v___x_3364_);
v___x_3735_ = l_Lean_Meta_matchNe_x3f(v___x_3364_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
if (lean_obj_tag(v_a_3736_) == 1)
{
lean_object* v_val_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3807_; 
v_val_3737_ = lean_ctor_get(v_a_3736_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_a_3736_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3739_ = v_a_3736_;
v_isShared_3740_ = v_isSharedCheck_3807_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_val_3737_);
lean_dec(v_a_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3807_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v_snd_3741_; lean_object* v_fst_3742_; lean_object* v_snd_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3806_; 
v_snd_3741_ = lean_ctor_get(v_val_3737_, 1);
lean_inc(v_snd_3741_);
lean_dec(v_val_3737_);
v_fst_3742_ = lean_ctor_get(v_snd_3741_, 0);
v_snd_3743_ = lean_ctor_get(v_snd_3741_, 1);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_snd_3741_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3745_ = v_snd_3741_;
v_isShared_3746_ = v_isSharedCheck_3806_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_snd_3743_);
lean_inc(v_fst_3742_);
lean_dec(v_snd_3741_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3806_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3747_; 
lean_inc(v_fst_3742_);
v___x_3747_ = l_Lean_Meta_isExprDefEq(v_fst_3742_, v_snd_3743_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; uint8_t v___x_3749_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_a_3748_);
lean_dec_ref_known(v___x_3747_, 1);
v___x_3749_ = lean_unbox(v_a_3748_);
lean_dec(v_a_3748_);
if (v___x_3749_ == 0)
{
lean_del_object(v___x_3745_);
lean_dec(v_fst_3742_);
lean_del_object(v___x_3739_);
v___y_3642_ = v___y_3688_;
v___y_3643_ = v___y_3689_;
v___y_3644_ = v___y_3690_;
v___y_3645_ = v___y_3691_;
goto v___jp_3641_;
}
else
{
lean_object* v___x_3750_; 
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec_ref(v_config_3212_);
lean_inc(v_mvarId_3213_);
v___x_3750_ = l_Lean_MVarId_getType(v_mvarId_3213_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3752_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3750_, 1);
v___x_3752_ = l_Lean_Meta_mkEqRefl(v_fst_3742_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3752_, 1);
v___x_3754_ = l_Lean_LocalDecl_toExpr(v_val_3244_);
v___x_3755_ = l_Lean_Meta_mkAbsurd(v_a_3751_, v_a_3753_, v___x_3754_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3757_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v___x_3757_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3213_, v_a_3756_, v___y_3689_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v___x_3758_; lean_object* v___x_3760_; 
lean_dec_ref_known(v___x_3757_, 1);
v___x_3758_ = lean_box(v___x_3223_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3758_);
v___x_3760_ = v___x_3739_;
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
lean_object* v___x_3762_; 
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 1, v___x_3248_);
lean_ctor_set(v___x_3745_, 0, v___x_3760_);
v___x_3762_ = v___x_3745_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v___x_3248_);
v___x_3762_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
v_a_3230_ = v___x_3763_;
goto v___jp_3229_;
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_del_object(v___x_3745_);
lean_del_object(v___x_3739_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
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
lean_del_object(v___x_3745_);
lean_del_object(v___x_3739_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
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
lean_dec(v_a_3751_);
lean_del_object(v___x_3745_);
lean_del_object(v___x_3739_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3782_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3752_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3752_);
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
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_del_object(v___x_3745_);
lean_dec(v_fst_3742_);
lean_del_object(v___x_3739_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3790_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3750_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3750_);
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
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_del_object(v___x_3745_);
lean_dec(v_fst_3742_);
lean_del_object(v___x_3739_);
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3798_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3747_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3747_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3736_);
v___y_3642_ = v___y_3688_;
v___y_3643_ = v___y_3689_;
v___y_3644_ = v___y_3690_;
v___y_3645_ = v___y_3691_;
goto v___jp_3641_;
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3808_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3735_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3735_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec_ref(v___x_3364_);
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3816_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3692_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3692_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
else
{
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
v_a_3238_ = v___x_3290_;
goto v___jp_3237_;
}
v___jp_3249_:
{
lean_object* v___x_3254_; 
lean_inc(v_mvarId_3213_);
v___x_3254_ = l_Lean_MVarId_getType(v_mvarId_3213_, v___y_3252_, v___y_3253_, v___y_3251_, v___y_3250_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___x_3254_, 1);
v___x_3256_ = l_Lean_LocalDecl_toExpr(v_val_3244_);
v___x_3257_ = l_Lean_Meta_mkNoConfusion(v_a_3255_, v___x_3256_, v___y_3252_, v___y_3253_, v___y_3251_, v___y_3250_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3259_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___x_3257_, 1);
v___x_3259_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3213_, v_a_3258_, v___y_3253_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
lean_dec_ref_known(v___x_3259_, 1);
v___x_3260_ = lean_box(v___x_3223_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v___x_3260_);
v___x_3262_ = v___x_3246_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
lean_ctor_set(v___x_3263_, 1, v___x_3248_);
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
v_a_3230_ = v___x_3264_;
goto v___jp_3229_;
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_del_object(v___x_3246_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
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
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_del_object(v___x_3246_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3274_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3257_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3257_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
v_a_3282_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3254_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3254_);
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
v___jp_3291_:
{
lean_object* v_searchFuel_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_searchFuel_3296_ = lean_ctor_get(v_config_3212_, 0);
v___x_3297_ = l_Lean_LocalDecl_fvarId(v_val_3244_);
lean_dec(v_val_3244_);
lean_inc(v_searchFuel_3296_);
lean_inc(v_mvarId_3213_);
v___x_3298_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3213_, v___x_3297_, v_searchFuel_3296_, v___y_3294_, v___y_3295_, v___y_3293_, v___y_3292_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; uint8_t v___x_3300_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3298_, 1);
v___x_3300_ = lean_unbox(v_a_3299_);
lean_dec(v_a_3299_);
if (v___x_3300_ == 0)
{
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
v_a_3238_ = v___x_3290_;
goto v___jp_3237_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v___x_3301_ = lean_box(v___x_3223_);
v___x_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v___x_3248_);
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
v_a_3230_ = v___x_3304_;
goto v___jp_3229_;
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3305_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3298_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3298_);
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
v___jp_3313_:
{
if (v___y_3318_ == 0)
{
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
v_a_3238_ = v___x_3290_;
goto v___jp_3237_;
}
else
{
v___y_3292_ = v___y_3314_;
v___y_3293_ = v___y_3316_;
v___y_3294_ = v___y_3315_;
v___y_3295_ = v___y_3317_;
goto v___jp_3291_;
}
}
v___jp_3320_:
{
if (v___y_3321_ == 0)
{
v___y_3292_ = v___y_3322_;
v___y_3293_ = v___y_3324_;
v___y_3294_ = v___y_3323_;
v___y_3295_ = v___y_3325_;
goto v___jp_3291_;
}
else
{
v___y_3314_ = v___y_3322_;
v___y_3315_ = v___y_3323_;
v___y_3316_ = v___y_3324_;
v___y_3317_ = v___y_3325_;
v___y_3318_ = v___x_3319_;
goto v___jp_3313_;
}
}
v___jp_3326_:
{
if (v___y_3332_ == 0)
{
v___y_3314_ = v___y_3328_;
v___y_3315_ = v___y_3330_;
v___y_3316_ = v___y_3329_;
v___y_3317_ = v___y_3331_;
v___y_3318_ = v___x_3319_;
goto v___jp_3313_;
}
else
{
v___y_3321_ = v___y_3327_;
v___y_3322_ = v___y_3328_;
v___y_3323_ = v___y_3330_;
v___y_3324_ = v___y_3329_;
v___y_3325_ = v___y_3331_;
goto v___jp_3320_;
}
}
v___jp_3333_:
{
uint8_t v_emptyType_3340_; 
v_emptyType_3340_ = lean_ctor_get_uint8(v_config_3212_, sizeof(void*)*1 + 1);
if (v_emptyType_3340_ == 0)
{
v___y_3327_ = v___y_3334_;
v___y_3328_ = v___y_3339_;
v___y_3329_ = v___y_3338_;
v___y_3330_ = v___y_3336_;
v___y_3331_ = v___y_3337_;
v___y_3332_ = v___x_3319_;
goto v___jp_3326_;
}
else
{
if (v___y_3335_ == 0)
{
v___y_3321_ = v___y_3334_;
v___y_3322_ = v___y_3339_;
v___y_3323_ = v___y_3336_;
v___y_3324_ = v___y_3338_;
v___y_3325_ = v___y_3337_;
goto v___jp_3320_;
}
else
{
v___y_3327_ = v___y_3334_;
v___y_3328_ = v___y_3339_;
v___y_3329_ = v___y_3338_;
v___y_3330_ = v___y_3336_;
v___y_3331_ = v___y_3337_;
v___y_3332_ = v___x_3319_;
goto v___jp_3326_;
}
}
}
v___jp_3341_:
{
if (v___y_3348_ == 0)
{
v___y_3334_ = v___y_3342_;
v___y_3335_ = v___y_3343_;
v___y_3336_ = v___y_3347_;
v___y_3337_ = v___y_3344_;
v___y_3338_ = v___y_3345_;
v___y_3339_ = v___y_3346_;
goto v___jp_3333_;
}
else
{
lean_object* v___x_3349_; 
lean_inc(v_val_3244_);
lean_inc(v_mvarId_3213_);
v___x_3349_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3213_, v_val_3244_, v___y_3347_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; uint8_t v___x_3351_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
v___x_3351_ = lean_unbox(v_a_3350_);
lean_dec(v_a_3350_);
if (v___x_3351_ == 0)
{
v___y_3334_ = v___y_3342_;
v___y_3335_ = v___y_3343_;
v___y_3336_ = v___y_3347_;
v___y_3337_ = v___y_3344_;
v___y_3338_ = v___y_3345_;
v___y_3339_ = v___y_3346_;
goto v___jp_3333_;
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec(v_val_3244_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v___x_3352_ = lean_box(v___x_3223_);
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
lean_ctor_set(v___x_3354_, 1, v___x_3248_);
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
v_a_3230_ = v___x_3355_;
goto v___jp_3229_;
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec(v_val_3244_);
lean_del_object(v___x_3227_);
lean_dec(v_snd_3225_);
lean_dec(v_mvarId_3213_);
lean_dec_ref(v_config_3212_);
v_a_3356_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3349_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3349_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
}
}
v___jp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_a_3230_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3231_);
v___x_3233_ = v___x_3227_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3231_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_snd_3225_);
v___x_3233_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
return v___x_3234_;
}
}
v___jp_3237_:
{
lean_object* v___x_3239_; size_t v___x_3240_; size_t v___x_3241_; 
v___x_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3236_);
lean_ctor_set(v___x_3239_, 1, v_a_3238_);
v___x_3240_ = ((size_t)1ULL);
v___x_3241_ = lean_usize_add(v_i_3216_, v___x_3240_);
v_i_3216_ = v___x_3241_;
v_b_3217_ = v___x_3239_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_3212_ = stack[0].m_obj;
lean_object* v_mvarId_3213_ = stack[1].m_obj;
lean_object* v_as_3214_ = stack[2].m_obj;
size_t v_sz_3215_ = stack[3].m_num;
size_t v_i_3216_ = stack[4].m_num;
lean_object* v_b_3217_ = stack[5].m_obj;
lean_object* v___y_3218_ = stack[6].m_obj;
lean_object* v___y_3219_ = stack[7].m_obj;
lean_object* v___y_3220_ = stack[8].m_obj;
lean_object* v___y_3221_ = stack[9].m_obj;
lean_object* v_res_3897_;
v_res_3897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3212_, v_mvarId_3213_, v_as_3214_, v_sz_3215_, v_i_3216_, v_b_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
stack->m_obj
 = v_res_3897_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3898_, lean_object* v_mvarId_3899_, lean_object* v_as_3900_, lean_object* v_sz_3901_, lean_object* v_i_3902_, lean_object* v_b_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
size_t v_sz_boxed_3909_; size_t v_i_boxed_3910_; lean_object* v_res_3911_; 
v_sz_boxed_3909_ = lean_unbox_usize(v_sz_3901_);
lean_dec(v_sz_3901_);
v_i_boxed_3910_ = lean_unbox_usize(v_i_3902_);
lean_dec(v_i_3902_);
v_res_3911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3898_, v_mvarId_3899_, v_as_3900_, v_sz_boxed_3909_, v_i_boxed_3910_, v_b_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec_ref(v_as_3900_);
return v_res_3911_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3912_, lean_object* v_mvarId_3913_, lean_object* v_as_3914_, size_t v_sz_3915_, size_t v_i_3916_, lean_object* v_b_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
uint8_t v___x_3923_; 
v___x_3923_ = lean_usize_dec_lt(v_i_3916_, v_sz_3915_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; 
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v_b_3917_);
return v___x_3924_;
}
else
{
lean_object* v_snd_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_4595_; 
v_snd_3925_ = lean_ctor_get(v_b_3917_, 1);
v_isSharedCheck_4595_ = !lean_is_exclusive(v_b_3917_);
if (v_isSharedCheck_4595_ == 0)
{
lean_object* v_unused_4596_; 
v_unused_4596_ = lean_ctor_get(v_b_3917_, 0);
lean_dec(v_unused_4596_);
v___x_3927_ = v_b_3917_;
v_isShared_3928_ = v_isSharedCheck_4595_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_snd_3925_);
lean_dec(v_b_3917_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_4595_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v_a_3930_; lean_object* v___x_3936_; lean_object* v_a_3938_; lean_object* v_a_3943_; 
v___x_3936_ = lean_box(0);
v_a_3943_ = lean_array_uget(v_as_3914_, v_i_3916_);
if (lean_obj_tag(v_a_3943_) == 0)
{
lean_del_object(v___x_3927_);
v_a_3938_ = v_snd_3925_;
goto v___jp_3937_;
}
else
{
lean_object* v_val_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_4594_; 
v_val_3944_ = lean_ctor_get(v_a_3943_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_a_3943_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_3946_ = v_a_3943_;
v_isShared_3947_ = v_isSharedCheck_4594_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_val_3944_);
lean_dec(v_a_3943_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_4594_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3948_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___x_3990_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; uint8_t v___y_4018_; uint8_t v___x_4019_; lean_object* v___y_4021_; lean_object* v___y_4022_; uint8_t v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4027_; lean_object* v___y_4028_; uint8_t v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; uint8_t v___y_4032_; uint8_t v___y_4034_; uint8_t v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; uint8_t v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; uint8_t v___y_4046_; lean_object* v___y_4047_; uint8_t v___y_4048_; 
v___x_3948_ = lean_box(0);
v___x_3990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_4019_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3944_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4064_; uint8_t v___y_4066_; uint8_t v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4075_; uint8_t v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; uint8_t v___y_4080_; lean_object* v___y_4081_; uint8_t v___y_4082_; lean_object* v___y_4085_; lean_object* v___y_4086_; uint8_t v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; uint8_t v___y_4090_; lean_object* v_a_4091_; lean_object* v___y_4095_; lean_object* v___y_4096_; uint8_t v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; uint8_t v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4146_; uint8_t v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; uint8_t v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4175_; uint8_t v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; uint8_t v___y_4179_; lean_object* v___y_4180_; uint8_t v___y_4181_; lean_object* v___y_4183_; lean_object* v___y_4184_; uint8_t v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; uint8_t v___y_4189_; uint8_t v___y_4190_; lean_object* v___y_4193_; lean_object* v___y_4194_; uint8_t v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; uint8_t v___y_4198_; uint8_t v___y_4199_; lean_object* v___y_4212_; uint8_t v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; uint8_t v___y_4216_; lean_object* v___y_4217_; uint8_t v___y_4218_; uint8_t v___y_4220_; uint8_t v_isHEq_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; uint8_t v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; uint8_t v_isEq_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___x_4524_; 
v___x_4064_ = l_Lean_LocalDecl_type(v_val_3944_);
lean_inc_ref(v___x_4064_);
v___x_4524_ = l_Lean_Meta_matchNot_x3f(v___x_4064_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
lean_dec_ref_known(v___x_4524_, 1);
if (lean_obj_tag(v_a_4525_) == 1)
{
lean_object* v_val_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4585_; 
v_val_4526_ = lean_ctor_get(v_a_4525_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_a_4525_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4528_ = v_a_4525_;
v_isShared_4529_ = v_isSharedCheck_4585_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_val_4526_);
lean_dec(v_a_4525_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4585_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4530_; 
v___x_4530_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4526_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; 
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc(v_a_4531_);
lean_dec_ref_known(v___x_4530_, 1);
if (lean_obj_tag(v_a_4531_) == 1)
{
lean_object* v_val_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4576_; 
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec_ref(v_config_3912_);
v_val_4532_ = lean_ctor_get(v_a_4531_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v_a_4531_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4534_ = v_a_4531_;
v_isShared_4535_ = v_isSharedCheck_4576_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_val_4532_);
lean_dec(v_a_4531_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4576_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4536_; 
lean_inc(v_mvarId_3913_);
v___x_4536_ = l_Lean_MVarId_getType(v_mvarId_3913_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4536_, 1);
v___x_4538_ = l_Lean_LocalDecl_toExpr(v_val_3944_);
v___x_4539_ = l_Lean_mkFVar(v_val_4532_);
v___x_4540_ = l_Lean_Expr_app___override(v___x_4538_, v___x_4539_);
v___x_4541_ = l_Lean_Meta_mkFalseElim(v_a_4537_, v___x_4540_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4543_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v___x_4541_, 1);
v___x_4543_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3913_, v_a_4542_, v___y_3919_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v___x_4544_; lean_object* v___x_4546_; 
lean_dec_ref_known(v___x_4543_, 1);
v___x_4544_ = lean_box(v___x_3923_);
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v___x_4544_);
v___x_4546_ = v___x_4534_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4544_);
v___x_4546_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4547_; lean_object* v___x_4549_; 
v___x_4547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
lean_ctor_set(v___x_4547_, 1, v___x_3948_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set_tag(v___x_4528_, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4547_);
v___x_4549_ = v___x_4528_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
v_a_3930_ = v___x_4549_;
goto v___jp_3929_;
}
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_del_object(v___x_4534_);
lean_del_object(v___x_4528_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
v_a_4552_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4543_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4543_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
else
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4567_; 
lean_del_object(v___x_4534_);
lean_del_object(v___x_4528_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4560_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4562_ = v___x_4541_;
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4541_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4560_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_del_object(v___x_4534_);
lean_dec(v_val_4532_);
lean_del_object(v___x_4528_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4568_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4536_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4536_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
}
else
{
lean_dec(v_a_4531_);
lean_del_object(v___x_4528_);
v___y_4388_ = v___y_3918_;
v___y_4389_ = v___y_3919_;
v___y_4390_ = v___y_3920_;
v___y_4391_ = v___y_3921_;
goto v___jp_4387_;
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_del_object(v___x_4528_);
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4577_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4530_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4530_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
}
else
{
lean_dec(v_a_4525_);
v___y_4388_ = v___y_3918_;
v___y_4389_ = v___y_3919_;
v___y_4390_ = v___y_3920_;
v___y_4391_ = v___y_3921_;
goto v___jp_4387_;
}
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4586_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4524_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4524_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
v___jp_4065_:
{
uint8_t v_genDiseq_4072_; 
v_genDiseq_4072_ = lean_ctor_get_uint8(v_config_3912_, sizeof(void*)*1 + 2);
if (v_genDiseq_4072_ == 0)
{
lean_dec_ref(v___x_4064_);
v___y_4042_ = v___y_4066_;
v___y_4043_ = v___y_4070_;
v___y_4044_ = v___y_4071_;
v___y_4045_ = v___y_4069_;
v___y_4046_ = v___y_4067_;
v___y_4047_ = v___y_4068_;
v___y_4048_ = v___x_4019_;
goto v___jp_4041_;
}
else
{
uint8_t v___x_4073_; 
v___x_4073_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4064_);
v___y_4042_ = v___y_4066_;
v___y_4043_ = v___y_4070_;
v___y_4044_ = v___y_4071_;
v___y_4045_ = v___y_4069_;
v___y_4046_ = v___y_4067_;
v___y_4047_ = v___y_4068_;
v___y_4048_ = v___x_4073_;
goto v___jp_4041_;
}
}
v___jp_4074_:
{
if (v___y_4082_ == 0)
{
lean_dec_ref(v___y_4078_);
v___y_4066_ = v___y_4076_;
v___y_4067_ = v___y_4080_;
v___y_4068_ = v___y_4077_;
v___y_4069_ = v___y_4075_;
v___y_4070_ = v___y_4079_;
v___y_4071_ = v___y_4081_;
goto v___jp_4065_;
}
else
{
lean_object* v___x_4083_; 
lean_dec_ref(v___x_4064_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v___x_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4083_, 0, v___y_4078_);
return v___x_4083_;
}
}
v___jp_4084_:
{
uint8_t v___x_4092_; 
v___x_4092_ = l_Lean_Exception_isInterrupt(v_a_4091_);
if (v___x_4092_ == 0)
{
uint8_t v___x_4093_; 
lean_inc_ref(v_a_4091_);
v___x_4093_ = l_Lean_Exception_isRuntime(v_a_4091_);
v___y_4075_ = v___y_4085_;
v___y_4076_ = v___y_4087_;
v___y_4077_ = v___y_4086_;
v___y_4078_ = v_a_4091_;
v___y_4079_ = v___y_4088_;
v___y_4080_ = v___y_4090_;
v___y_4081_ = v___y_4089_;
v___y_4082_ = v___x_4093_;
goto v___jp_4074_;
}
else
{
v___y_4075_ = v___y_4085_;
v___y_4076_ = v___y_4087_;
v___y_4077_ = v___y_4086_;
v___y_4078_ = v_a_4091_;
v___y_4079_ = v___y_4088_;
v___y_4080_ = v___y_4090_;
v___y_4081_ = v___y_4089_;
v___y_4082_ = v___x_4092_;
goto v___jp_4074_;
}
}
v___jp_4094_:
{
if (lean_obj_tag(v___y_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v_a_4103_ = lean_ctor_get(v___y_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___y_4102_, 1);
v___x_4104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4105_ = l_Lean_Expr_isConstOf(v_a_4103_, v___x_4104_);
lean_dec(v_a_4103_);
if (v___x_4105_ == 0)
{
lean_dec_ref(v___y_4096_);
v___y_4066_ = v___y_4097_;
v___y_4067_ = v___y_4100_;
v___y_4068_ = v___y_4098_;
v___y_4069_ = v___y_4095_;
v___y_4070_ = v___y_4099_;
v___y_4071_ = v___y_4101_;
goto v___jp_4065_;
}
else
{
lean_object* v___x_4106_; 
lean_inc_ref(v___y_4096_);
v___x_4106_ = l_Lean_Meta_mkEqRefl(v___y_4096_, v___y_4098_, v___y_4095_, v___y_4099_, v___y_4101_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4108_; lean_object* v_dummy_4109_; lean_object* v_nargs_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___x_4106_, 1);
v___x_4108_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_4110_ = l_Lean_Expr_getAppNumArgs(v___y_4096_);
lean_inc(v_nargs_4110_);
v___x_4111_ = lean_mk_array(v_nargs_4110_, v_dummy_4109_);
v___x_4112_ = lean_unsigned_to_nat(1u);
v___x_4113_ = lean_nat_sub(v_nargs_4110_, v___x_4112_);
lean_dec(v_nargs_4110_);
v___x_4114_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_4096_, v___x_4111_, v___x_4113_);
v___x_4115_ = lean_array_push(v___x_4114_, v_a_4107_);
v___x_4116_ = l_Lean_mkAppN(v___x_4108_, v___x_4115_);
lean_dec_ref(v___x_4115_);
lean_inc(v_mvarId_3913_);
v___x_4117_ = l_Lean_MVarId_getType(v_mvarId_3913_, v___y_4098_, v___y_4095_, v___y_4099_, v___y_4101_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref_known(v___x_4117_, 1);
lean_inc(v_val_3944_);
v___x_4119_ = l_Lean_LocalDecl_toExpr(v_val_3944_);
v___x_4120_ = l_Lean_Meta_mkAbsurd(v_a_4118_, v___x_4119_, v___x_4116_, v___y_4098_, v___y_4095_, v___y_4099_, v___y_4101_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4140_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4123_ = v___x_4120_;
v_isShared_4124_ = v_isSharedCheck_4140_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4120_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4140_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4125_; 
lean_inc(v_mvarId_3913_);
v___x_4125_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3913_, v_a_4121_, v___y_4095_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref(v___x_4064_);
lean_dec(v_val_3944_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4137_ == 0)
{
lean_object* v_unused_4138_; 
v_unused_4138_ = lean_ctor_get(v___x_4125_, 0);
lean_dec(v_unused_4138_);
v___x_4127_ = v___x_4125_;
v_isShared_4128_ = v_isSharedCheck_4137_;
goto v_resetjp_4126_;
}
else
{
lean_dec(v___x_4125_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4137_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4129_ = lean_box(v___x_3923_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set_tag(v___x_4127_, 1);
lean_ctor_set(v___x_4127_, 0, v___x_4129_);
v___x_4131_ = v___x_4127_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4134_; 
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
lean_ctor_set(v___x_4132_, 1, v___x_3948_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 0, v___x_4132_);
v___x_4134_ = v___x_4123_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4132_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
v_a_3930_ = v___x_4134_;
goto v___jp_3929_;
}
}
}
}
else
{
lean_object* v_a_4139_; 
lean_del_object(v___x_4123_);
v_a_4139_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4125_, 1);
v___y_4085_ = v___y_4095_;
v___y_4086_ = v___y_4098_;
v___y_4087_ = v___y_4097_;
v___y_4088_ = v___y_4099_;
v___y_4089_ = v___y_4101_;
v___y_4090_ = v___y_4100_;
v_a_4091_ = v_a_4139_;
goto v___jp_4084_;
}
}
}
else
{
lean_object* v_a_4141_; 
v_a_4141_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4120_, 1);
v___y_4085_ = v___y_4095_;
v___y_4086_ = v___y_4098_;
v___y_4087_ = v___y_4097_;
v___y_4088_ = v___y_4099_;
v___y_4089_ = v___y_4101_;
v___y_4090_ = v___y_4100_;
v_a_4091_ = v_a_4141_;
goto v___jp_4084_;
}
}
else
{
lean_object* v_a_4142_; 
lean_dec_ref(v___x_4116_);
v_a_4142_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4117_, 1);
v___y_4085_ = v___y_4095_;
v___y_4086_ = v___y_4098_;
v___y_4087_ = v___y_4097_;
v___y_4088_ = v___y_4099_;
v___y_4089_ = v___y_4101_;
v___y_4090_ = v___y_4100_;
v_a_4091_ = v_a_4142_;
goto v___jp_4084_;
}
}
else
{
lean_object* v_a_4143_; 
lean_dec_ref(v___y_4096_);
v_a_4143_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4106_, 1);
v___y_4085_ = v___y_4095_;
v___y_4086_ = v___y_4098_;
v___y_4087_ = v___y_4097_;
v___y_4088_ = v___y_4099_;
v___y_4089_ = v___y_4101_;
v___y_4090_ = v___y_4100_;
v_a_4091_ = v_a_4143_;
goto v___jp_4084_;
}
}
}
else
{
lean_object* v_a_4144_; 
lean_dec_ref(v___y_4096_);
v_a_4144_ = lean_ctor_get(v___y_4102_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___y_4102_, 1);
v___y_4085_ = v___y_4095_;
v___y_4086_ = v___y_4098_;
v___y_4087_ = v___y_4097_;
v___y_4088_ = v___y_4099_;
v___y_4089_ = v___y_4101_;
v___y_4090_ = v___y_4100_;
v_a_4091_ = v_a_4144_;
goto v___jp_4084_;
}
}
v___jp_4145_:
{
lean_object* v___x_4152_; 
lean_inc_ref(v___x_4064_);
v___x_4152_ = l_Lean_Meta_mkDecide(v___x_4064_, v___y_4148_, v___y_4146_, v___y_4149_, v___y_4151_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; uint8_t v_transparency_4155_; uint8_t v___x_4156_; uint8_t v___x_4157_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
v___x_4154_ = l_Lean_Meta_Context_config(v___y_4148_);
v_transparency_4155_ = lean_ctor_get_uint8(v___x_4154_, 9);
lean_dec_ref(v___x_4154_);
v___x_4156_ = 1;
v___x_4157_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4155_, v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v_keyedConfig_4158_; uint8_t v_trackZetaDelta_4159_; lean_object* v_zetaDeltaSet_4160_; lean_object* v_lctx_4161_; lean_object* v_localInstances_4162_; lean_object* v_defEqCtx_x3f_4163_; lean_object* v_synthPendingDepth_4164_; lean_object* v_customCanUnfoldPredicate_x3f_4165_; uint8_t v_univApprox_4166_; uint8_t v_inTypeClassResolution_4167_; uint8_t v_cacheInferType_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v_keyedConfig_4158_ = lean_ctor_get(v___y_4148_, 0);
v_trackZetaDelta_4159_ = lean_ctor_get_uint8(v___y_4148_, sizeof(void*)*7);
v_zetaDeltaSet_4160_ = lean_ctor_get(v___y_4148_, 1);
v_lctx_4161_ = lean_ctor_get(v___y_4148_, 2);
v_localInstances_4162_ = lean_ctor_get(v___y_4148_, 3);
v_defEqCtx_x3f_4163_ = lean_ctor_get(v___y_4148_, 4);
v_synthPendingDepth_4164_ = lean_ctor_get(v___y_4148_, 5);
v_customCanUnfoldPredicate_x3f_4165_ = lean_ctor_get(v___y_4148_, 6);
v_univApprox_4166_ = lean_ctor_get_uint8(v___y_4148_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4167_ = lean_ctor_get_uint8(v___y_4148_, sizeof(void*)*7 + 2);
v_cacheInferType_4168_ = lean_ctor_get_uint8(v___y_4148_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4158_);
v___x_4169_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4156_, v_keyedConfig_4158_);
lean_inc(v_customCanUnfoldPredicate_x3f_4165_);
lean_inc(v_synthPendingDepth_4164_);
lean_inc(v_defEqCtx_x3f_4163_);
lean_inc_ref(v_localInstances_4162_);
lean_inc_ref(v_lctx_4161_);
lean_inc(v_zetaDeltaSet_4160_);
v___x_4170_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
lean_ctor_set(v___x_4170_, 1, v_zetaDeltaSet_4160_);
lean_ctor_set(v___x_4170_, 2, v_lctx_4161_);
lean_ctor_set(v___x_4170_, 3, v_localInstances_4162_);
lean_ctor_set(v___x_4170_, 4, v_defEqCtx_x3f_4163_);
lean_ctor_set(v___x_4170_, 5, v_synthPendingDepth_4164_);
lean_ctor_set(v___x_4170_, 6, v_customCanUnfoldPredicate_x3f_4165_);
lean_ctor_set_uint8(v___x_4170_, sizeof(void*)*7, v_trackZetaDelta_4159_);
lean_ctor_set_uint8(v___x_4170_, sizeof(void*)*7 + 1, v_univApprox_4166_);
lean_ctor_set_uint8(v___x_4170_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4167_);
lean_ctor_set_uint8(v___x_4170_, sizeof(void*)*7 + 3, v_cacheInferType_4168_);
lean_inc(v___y_4151_);
lean_inc_ref(v___y_4149_);
lean_inc(v___y_4146_);
lean_inc(v_a_4153_);
v___x_4171_ = lean_whnf(v_a_4153_, v___x_4170_, v___y_4146_, v___y_4149_, v___y_4151_);
v___y_4095_ = v___y_4146_;
v___y_4096_ = v_a_4153_;
v___y_4097_ = v___y_4147_;
v___y_4098_ = v___y_4148_;
v___y_4099_ = v___y_4149_;
v___y_4100_ = v___y_4150_;
v___y_4101_ = v___y_4151_;
v___y_4102_ = v___x_4171_;
goto v___jp_4094_;
}
else
{
lean_object* v___x_4172_; 
lean_inc(v___y_4151_);
lean_inc_ref(v___y_4149_);
lean_inc(v___y_4146_);
lean_inc_ref(v___y_4148_);
lean_inc(v_a_4153_);
v___x_4172_ = lean_whnf(v_a_4153_, v___y_4148_, v___y_4146_, v___y_4149_, v___y_4151_);
v___y_4095_ = v___y_4146_;
v___y_4096_ = v_a_4153_;
v___y_4097_ = v___y_4147_;
v___y_4098_ = v___y_4148_;
v___y_4099_ = v___y_4149_;
v___y_4100_ = v___y_4150_;
v___y_4101_ = v___y_4151_;
v___y_4102_ = v___x_4172_;
goto v___jp_4094_;
}
}
else
{
lean_object* v_a_4173_; 
v_a_4173_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4152_, 1);
v___y_4085_ = v___y_4146_;
v___y_4086_ = v___y_4148_;
v___y_4087_ = v___y_4147_;
v___y_4088_ = v___y_4149_;
v___y_4089_ = v___y_4151_;
v___y_4090_ = v___y_4150_;
v_a_4091_ = v_a_4173_;
goto v___jp_4084_;
}
}
v___jp_4174_:
{
if (v___y_4181_ == 0)
{
v___y_4066_ = v___y_4176_;
v___y_4067_ = v___y_4179_;
v___y_4068_ = v___y_4177_;
v___y_4069_ = v___y_4175_;
v___y_4070_ = v___y_4178_;
v___y_4071_ = v___y_4180_;
goto v___jp_4065_;
}
else
{
v___y_4146_ = v___y_4175_;
v___y_4147_ = v___y_4176_;
v___y_4148_ = v___y_4177_;
v___y_4149_ = v___y_4178_;
v___y_4150_ = v___y_4179_;
v___y_4151_ = v___y_4180_;
goto v___jp_4145_;
}
}
v___jp_4182_:
{
if (v___y_4190_ == 0)
{
lean_dec_ref(v___y_4186_);
v___y_4175_ = v___y_4183_;
v___y_4176_ = v___y_4185_;
v___y_4177_ = v___y_4184_;
v___y_4178_ = v___y_4187_;
v___y_4179_ = v___y_4189_;
v___y_4180_ = v___y_4188_;
v___y_4181_ = v___x_4019_;
goto v___jp_4174_;
}
else
{
uint8_t v___x_4191_; 
v___x_4191_ = l_Lean_Expr_hasFVar(v___y_4186_);
lean_dec_ref(v___y_4186_);
if (v___x_4191_ == 0)
{
v___y_4146_ = v___y_4183_;
v___y_4147_ = v___y_4185_;
v___y_4148_ = v___y_4184_;
v___y_4149_ = v___y_4187_;
v___y_4150_ = v___y_4189_;
v___y_4151_ = v___y_4188_;
goto v___jp_4145_;
}
else
{
v___y_4175_ = v___y_4183_;
v___y_4176_ = v___y_4185_;
v___y_4177_ = v___y_4184_;
v___y_4178_ = v___y_4187_;
v___y_4179_ = v___y_4189_;
v___y_4180_ = v___y_4188_;
v___y_4181_ = v___x_4019_;
goto v___jp_4174_;
}
}
}
v___jp_4192_:
{
lean_object* v___x_4200_; 
lean_inc_ref(v___x_4064_);
v___x_4200_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4064_, v___y_4193_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; uint8_t v___x_4202_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref_known(v___x_4200_, 1);
v___x_4202_ = l_Lean_Expr_hasMVar(v_a_4201_);
if (v___x_4202_ == 0)
{
v___y_4183_ = v___y_4193_;
v___y_4184_ = v___y_4194_;
v___y_4185_ = v___y_4195_;
v___y_4186_ = v_a_4201_;
v___y_4187_ = v___y_4196_;
v___y_4188_ = v___y_4197_;
v___y_4189_ = v___y_4198_;
v___y_4190_ = v___y_4199_;
goto v___jp_4182_;
}
else
{
v___y_4183_ = v___y_4193_;
v___y_4184_ = v___y_4194_;
v___y_4185_ = v___y_4195_;
v___y_4186_ = v_a_4201_;
v___y_4187_ = v___y_4196_;
v___y_4188_ = v___y_4197_;
v___y_4189_ = v___y_4198_;
v___y_4190_ = v___x_4019_;
goto v___jp_4182_;
}
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec_ref(v___x_4064_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4203_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4200_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4200_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
v___jp_4211_:
{
if (v___y_4218_ == 0)
{
v___y_4066_ = v___y_4213_;
v___y_4067_ = v___y_4216_;
v___y_4068_ = v___y_4214_;
v___y_4069_ = v___y_4212_;
v___y_4070_ = v___y_4215_;
v___y_4071_ = v___y_4217_;
goto v___jp_4065_;
}
else
{
v___y_4193_ = v___y_4212_;
v___y_4194_ = v___y_4214_;
v___y_4195_ = v___y_4213_;
v___y_4196_ = v___y_4215_;
v___y_4197_ = v___y_4217_;
v___y_4198_ = v___y_4216_;
v___y_4199_ = v___y_4218_;
goto v___jp_4192_;
}
}
v___jp_4219_:
{
uint8_t v_useDecide_4226_; 
v_useDecide_4226_ = lean_ctor_get_uint8(v_config_3912_, sizeof(void*)*1);
if (v_useDecide_4226_ == 0)
{
v___y_4212_ = v___y_4223_;
v___y_4213_ = v___y_4220_;
v___y_4214_ = v___y_4222_;
v___y_4215_ = v___y_4224_;
v___y_4216_ = v_isHEq_4221_;
v___y_4217_ = v___y_4225_;
v___y_4218_ = v___x_4019_;
goto v___jp_4211_;
}
else
{
uint8_t v___x_4227_; 
v___x_4227_ = l_Lean_Expr_hasFVar(v___x_4064_);
if (v___x_4227_ == 0)
{
v___y_4193_ = v___y_4223_;
v___y_4194_ = v___y_4222_;
v___y_4195_ = v___y_4220_;
v___y_4196_ = v___y_4224_;
v___y_4197_ = v___y_4225_;
v___y_4198_ = v_isHEq_4221_;
v___y_4199_ = v_useDecide_4226_;
goto v___jp_4192_;
}
else
{
v___y_4212_ = v___y_4223_;
v___y_4213_ = v___y_4220_;
v___y_4214_ = v___y_4222_;
v___y_4215_ = v___y_4224_;
v___y_4216_ = v_isHEq_4221_;
v___y_4217_ = v___y_4225_;
v___y_4218_ = v___x_4019_;
goto v___jp_4211_;
}
}
}
v___jp_4228_:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Lean_Meta_isExprDefEq(v___y_4234_, v___y_4233_, v___y_4230_, v___y_4231_, v___y_4235_, v___y_4229_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; uint8_t v___x_4238_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
v___x_4238_ = lean_unbox(v_a_4237_);
lean_dec(v_a_4237_);
if (v___x_4238_ == 0)
{
v___y_4220_ = v___y_4232_;
v_isHEq_4221_ = v___x_3923_;
v___y_4222_ = v___y_4230_;
v___y_4223_ = v___y_4231_;
v___y_4224_ = v___y_4235_;
v___y_4225_ = v___y_4229_;
goto v___jp_4219_;
}
else
{
lean_object* v___x_4239_; 
lean_dec_ref(v___x_4064_);
lean_dec_ref(v_config_3912_);
lean_inc(v_mvarId_3913_);
v___x_4239_ = l_Lean_MVarId_getType(v_mvarId_3913_, v___y_4230_, v___y_4231_, v___y_4235_, v___y_4229_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref_known(v___x_4239_, 1);
v___x_4241_ = l_Lean_LocalDecl_toExpr(v_val_3944_);
v___x_4242_ = l_Lean_Meta_mkEqOfHEq(v___x_4241_, v___x_3923_, v___y_4230_, v___y_4231_, v___y_4235_, v___y_4229_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4244_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v___x_4242_, 1);
v___x_4244_ = l_Lean_Meta_mkNoConfusion(v_a_4240_, v_a_4243_, v___y_4230_, v___y_4231_, v___y_4235_, v___y_4229_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4246_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
v___x_4246_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3913_, v_a_4245_, v___y_4231_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
lean_dec_ref_known(v___x_4246_, 1);
v___x_4247_ = lean_box(v___x_3923_);
v___x_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
v___x_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4248_);
lean_ctor_set(v___x_4249_, 1, v___x_3948_);
v___x_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4249_);
v_a_3930_ = v___x_4250_;
goto v___jp_3929_;
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
v_a_4251_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4246_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4246_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4259_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4244_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4244_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v_a_4240_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4267_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4242_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4242_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4275_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4239_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4239_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_dec_ref(v___x_4064_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4283_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4236_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4236_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
v___jp_4291_:
{
lean_object* v___x_4297_; 
lean_inc_ref(v___x_4064_);
v___x_4297_ = l_Lean_Meta_matchHEq_x3f(v___x_4064_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
if (lean_obj_tag(v_a_4298_) == 1)
{
lean_object* v_val_4299_; lean_object* v_snd_4300_; lean_object* v_snd_4301_; lean_object* v_fst_4302_; lean_object* v_fst_4303_; lean_object* v_fst_4304_; lean_object* v_snd_4305_; lean_object* v___x_4306_; 
v_val_4299_ = lean_ctor_get(v_a_4298_, 0);
lean_inc(v_val_4299_);
lean_dec_ref_known(v_a_4298_, 1);
v_snd_4300_ = lean_ctor_get(v_val_4299_, 1);
lean_inc(v_snd_4300_);
v_snd_4301_ = lean_ctor_get(v_snd_4300_, 1);
lean_inc(v_snd_4301_);
v_fst_4302_ = lean_ctor_get(v_val_4299_, 0);
lean_inc(v_fst_4302_);
lean_dec(v_val_4299_);
v_fst_4303_ = lean_ctor_get(v_snd_4300_, 0);
lean_inc(v_fst_4303_);
lean_dec(v_snd_4300_);
v_fst_4304_ = lean_ctor_get(v_snd_4301_, 0);
lean_inc(v_fst_4304_);
v_snd_4305_ = lean_ctor_get(v_snd_4301_, 1);
lean_inc(v_snd_4305_);
lean_dec(v_snd_4301_);
v___x_4306_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4303_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
if (lean_obj_tag(v_a_4307_) == 1)
{
lean_object* v_val_4308_; lean_object* v___x_4309_; 
v_val_4308_ = lean_ctor_get(v_a_4307_, 0);
lean_inc(v_val_4308_);
lean_dec_ref_known(v_a_4307_, 1);
v___x_4309_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4305_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4309_, 1);
if (lean_obj_tag(v_a_4310_) == 1)
{
lean_object* v_toConstantVal_4311_; lean_object* v_val_4312_; lean_object* v_toConstantVal_4313_; lean_object* v_name_4314_; lean_object* v_name_4315_; uint8_t v___x_4316_; 
v_toConstantVal_4311_ = lean_ctor_get(v_val_4308_, 0);
lean_inc_ref(v_toConstantVal_4311_);
lean_dec(v_val_4308_);
v_val_4312_ = lean_ctor_get(v_a_4310_, 0);
lean_inc(v_val_4312_);
lean_dec_ref_known(v_a_4310_, 1);
v_toConstantVal_4313_ = lean_ctor_get(v_val_4312_, 0);
lean_inc_ref(v_toConstantVal_4313_);
lean_dec(v_val_4312_);
v_name_4314_ = lean_ctor_get(v_toConstantVal_4311_, 0);
lean_inc(v_name_4314_);
lean_dec_ref(v_toConstantVal_4311_);
v_name_4315_ = lean_ctor_get(v_toConstantVal_4313_, 0);
lean_inc(v_name_4315_);
lean_dec_ref(v_toConstantVal_4313_);
v___x_4316_ = lean_name_eq(v_name_4314_, v_name_4315_);
lean_dec(v_name_4315_);
lean_dec(v_name_4314_);
if (v___x_4316_ == 0)
{
v___y_4229_ = v___y_4296_;
v___y_4230_ = v___y_4293_;
v___y_4231_ = v___y_4294_;
v___y_4232_ = v_isEq_4292_;
v___y_4233_ = v_fst_4304_;
v___y_4234_ = v_fst_4302_;
v___y_4235_ = v___y_4295_;
goto v___jp_4228_;
}
else
{
if (v___x_4019_ == 0)
{
lean_dec(v_fst_4304_);
lean_dec(v_fst_4302_);
v___y_4220_ = v_isEq_4292_;
v_isHEq_4221_ = v___x_3923_;
v___y_4222_ = v___y_4293_;
v___y_4223_ = v___y_4294_;
v___y_4224_ = v___y_4295_;
v___y_4225_ = v___y_4296_;
goto v___jp_4219_;
}
else
{
v___y_4229_ = v___y_4296_;
v___y_4230_ = v___y_4293_;
v___y_4231_ = v___y_4294_;
v___y_4232_ = v_isEq_4292_;
v___y_4233_ = v_fst_4304_;
v___y_4234_ = v_fst_4302_;
v___y_4235_ = v___y_4295_;
goto v___jp_4228_;
}
}
}
else
{
lean_dec(v_a_4310_);
lean_dec(v_val_4308_);
lean_dec(v_fst_4304_);
lean_dec(v_fst_4302_);
v___y_4220_ = v_isEq_4292_;
v_isHEq_4221_ = v___x_3923_;
v___y_4222_ = v___y_4293_;
v___y_4223_ = v___y_4294_;
v___y_4224_ = v___y_4295_;
v___y_4225_ = v___y_4296_;
goto v___jp_4219_;
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4324_; 
lean_dec(v_val_4308_);
lean_dec(v_fst_4304_);
lean_dec(v_fst_4302_);
lean_dec_ref(v___x_4064_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4317_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4319_ = v___x_4309_;
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4309_);
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
lean_dec(v_a_4307_);
lean_dec(v_snd_4305_);
lean_dec(v_fst_4304_);
lean_dec(v_fst_4302_);
v___y_4220_ = v_isEq_4292_;
v_isHEq_4221_ = v___x_3923_;
v___y_4222_ = v___y_4293_;
v___y_4223_ = v___y_4294_;
v___y_4224_ = v___y_4295_;
v___y_4225_ = v___y_4296_;
goto v___jp_4219_;
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec(v_snd_4305_);
lean_dec(v_fst_4304_);
lean_dec(v_fst_4302_);
lean_dec_ref(v___x_4064_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4325_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4306_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4306_);
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
else
{
lean_dec(v_a_4298_);
v___y_4220_ = v_isEq_4292_;
v_isHEq_4221_ = v___x_4019_;
v___y_4222_ = v___y_4293_;
v___y_4223_ = v___y_4294_;
v___y_4224_ = v___y_4295_;
v___y_4225_ = v___y_4296_;
goto v___jp_4219_;
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_dec_ref(v___x_4064_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4333_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4297_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4297_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
v___jp_4341_:
{
lean_object* v___x_4346_; 
lean_inc_ref(v___x_4064_);
v___x_4346_ = l_Lean_Meta_matchEq_x3f(v___x_4064_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4346_, 1);
if (lean_obj_tag(v_a_4347_) == 1)
{
lean_object* v_val_4348_; lean_object* v_snd_4349_; lean_object* v_fst_4350_; lean_object* v_snd_4351_; lean_object* v___x_4352_; 
v_val_4348_ = lean_ctor_get(v_a_4347_, 0);
lean_inc(v_val_4348_);
lean_dec_ref_known(v_a_4347_, 1);
v_snd_4349_ = lean_ctor_get(v_val_4348_, 1);
lean_inc(v_snd_4349_);
lean_dec(v_val_4348_);
v_fst_4350_ = lean_ctor_get(v_snd_4349_, 0);
lean_inc(v_fst_4350_);
v_snd_4351_ = lean_ctor_get(v_snd_4349_, 1);
lean_inc(v_snd_4351_);
lean_dec(v_snd_4349_);
v___x_4352_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4350_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
if (lean_obj_tag(v_a_4353_) == 1)
{
lean_object* v_val_4354_; lean_object* v___x_4355_; 
v_val_4354_ = lean_ctor_get(v_a_4353_, 0);
lean_inc(v_val_4354_);
lean_dec_ref_known(v_a_4353_, 1);
v___x_4355_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4351_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
if (lean_obj_tag(v_a_4356_) == 1)
{
lean_object* v_toConstantVal_4357_; lean_object* v_val_4358_; lean_object* v_toConstantVal_4359_; lean_object* v_name_4360_; lean_object* v_name_4361_; uint8_t v___x_4362_; 
v_toConstantVal_4357_ = lean_ctor_get(v_val_4354_, 0);
lean_inc_ref(v_toConstantVal_4357_);
lean_dec(v_val_4354_);
v_val_4358_ = lean_ctor_get(v_a_4356_, 0);
lean_inc(v_val_4358_);
lean_dec_ref_known(v_a_4356_, 1);
v_toConstantVal_4359_ = lean_ctor_get(v_val_4358_, 0);
lean_inc_ref(v_toConstantVal_4359_);
lean_dec(v_val_4358_);
v_name_4360_ = lean_ctor_get(v_toConstantVal_4357_, 0);
lean_inc(v_name_4360_);
lean_dec_ref(v_toConstantVal_4357_);
v_name_4361_ = lean_ctor_get(v_toConstantVal_4359_, 0);
lean_inc(v_name_4361_);
lean_dec_ref(v_toConstantVal_4359_);
v___x_4362_ = lean_name_eq(v_name_4360_, v_name_4361_);
lean_dec(v_name_4361_);
lean_dec(v_name_4360_);
if (v___x_4362_ == 0)
{
lean_dec_ref(v___x_4064_);
lean_dec_ref(v_config_3912_);
v___y_3950_ = v___y_4344_;
v___y_3951_ = v___y_4342_;
v___y_3952_ = v___y_4343_;
v___y_3953_ = v___y_4345_;
goto v___jp_3949_;
}
else
{
if (v___x_4019_ == 0)
{
lean_del_object(v___x_3946_);
v_isEq_4292_ = v___x_3923_;
v___y_4293_ = v___y_4342_;
v___y_4294_ = v___y_4343_;
v___y_4295_ = v___y_4344_;
v___y_4296_ = v___y_4345_;
goto v___jp_4291_;
}
else
{
lean_dec_ref(v___x_4064_);
lean_dec_ref(v_config_3912_);
v___y_3950_ = v___y_4344_;
v___y_3951_ = v___y_4342_;
v___y_3952_ = v___y_4343_;
v___y_3953_ = v___y_4345_;
goto v___jp_3949_;
}
}
}
else
{
lean_dec(v_a_4356_);
lean_dec(v_val_4354_);
lean_del_object(v___x_3946_);
v_isEq_4292_ = v___x_3923_;
v___y_4293_ = v___y_4342_;
v___y_4294_ = v___y_4343_;
v___y_4295_ = v___y_4344_;
v___y_4296_ = v___y_4345_;
goto v___jp_4291_;
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec(v_val_4354_);
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4363_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4355_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4355_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
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
lean_dec(v_a_4353_);
lean_dec(v_snd_4351_);
lean_del_object(v___x_3946_);
v_isEq_4292_ = v___x_3923_;
v___y_4293_ = v___y_4342_;
v___y_4294_ = v___y_4343_;
v___y_4295_ = v___y_4344_;
v___y_4296_ = v___y_4345_;
goto v___jp_4291_;
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec(v_snd_4351_);
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4371_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4352_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4352_);
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
else
{
lean_dec(v_a_4347_);
lean_del_object(v___x_3946_);
v_isEq_4292_ = v___x_4019_;
v___y_4293_ = v___y_4342_;
v___y_4294_ = v___y_4343_;
v___y_4295_ = v___y_4344_;
v___y_4296_ = v___y_4345_;
goto v___jp_4291_;
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4379_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4346_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4346_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
v___jp_4387_:
{
lean_object* v___x_4392_; 
lean_inc_ref(v___x_4064_);
v___x_4392_ = l_Lean_refutableHasNotBit_x3f(v___x_4064_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4393_);
lean_dec_ref_known(v___x_4392_, 1);
if (lean_obj_tag(v_a_4393_) == 1)
{
lean_object* v_val_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4434_; 
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec_ref(v_config_3912_);
v_val_4394_ = lean_ctor_get(v_a_4393_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v_a_4393_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4396_ = v_a_4393_;
v_isShared_4397_ = v_isSharedCheck_4434_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_val_4394_);
lean_dec(v_a_4393_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4434_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; 
lean_inc(v_mvarId_3913_);
v___x_4398_ = l_Lean_MVarId_getType(v_mvarId_3913_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v___x_4400_ = l_Lean_LocalDecl_toExpr(v_val_3944_);
v___x_4401_ = l_Lean_Meta_mkAbsurd(v_a_4399_, v_val_4394_, v___x_4400_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___x_4403_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v___x_4403_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3913_, v_a_4402_, v___y_4389_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v___x_4404_; lean_object* v___x_4406_; 
lean_dec_ref_known(v___x_4403_, 1);
v___x_4404_ = lean_box(v___x_3923_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4404_);
v___x_4406_ = v___x_4396_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4404_);
v___x_4406_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
lean_ctor_set(v___x_4407_, 1, v___x_3948_);
v___x_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4407_);
v_a_3930_ = v___x_4408_;
goto v___jp_3929_;
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_del_object(v___x_4396_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
v_a_4410_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4403_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4403_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_del_object(v___x_4396_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4418_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4401_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4401_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4426_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4398_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4398_);
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
}
else
{
lean_object* v___x_4435_; 
lean_dec(v_a_4393_);
lean_inc_ref(v___x_4064_);
v___x_4435_ = l_Lean_Meta_matchNe_x3f(v___x_4064_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v___x_4435_, 1);
if (lean_obj_tag(v_a_4436_) == 1)
{
lean_object* v_val_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4507_; 
v_val_4437_ = lean_ctor_get(v_a_4436_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v_a_4436_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4439_ = v_a_4436_;
v_isShared_4440_ = v_isSharedCheck_4507_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_val_4437_);
lean_dec(v_a_4436_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4507_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v_snd_4441_; lean_object* v_fst_4442_; lean_object* v_snd_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4506_; 
v_snd_4441_ = lean_ctor_get(v_val_4437_, 1);
lean_inc(v_snd_4441_);
lean_dec(v_val_4437_);
v_fst_4442_ = lean_ctor_get(v_snd_4441_, 0);
v_snd_4443_ = lean_ctor_get(v_snd_4441_, 1);
v_isSharedCheck_4506_ = !lean_is_exclusive(v_snd_4441_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4445_ = v_snd_4441_;
v_isShared_4446_ = v_isSharedCheck_4506_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_snd_4443_);
lean_inc(v_fst_4442_);
lean_dec(v_snd_4441_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4506_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4447_; 
lean_inc(v_fst_4442_);
v___x_4447_ = l_Lean_Meta_isExprDefEq(v_fst_4442_, v_snd_4443_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; uint8_t v___x_4449_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref_known(v___x_4447_, 1);
v___x_4449_ = lean_unbox(v_a_4448_);
lean_dec(v_a_4448_);
if (v___x_4449_ == 0)
{
lean_del_object(v___x_4445_);
lean_dec(v_fst_4442_);
lean_del_object(v___x_4439_);
v___y_4342_ = v___y_4388_;
v___y_4343_ = v___y_4389_;
v___y_4344_ = v___y_4390_;
v___y_4345_ = v___y_4391_;
goto v___jp_4341_;
}
else
{
lean_object* v___x_4450_; 
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec_ref(v_config_3912_);
lean_inc(v_mvarId_3913_);
v___x_4450_ = l_Lean_MVarId_getType(v_mvarId_3913_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4452_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_a_4451_);
lean_dec_ref_known(v___x_4450_, 1);
v___x_4452_ = l_Lean_Meta_mkEqRefl(v_fst_4442_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4452_, 1);
v___x_4454_ = l_Lean_LocalDecl_toExpr(v_val_3944_);
v___x_4455_ = l_Lean_Meta_mkAbsurd(v_a_4451_, v_a_4453_, v___x_4454_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4457_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref_known(v___x_4455_, 1);
v___x_4457_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3913_, v_a_4456_, v___y_4389_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4460_; 
lean_dec_ref_known(v___x_4457_, 1);
v___x_4458_ = lean_box(v___x_3923_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 0, v___x_4458_);
v___x_4460_ = v___x_4439_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4458_);
v___x_4460_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
lean_object* v___x_4462_; 
if (v_isShared_4446_ == 0)
{
lean_ctor_set(v___x_4445_, 1, v___x_3948_);
lean_ctor_set(v___x_4445_, 0, v___x_4460_);
v___x_4462_ = v___x_4445_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4460_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v___x_3948_);
v___x_4462_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4462_);
v_a_3930_ = v___x_4463_;
goto v___jp_3929_;
}
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
lean_del_object(v___x_4445_);
lean_del_object(v___x_4439_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
v_a_4466_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4457_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4457_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_del_object(v___x_4445_);
lean_del_object(v___x_4439_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4474_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4455_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4455_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
else
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
lean_dec(v_a_4451_);
lean_del_object(v___x_4445_);
lean_del_object(v___x_4439_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4482_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_4452_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4452_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_del_object(v___x_4445_);
lean_dec(v_fst_4442_);
lean_del_object(v___x_4439_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_4490_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4450_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4450_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_del_object(v___x_4445_);
lean_dec(v_fst_4442_);
lean_del_object(v___x_4439_);
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4498_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4447_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4447_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4436_);
v___y_4342_ = v___y_4388_;
v___y_4343_ = v___y_4389_;
v___y_4344_ = v___y_4390_;
v___y_4345_ = v___y_4391_;
goto v___jp_4341_;
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4508_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4435_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4435_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec_ref(v___x_4064_);
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4516_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4392_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4392_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
}
else
{
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
v_a_3938_ = v___x_3990_;
goto v___jp_3937_;
}
v___jp_3949_:
{
lean_object* v___x_3954_; 
lean_inc(v_mvarId_3913_);
v___x_3954_ = l_Lean_MVarId_getType(v_mvarId_3913_, v___y_3951_, v___y_3952_, v___y_3950_, v___y_3953_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
v___x_3956_ = l_Lean_LocalDecl_toExpr(v_val_3944_);
v___x_3957_ = l_Lean_Meta_mkNoConfusion(v_a_3955_, v___x_3956_, v___y_3951_, v___y_3952_, v___y_3950_, v___y_3953_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3959_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3913_, v_a_3958_, v___y_3952_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
lean_dec_ref_known(v___x_3959_, 1);
v___x_3960_ = lean_box(v___x_3923_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 0, v___x_3960_);
v___x_3962_ = v___x_3946_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
lean_ctor_set(v___x_3963_, 1, v___x_3948_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
v_a_3930_ = v___x_3964_;
goto v___jp_3929_;
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_del_object(v___x_3946_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
v_a_3966_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3959_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3959_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_del_object(v___x_3946_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_3974_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3957_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3957_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_del_object(v___x_3946_);
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
v_a_3982_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3954_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3954_);
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
v___jp_3991_:
{
lean_object* v_searchFuel_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v_searchFuel_3996_ = lean_ctor_get(v_config_3912_, 0);
v___x_3997_ = l_Lean_LocalDecl_fvarId(v_val_3944_);
lean_dec(v_val_3944_);
lean_inc(v_searchFuel_3996_);
lean_inc(v_mvarId_3913_);
v___x_3998_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3913_, v___x_3997_, v_searchFuel_3996_, v___y_3994_, v___y_3993_, v___y_3992_, v___y_3995_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; uint8_t v___x_4000_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4000_ = lean_unbox(v_a_3999_);
lean_dec(v_a_3999_);
if (v___x_4000_ == 0)
{
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
v_a_3938_ = v___x_3990_;
goto v___jp_3937_;
}
else
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v___x_4001_ = lean_box(v___x_3923_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
lean_ctor_set(v___x_4003_, 1, v___x_3948_);
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
v_a_3930_ = v___x_4004_;
goto v___jp_3929_;
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4005_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3998_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3998_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
v___jp_4013_:
{
if (v___y_4018_ == 0)
{
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
v_a_3938_ = v___x_3990_;
goto v___jp_3937_;
}
else
{
v___y_3992_ = v___y_4014_;
v___y_3993_ = v___y_4015_;
v___y_3994_ = v___y_4016_;
v___y_3995_ = v___y_4017_;
goto v___jp_3991_;
}
}
v___jp_4020_:
{
if (v___y_4023_ == 0)
{
v___y_3992_ = v___y_4021_;
v___y_3993_ = v___y_4022_;
v___y_3994_ = v___y_4024_;
v___y_3995_ = v___y_4025_;
goto v___jp_3991_;
}
else
{
v___y_4014_ = v___y_4021_;
v___y_4015_ = v___y_4022_;
v___y_4016_ = v___y_4024_;
v___y_4017_ = v___y_4025_;
v___y_4018_ = v___x_4019_;
goto v___jp_4013_;
}
}
v___jp_4026_:
{
if (v___y_4032_ == 0)
{
v___y_4014_ = v___y_4027_;
v___y_4015_ = v___y_4028_;
v___y_4016_ = v___y_4030_;
v___y_4017_ = v___y_4031_;
v___y_4018_ = v___x_4019_;
goto v___jp_4013_;
}
else
{
v___y_4021_ = v___y_4027_;
v___y_4022_ = v___y_4028_;
v___y_4023_ = v___y_4029_;
v___y_4024_ = v___y_4030_;
v___y_4025_ = v___y_4031_;
goto v___jp_4020_;
}
}
v___jp_4033_:
{
uint8_t v_emptyType_4040_; 
v_emptyType_4040_ = lean_ctor_get_uint8(v_config_3912_, sizeof(void*)*1 + 1);
if (v_emptyType_4040_ == 0)
{
v___y_4027_ = v___y_4038_;
v___y_4028_ = v___y_4037_;
v___y_4029_ = v___y_4035_;
v___y_4030_ = v___y_4036_;
v___y_4031_ = v___y_4039_;
v___y_4032_ = v___x_4019_;
goto v___jp_4026_;
}
else
{
if (v___y_4034_ == 0)
{
v___y_4021_ = v___y_4038_;
v___y_4022_ = v___y_4037_;
v___y_4023_ = v___y_4035_;
v___y_4024_ = v___y_4036_;
v___y_4025_ = v___y_4039_;
goto v___jp_4020_;
}
else
{
v___y_4027_ = v___y_4038_;
v___y_4028_ = v___y_4037_;
v___y_4029_ = v___y_4035_;
v___y_4030_ = v___y_4036_;
v___y_4031_ = v___y_4039_;
v___y_4032_ = v___x_4019_;
goto v___jp_4026_;
}
}
}
v___jp_4041_:
{
if (v___y_4048_ == 0)
{
v___y_4034_ = v___y_4042_;
v___y_4035_ = v___y_4046_;
v___y_4036_ = v___y_4047_;
v___y_4037_ = v___y_4045_;
v___y_4038_ = v___y_4043_;
v___y_4039_ = v___y_4044_;
goto v___jp_4033_;
}
else
{
lean_object* v___x_4049_; 
lean_inc(v_val_3944_);
lean_inc(v_mvarId_3913_);
v___x_4049_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3913_, v_val_3944_, v___y_4047_, v___y_4045_, v___y_4043_, v___y_4044_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; uint8_t v___x_4051_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v___x_4051_ = lean_unbox(v_a_4050_);
lean_dec(v_a_4050_);
if (v___x_4051_ == 0)
{
v___y_4034_ = v___y_4042_;
v___y_4035_ = v___y_4046_;
v___y_4036_ = v___y_4047_;
v___y_4037_ = v___y_4045_;
v___y_4038_ = v___y_4043_;
v___y_4039_ = v___y_4044_;
goto v___jp_4033_;
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
lean_dec(v_val_3944_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v___x_4052_ = lean_box(v___x_3923_);
v___x_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
v___x_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
lean_ctor_set(v___x_4054_, 1, v___x_3948_);
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
v_a_3930_ = v___x_4055_;
goto v___jp_3929_;
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec(v_val_3944_);
lean_del_object(v___x_3927_);
lean_dec(v_snd_3925_);
lean_dec(v_mvarId_3913_);
lean_dec_ref(v_config_3912_);
v_a_4056_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4049_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4049_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
}
}
v___jp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3933_; 
v___x_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3931_, 0, v_a_3930_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3931_);
v___x_3933_ = v___x_3927_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3931_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_snd_3925_);
v___x_3933_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
return v___x_3934_;
}
}
v___jp_3937_:
{
lean_object* v___x_3939_; size_t v___x_3940_; size_t v___x_3941_; lean_object* v___x_3942_; 
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3936_);
lean_ctor_set(v___x_3939_, 1, v_a_3938_);
v___x_3940_ = ((size_t)1ULL);
v___x_3941_ = lean_usize_add(v_i_3916_, v___x_3940_);
v___x_3942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3912_, v_mvarId_3913_, v_as_3914_, v_sz_3915_, v___x_3941_, v___x_3939_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
return v___x_3942_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_3912_ = stack[0].m_obj;
lean_object* v_mvarId_3913_ = stack[1].m_obj;
lean_object* v_as_3914_ = stack[2].m_obj;
size_t v_sz_3915_ = stack[3].m_num;
size_t v_i_3916_ = stack[4].m_num;
lean_object* v_b_3917_ = stack[5].m_obj;
lean_object* v___y_3918_ = stack[6].m_obj;
lean_object* v___y_3919_ = stack[7].m_obj;
lean_object* v___y_3920_ = stack[8].m_obj;
lean_object* v___y_3921_ = stack[9].m_obj;
lean_object* v_res_4597_;
v_res_4597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_3912_, v_mvarId_3913_, v_as_3914_, v_sz_3915_, v_i_3916_, v_b_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
stack->m_obj
 = v_res_4597_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4598_, lean_object* v_mvarId_4599_, lean_object* v_as_4600_, lean_object* v_sz_4601_, lean_object* v_i_4602_, lean_object* v_b_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
size_t v_sz_boxed_4609_; size_t v_i_boxed_4610_; lean_object* v_res_4611_; 
v_sz_boxed_4609_ = lean_unbox_usize(v_sz_4601_);
lean_dec(v_sz_4601_);
v_i_boxed_4610_ = lean_unbox_usize(v_i_4602_);
lean_dec(v_i_4602_);
v_res_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4598_, v_mvarId_4599_, v_as_4600_, v_sz_boxed_4609_, v_i_boxed_4610_, v_b_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec_ref(v_as_4600_);
return v_res_4611_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4612_, lean_object* v_config_4613_, lean_object* v_mvarId_4614_, lean_object* v_n_4615_, lean_object* v_b_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
if (lean_obj_tag(v_n_4615_) == 0)
{
lean_object* v_cs_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; size_t v_sz_4625_; size_t v___x_4626_; lean_object* v___x_4627_; 
v_cs_4622_ = lean_ctor_get(v_n_4615_, 0);
v___x_4623_ = lean_box(0);
v___x_4624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4623_);
lean_ctor_set(v___x_4624_, 1, v_b_4616_);
v_sz_4625_ = lean_array_size(v_cs_4622_);
v___x_4626_ = ((size_t)0ULL);
v___x_4627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4612_, v_config_4613_, v_mvarId_4614_, v_cs_4622_, v_sz_4625_, v___x_4626_, v___x_4624_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4642_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4630_ = v___x_4627_;
v_isShared_4631_ = v_isSharedCheck_4642_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4627_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4642_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v_fst_4632_; 
v_fst_4632_ = lean_ctor_get(v_a_4628_, 0);
if (lean_obj_tag(v_fst_4632_) == 0)
{
lean_object* v_snd_4633_; lean_object* v___x_4634_; lean_object* v___x_4636_; 
v_snd_4633_ = lean_ctor_get(v_a_4628_, 1);
lean_inc(v_snd_4633_);
lean_dec(v_a_4628_);
v___x_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4634_, 0, v_snd_4633_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 0, v___x_4634_);
v___x_4636_ = v___x_4630_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
else
{
lean_object* v_val_4638_; lean_object* v___x_4640_; 
lean_inc_ref(v_fst_4632_);
lean_dec(v_a_4628_);
v_val_4638_ = lean_ctor_get(v_fst_4632_, 0);
lean_inc(v_val_4638_);
lean_dec_ref_known(v_fst_4632_, 1);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 0, v_val_4638_);
v___x_4640_ = v___x_4630_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_val_4638_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
else
{
lean_object* v_a_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4650_; 
v_a_4643_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4645_ = v___x_4627_;
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_a_4643_);
lean_dec(v___x_4627_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4648_; 
if (v_isShared_4646_ == 0)
{
v___x_4648_ = v___x_4645_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4643_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
}
else
{
lean_object* v_vs_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; size_t v_sz_4654_; size_t v___x_4655_; lean_object* v___x_4656_; 
v_vs_4651_ = lean_ctor_get(v_n_4615_, 0);
v___x_4652_ = lean_box(0);
v___x_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
lean_ctor_set(v___x_4653_, 1, v_b_4616_);
v_sz_4654_ = lean_array_size(v_vs_4651_);
v___x_4655_ = ((size_t)0ULL);
v___x_4656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4613_, v_mvarId_4614_, v_vs_4651_, v_sz_4654_, v___x_4655_, v___x_4653_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4671_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4659_ = v___x_4656_;
v_isShared_4660_ = v_isSharedCheck_4671_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4671_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v_fst_4661_; 
v_fst_4661_ = lean_ctor_get(v_a_4657_, 0);
if (lean_obj_tag(v_fst_4661_) == 0)
{
lean_object* v_snd_4662_; lean_object* v___x_4663_; lean_object* v___x_4665_; 
v_snd_4662_ = lean_ctor_get(v_a_4657_, 1);
lean_inc(v_snd_4662_);
lean_dec(v_a_4657_);
v___x_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4663_, 0, v_snd_4662_);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 0, v___x_4663_);
v___x_4665_ = v___x_4659_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
else
{
lean_object* v_val_4667_; lean_object* v___x_4669_; 
lean_inc_ref(v_fst_4661_);
lean_dec(v_a_4657_);
v_val_4667_ = lean_ctor_get(v_fst_4661_, 0);
lean_inc(v_val_4667_);
lean_dec_ref_known(v_fst_4661_, 1);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 0, v_val_4667_);
v___x_4669_ = v___x_4659_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_val_4667_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
v_a_4672_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4656_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4656_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_4612_ = stack[0].m_obj;
lean_object* v_config_4613_ = stack[1].m_obj;
lean_object* v_mvarId_4614_ = stack[2].m_obj;
lean_object* v_n_4615_ = stack[3].m_obj;
lean_object* v_b_4616_ = stack[4].m_obj;
lean_object* v___y_4617_ = stack[5].m_obj;
lean_object* v___y_4618_ = stack[6].m_obj;
lean_object* v___y_4619_ = stack[7].m_obj;
lean_object* v___y_4620_ = stack[8].m_obj;
lean_object* v_res_4680_;
v_res_4680_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4612_, v_config_4613_, v_mvarId_4614_, v_n_4615_, v_b_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
stack->m_obj
 = v_res_4680_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4681_, lean_object* v_config_4682_, lean_object* v_mvarId_4683_, lean_object* v_as_4684_, size_t v_sz_4685_, size_t v_i_4686_, lean_object* v_b_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
uint8_t v___x_4693_; 
v___x_4693_ = lean_usize_dec_lt(v_i_4686_, v_sz_4685_);
if (v___x_4693_ == 0)
{
lean_object* v___x_4694_; 
lean_dec(v_mvarId_4683_);
lean_dec_ref(v_config_4682_);
v___x_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4694_, 0, v_b_4687_);
return v___x_4694_;
}
else
{
lean_object* v_snd_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4729_; 
v_snd_4695_ = lean_ctor_get(v_b_4687_, 1);
v_isSharedCheck_4729_ = !lean_is_exclusive(v_b_4687_);
if (v_isSharedCheck_4729_ == 0)
{
lean_object* v_unused_4730_; 
v_unused_4730_ = lean_ctor_get(v_b_4687_, 0);
lean_dec(v_unused_4730_);
v___x_4697_ = v_b_4687_;
v_isShared_4698_ = v_isSharedCheck_4729_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_snd_4695_);
lean_dec(v_b_4687_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4729_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4699_; lean_object* v_a_4700_; lean_object* v___x_4701_; 
v___x_4699_ = lean_box(0);
v_a_4700_ = lean_array_uget_borrowed(v_as_4684_, v_i_4686_);
lean_inc(v_snd_4695_);
lean_inc(v_mvarId_4683_);
lean_inc_ref(v_config_4682_);
v___x_4701_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4681_, v_config_4682_, v_mvarId_4683_, v_a_4700_, v_snd_4695_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4720_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4704_ = v___x_4701_;
v_isShared_4705_ = v_isSharedCheck_4720_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4701_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4720_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
if (lean_obj_tag(v_a_4702_) == 0)
{
lean_object* v___x_4706_; lean_object* v___x_4708_; 
lean_dec(v_mvarId_4683_);
lean_dec_ref(v_config_4682_);
v___x_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4706_, 0, v_a_4702_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 0, v___x_4706_);
v___x_4708_ = v___x_4697_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4706_);
lean_ctor_set(v_reuseFailAlloc_4712_, 1, v_snd_4695_);
v___x_4708_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4710_; 
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 0, v___x_4708_);
v___x_4710_ = v___x_4704_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v___x_4708_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; 
lean_del_object(v___x_4704_);
lean_dec(v_snd_4695_);
v_a_4713_ = lean_ctor_get(v_a_4702_, 0);
lean_inc(v_a_4713_);
lean_dec_ref_known(v_a_4702_, 1);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 1, v_a_4713_);
lean_ctor_set(v___x_4697_, 0, v___x_4699_);
v___x_4715_ = v___x_4697_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4699_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v_a_4713_);
v___x_4715_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
size_t v___x_4716_; size_t v___x_4717_; 
v___x_4716_ = ((size_t)1ULL);
v___x_4717_ = lean_usize_add(v_i_4686_, v___x_4716_);
v_i_4686_ = v___x_4717_;
v_b_4687_ = v___x_4715_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_del_object(v___x_4697_);
lean_dec(v_snd_4695_);
lean_dec(v_mvarId_4683_);
lean_dec_ref(v_config_4682_);
v_a_4721_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4701_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4701_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_4681_ = stack[0].m_obj;
lean_object* v_config_4682_ = stack[1].m_obj;
lean_object* v_mvarId_4683_ = stack[2].m_obj;
lean_object* v_as_4684_ = stack[3].m_obj;
size_t v_sz_4685_ = stack[4].m_num;
size_t v_i_4686_ = stack[5].m_num;
lean_object* v_b_4687_ = stack[6].m_obj;
lean_object* v___y_4688_ = stack[7].m_obj;
lean_object* v___y_4689_ = stack[8].m_obj;
lean_object* v___y_4690_ = stack[9].m_obj;
lean_object* v___y_4691_ = stack[10].m_obj;
lean_object* v_res_4731_;
v_res_4731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4681_, v_config_4682_, v_mvarId_4683_, v_as_4684_, v_sz_4685_, v_i_4686_, v_b_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
stack->m_obj
 = v_res_4731_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4732_, lean_object* v_config_4733_, lean_object* v_mvarId_4734_, lean_object* v_as_4735_, lean_object* v_sz_4736_, lean_object* v_i_4737_, lean_object* v_b_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_){
_start:
{
size_t v_sz_boxed_4744_; size_t v_i_boxed_4745_; lean_object* v_res_4746_; 
v_sz_boxed_4744_ = lean_unbox_usize(v_sz_4736_);
lean_dec(v_sz_4736_);
v_i_boxed_4745_ = lean_unbox_usize(v_i_4737_);
lean_dec(v_i_4737_);
v_res_4746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4732_, v_config_4733_, v_mvarId_4734_, v_as_4735_, v_sz_boxed_4744_, v_i_boxed_4745_, v_b_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_);
lean_dec(v___y_4742_);
lean_dec_ref(v___y_4741_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec_ref(v_as_4735_);
lean_dec_ref(v_init_4732_);
return v_res_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4747_, lean_object* v_config_4748_, lean_object* v_mvarId_4749_, lean_object* v_n_4750_, lean_object* v_b_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4747_, v_config_4748_, v_mvarId_4749_, v_n_4750_, v_b_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec(v___y_4753_);
lean_dec_ref(v___y_4752_);
lean_dec_ref(v_n_4750_);
lean_dec_ref(v_init_4747_);
return v_res_4757_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4758_, lean_object* v_mvarId_4759_, lean_object* v_t_4760_, lean_object* v_init_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v_root_4767_; lean_object* v_tail_4768_; lean_object* v___x_4769_; 
v_root_4767_ = lean_ctor_get(v_t_4760_, 0);
v_tail_4768_ = lean_ctor_get(v_t_4760_, 1);
lean_inc(v_mvarId_4759_);
lean_inc_ref(v_config_4758_);
lean_inc_ref(v_init_4761_);
v___x_4769_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4761_, v_config_4758_, v_mvarId_4759_, v_root_4767_, v_init_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec_ref(v_init_4761_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4806_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4772_ = v___x_4769_;
v_isShared_4773_ = v_isSharedCheck_4806_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4769_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4806_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
if (lean_obj_tag(v_a_4770_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4776_; 
lean_dec(v_mvarId_4759_);
lean_dec_ref(v_config_4758_);
v_a_4774_ = lean_ctor_get(v_a_4770_, 0);
lean_inc(v_a_4774_);
lean_dec_ref_known(v_a_4770_, 1);
if (v_isShared_4773_ == 0)
{
lean_ctor_set(v___x_4772_, 0, v_a_4774_);
v___x_4776_ = v___x_4772_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4774_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; size_t v_sz_4781_; size_t v___x_4782_; lean_object* v___x_4783_; 
lean_del_object(v___x_4772_);
v_a_4778_ = lean_ctor_get(v_a_4770_, 0);
lean_inc(v_a_4778_);
lean_dec_ref_known(v_a_4770_, 1);
v___x_4779_ = lean_box(0);
v___x_4780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
lean_ctor_set(v___x_4780_, 1, v_a_4778_);
v_sz_4781_ = lean_array_size(v_tail_4768_);
v___x_4782_ = ((size_t)0ULL);
v___x_4783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4758_, v_mvarId_4759_, v_tail_4768_, v_sz_4781_, v___x_4782_, v___x_4780_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4797_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4786_ = v___x_4783_;
v_isShared_4787_ = v_isSharedCheck_4797_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4797_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v_fst_4788_; 
v_fst_4788_ = lean_ctor_get(v_a_4784_, 0);
if (lean_obj_tag(v_fst_4788_) == 0)
{
lean_object* v_snd_4789_; lean_object* v___x_4791_; 
v_snd_4789_ = lean_ctor_get(v_a_4784_, 1);
lean_inc(v_snd_4789_);
lean_dec(v_a_4784_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 0, v_snd_4789_);
v___x_4791_ = v___x_4786_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_snd_4789_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
else
{
lean_object* v_val_4793_; lean_object* v___x_4795_; 
lean_inc_ref(v_fst_4788_);
lean_dec(v_a_4784_);
v_val_4793_ = lean_ctor_get(v_fst_4788_, 0);
lean_inc(v_val_4793_);
lean_dec_ref_known(v_fst_4788_, 1);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 0, v_val_4793_);
v___x_4795_ = v___x_4786_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_val_4793_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
v_a_4798_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4783_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4783_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
lean_dec(v_mvarId_4759_);
lean_dec_ref(v_config_4758_);
v_a_4807_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4769_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4769_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_4758_ = stack[0].m_obj;
lean_object* v_mvarId_4759_ = stack[1].m_obj;
lean_object* v_t_4760_ = stack[2].m_obj;
lean_object* v_init_4761_ = stack[3].m_obj;
lean_object* v___y_4762_ = stack[4].m_obj;
lean_object* v___y_4763_ = stack[5].m_obj;
lean_object* v___y_4764_ = stack[6].m_obj;
lean_object* v___y_4765_ = stack[7].m_obj;
lean_object* v_res_4815_;
v_res_4815_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4758_, v_mvarId_4759_, v_t_4760_, v_init_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
stack->m_obj
 = v_res_4815_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4816_, lean_object* v_mvarId_4817_, lean_object* v_t_4818_, lean_object* v_init_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4816_, v_mvarId_4817_, v_t_4818_, v_init_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec(v___y_4821_);
lean_dec_ref(v___y_4820_);
lean_dec_ref(v_t_4818_);
return v_res_4825_;
}
}
lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4826_, lean_object* v___x_4827_, lean_object* v_config_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v___x_4834_; 
lean_inc(v_mvarId_4826_);
v___x_4834_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4826_, v___x_4827_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_object* v___x_4835_; 
lean_dec_ref_known(v___x_4834_, 1);
lean_inc(v_mvarId_4826_);
v___x_4835_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4826_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4869_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4838_ = v___x_4835_;
v_isShared_4839_ = v_isSharedCheck_4869_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4835_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4869_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
uint8_t v___x_4840_; 
v___x_4840_ = lean_unbox(v_a_4836_);
if (v___x_4840_ == 0)
{
lean_object* v_lctx_4841_; lean_object* v_decls_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
lean_del_object(v___x_4838_);
v_lctx_4841_ = lean_ctor_get(v___y_4829_, 2);
v_decls_4842_ = lean_ctor_get(v_lctx_4841_, 1);
v___x_4843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4844_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4828_, v_mvarId_4826_, v_decls_4842_, v___x_4843_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4857_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4847_ = v___x_4844_;
v_isShared_4848_ = v_isSharedCheck_4857_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4844_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4857_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v_fst_4849_; 
v_fst_4849_ = lean_ctor_get(v_a_4845_, 0);
lean_inc(v_fst_4849_);
lean_dec(v_a_4845_);
if (lean_obj_tag(v_fst_4849_) == 0)
{
lean_object* v___x_4851_; 
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v_a_4836_);
v___x_4851_ = v___x_4847_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4836_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
else
{
lean_object* v_val_4853_; lean_object* v___x_4855_; 
lean_dec(v_a_4836_);
v_val_4853_ = lean_ctor_get(v_fst_4849_, 0);
lean_inc(v_val_4853_);
lean_dec_ref_known(v_fst_4849_, 1);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v_val_4853_);
v___x_4855_ = v___x_4847_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_val_4853_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
else
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4865_; 
lean_dec(v_a_4836_);
v_a_4858_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4860_ = v___x_4844_;
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4844_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4863_; 
if (v_isShared_4861_ == 0)
{
v___x_4863_ = v___x_4860_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4858_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
}
}
else
{
lean_object* v___x_4867_; 
lean_dec_ref(v_config_4828_);
lean_dec(v_mvarId_4826_);
if (v_isShared_4839_ == 0)
{
v___x_4867_ = v___x_4838_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4836_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
else
{
lean_dec_ref(v_config_4828_);
lean_dec(v_mvarId_4826_);
return v___x_4835_;
}
}
else
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4877_; 
lean_dec_ref(v_config_4828_);
lean_dec(v_mvarId_4826_);
v_a_4870_ = lean_ctor_get(v___x_4834_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4834_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4872_ = v___x_4834_;
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4834_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4875_; 
if (v_isShared_4873_ == 0)
{
v___x_4875_ = v___x_4872_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_a_4870_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_contradictionCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4826_ = stack[0].m_obj;
lean_object* v___x_4827_ = stack[1].m_obj;
lean_object* v_config_4828_ = stack[2].m_obj;
lean_object* v___y_4829_ = stack[3].m_obj;
lean_object* v___y_4830_ = stack[4].m_obj;
lean_object* v___y_4831_ = stack[5].m_obj;
lean_object* v___y_4832_ = stack[6].m_obj;
lean_object* v_res_4878_;
v_res_4878_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4826_, v___x_4827_, v_config_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_);
stack->m_obj
 = v_res_4878_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4879_, lean_object* v___x_4880_, lean_object* v_config_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4879_, v___x_4880_, v_config_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
lean_dec(v___y_4885_);
lean_dec_ref(v___y_4884_);
lean_dec(v___y_4883_);
lean_dec_ref(v___y_4882_);
return v_res_4887_;
}
}
lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4890_, lean_object* v_config_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_){
_start:
{
lean_object* v___x_4897_; lean_object* v___f_4898_; lean_object* v___x_4899_; 
v___x_4897_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4890_);
v___f_4898_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4898_, 0, v_mvarId_4890_);
lean_closure_set(v___f_4898_, 1, v___x_4897_);
lean_closure_set(v___f_4898_, 2, v_config_4891_);
v___x_4899_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4890_, v___f_4898_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_);
return v___x_4899_;
}
}
LEAN_EXPORT void l_Lean_MVarId_contradictionCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4890_ = stack[0].m_obj;
lean_object* v_config_4891_ = stack[1].m_obj;
lean_object* v_a_4892_ = stack[2].m_obj;
lean_object* v_a_4893_ = stack[3].m_obj;
lean_object* v_a_4894_ = stack[4].m_obj;
lean_object* v_a_4895_ = stack[5].m_obj;
lean_object* v_res_4900_;
v_res_4900_ = l_Lean_MVarId_contradictionCore(v_mvarId_4890_, v_config_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_);
stack->m_obj
 = v_res_4900_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4901_, lean_object* v_config_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_Lean_MVarId_contradictionCore(v_mvarId_4901_, v_config_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
lean_dec(v_a_4906_);
lean_dec_ref(v_a_4905_);
lean_dec(v_a_4904_);
lean_dec_ref(v_a_4903_);
return v_res_4908_;
}
}
lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4909_, lean_object* v_config_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v___x_4916_; 
lean_inc(v_mvarId_4909_);
v___x_4916_ = l_Lean_MVarId_contradictionCore(v_mvarId_4909_, v_config_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4929_; 
v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4919_ = v___x_4916_;
v_isShared_4920_ = v_isSharedCheck_4929_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4916_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4929_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
uint8_t v___x_4921_; 
v___x_4921_ = lean_unbox(v_a_4917_);
lean_dec(v_a_4917_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
lean_del_object(v___x_4919_);
v___x_4922_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4923_ = lean_box(0);
v___x_4924_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4922_, v_mvarId_4909_, v___x_4923_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
return v___x_4924_;
}
else
{
lean_object* v___x_4925_; lean_object* v___x_4927_; 
lean_dec(v_mvarId_4909_);
v___x_4925_ = lean_box(0);
if (v_isShared_4920_ == 0)
{
lean_ctor_set(v___x_4919_, 0, v___x_4925_);
v___x_4927_ = v___x_4919_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4925_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
lean_dec(v_mvarId_4909_);
v_a_4930_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4916_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4916_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_contradiction_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4909_ = stack[0].m_obj;
lean_object* v_config_4910_ = stack[1].m_obj;
lean_object* v_a_4911_ = stack[2].m_obj;
lean_object* v_a_4912_ = stack[3].m_obj;
lean_object* v_a_4913_ = stack[4].m_obj;
lean_object* v_a_4914_ = stack[5].m_obj;
lean_object* v_res_4938_;
v_res_4938_ = l_Lean_MVarId_contradiction(v_mvarId_4909_, v_config_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
stack->m_obj
 = v_res_4938_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4939_, lean_object* v_config_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_MVarId_contradiction(v_mvarId_4939_, v_config_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
return v_res_4946_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5009_; uint8_t v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5009_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_5010_ = 0;
v___x_5011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_5012_ = l_Lean_registerTraceClass(v___x_5009_, v___x_5010_, v___x_5011_);
return v___x_5012_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5013_;
v_res_5013_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5013_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_5015_;
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
