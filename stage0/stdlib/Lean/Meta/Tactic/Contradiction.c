// Lean compiler output
// Module: Lean.Meta.Tactic.Contradiction
// Imports: public import Lean.Meta.Tactic.Assumption public import Lean.Meta.Tactic.Cases public import Lean.Meta.Tactic.Apply import Lean.Meta.HasNotBit import Lean.Meta.Tactic.Simp.Rewrite import Lean.Meta.LitValues
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
lean_object* l_Lean_Meta_floatLitValuesEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_sz_boxed_674_; size_t v___x_15996__boxed_675_; uint8_t v___x_15998__boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v___x_15996__boxed_675_ = lean_unbox_usize(v___x_665_);
lean_dec(v___x_665_);
v___x_15998__boxed_676_ = lean_unbox(v___x_667_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_661_, v_mvarId_662_, v_fields_663_, v_sz_boxed_674_, v___x_15996__boxed_675_, v___x_666_, v___x_15998__boxed_676_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
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
uint8_t v___x_16118__boxed_880_; uint8_t v___x_16121__boxed_881_; lean_object* v_res_882_; 
v___x_16118__boxed_880_ = lean_unbox(v___x_870_);
v___x_16121__boxed_881_ = lean_unbox(v___x_873_);
v_res_882_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_867_, v_fvarId_868_, v___x_869_, v___x_16118__boxed_880_, v___x_871_, v_val_872_, v___x_16121__boxed_881_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
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
lean_dec_ref(v_e_1274_);
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
v___x_1733_ = lean_unsigned_to_nat(121u);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(lean_object* v_x_1789_, lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1789_) == 0)
{
if (lean_obj_tag(v_x_1790_) == 0)
{
uint8_t v___x_1791_; 
v___x_1791_ = 1;
return v___x_1791_;
}
else
{
uint8_t v___x_1792_; 
v___x_1792_ = 0;
return v___x_1792_;
}
}
else
{
if (lean_obj_tag(v_x_1790_) == 0)
{
uint8_t v___x_1793_; 
v___x_1793_ = 0;
return v___x_1793_;
}
else
{
lean_object* v_val_1794_; uint8_t v___x_1795_; 
v_val_1794_ = lean_ctor_get(v_x_1790_, 0);
v___x_1795_ = lean_unbox(v_val_1794_);
if (v___x_1795_ == 0)
{
lean_object* v_val_1796_; uint8_t v___x_1797_; 
v_val_1796_ = lean_ctor_get(v_x_1789_, 0);
v___x_1797_ = lean_unbox(v_val_1796_);
if (v___x_1797_ == 0)
{
uint8_t v___x_1798_; 
v___x_1798_ = 1;
return v___x_1798_;
}
else
{
uint8_t v___x_1799_; 
v___x_1799_ = lean_unbox(v_val_1794_);
return v___x_1799_;
}
}
else
{
lean_object* v_val_1800_; uint8_t v___x_1801_; 
v_val_1800_ = lean_ctor_get(v_x_1789_, 0);
v___x_1801_ = lean_unbox(v_val_1800_);
return v___x_1801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0___boxed(lean_object* v_x_1802_, lean_object* v_x_1803_){
_start:
{
uint8_t v_res_1804_; lean_object* v_r_1805_; 
v_res_1804_ = l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(v_x_1802_, v_x_1803_);
lean_dec(v_x_1803_);
lean_dec(v_x_1802_);
v_r_1805_ = lean_box(v_res_1804_);
return v_r_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0(lean_object* v_lhs_1809_, lean_object* v_rhs_1810_, lean_object* v_mvarId_1811_, lean_object* v_h_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
lean_inc_ref(v_rhs_1810_);
lean_inc_ref(v_lhs_1809_);
v___x_1818_ = l_Lean_Meta_floatLitValuesEq_x3f(v_lhs_1809_, v_rhs_1810_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1881_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1881_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1881_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
uint8_t v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = 0;
v___x_1824_ = ((lean_object*)(l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___closed__0));
v___x_1825_ = l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(v_a_1819_, v___x_1824_);
lean_dec(v_a_1819_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_dec_ref(v_h_1812_);
lean_dec(v_mvarId_1811_);
lean_dec_ref(v_rhs_1810_);
lean_dec_ref(v_lhs_1809_);
v___x_1826_ = lean_box(v___x_1823_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1826_);
v___x_1828_ = v___x_1821_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
else
{
lean_object* v___x_1830_; 
lean_del_object(v___x_1821_);
v___x_1830_ = l_Lean_Meta_mkEq(v_lhs_1809_, v_rhs_1810_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = l_Lean_mkNot(v_a_1831_);
v___x_1833_ = l_Lean_Meta_mkDecideProof(v___x_1832_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
lean_inc(v_mvarId_1811_);
v___x_1835_ = l_Lean_MVarId_getType(v_mvarId_1811_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = l_Lean_Meta_mkAbsurd(v_a_1836_, v_h_1812_, v_a_1834_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1847_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1839_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1811_, v_a_1838_, v___y_1814_);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v___x_1839_, 0);
lean_dec(v_unused_1848_);
v___x_1841_ = v___x_1839_;
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
else
{
lean_dec(v___x_1839_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = lean_box(v___x_1825_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_mvarId_1811_);
v_a_1849_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1837_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1837_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1834_);
lean_dec_ref(v_h_1812_);
lean_dec(v_mvarId_1811_);
v_a_1857_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1835_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1835_);
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
lean_dec_ref(v_h_1812_);
lean_dec(v_mvarId_1811_);
v_a_1865_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1833_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1833_);
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
lean_dec_ref(v_h_1812_);
lean_dec(v_mvarId_1811_);
v_a_1873_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1830_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1830_);
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
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v_h_1812_);
lean_dec(v_mvarId_1811_);
lean_dec_ref(v_rhs_1810_);
lean_dec_ref(v_lhs_1809_);
v_a_1882_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1818_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1818_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___boxed(lean_object* v_lhs_1890_, lean_object* v_rhs_1891_, lean_object* v_mvarId_1892_, lean_object* v_h_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_MVarId_closeIfDistinctFloatLits___lam__0(v_lhs_1890_, v_rhs_1891_, v_mvarId_1892_, v_h_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits(lean_object* v_mvarId_1900_, lean_object* v_h_1901_, lean_object* v_lhs_1902_, lean_object* v_rhs_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___f_1909_; lean_object* v___x_1910_; 
lean_inc(v_mvarId_1900_);
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1909_, 0, v_lhs_1902_);
lean_closure_set(v___f_1909_, 1, v_rhs_1903_);
lean_closure_set(v___f_1909_, 2, v_mvarId_1900_);
lean_closure_set(v___f_1909_, 3, v_h_1901_);
v___x_1910_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1900_, v___f_1909_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___boxed(lean_object* v_mvarId_1911_, lean_object* v_h_1912_, lean_object* v_lhs_1913_, lean_object* v_rhs_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_MVarId_closeIfDistinctFloatLits(v_mvarId_1911_, v_h_1912_, v_lhs_1913_, v_rhs_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
return v_res_1920_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_box(0);
v___x_1933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1934_ = l_Lean_mkConst(v___x_1933_, v___x_1932_);
return v___x_1934_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1935_; lean_object* v_dummy_1936_; 
v___x_1935_ = lean_box(0);
v_dummy_1936_ = l_Lean_Expr_sort___override(v___x_1935_);
return v_dummy_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1937_, lean_object* v_mvarId_1938_, lean_object* v_as_1939_, size_t v_sz_1940_, size_t v_i_1941_, lean_object* v_b_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_usize_dec_lt(v_i_1941_, v_sz_1940_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_b_1942_);
return v___x_1949_;
}
else
{
lean_object* v_snd_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_2531_; 
v_snd_1950_ = lean_ctor_get(v_b_1942_, 1);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_b_1942_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; 
v_unused_2532_ = lean_ctor_get(v_b_1942_, 0);
lean_dec(v_unused_2532_);
v___x_1952_ = v_b_1942_;
v_isShared_1953_ = v_isSharedCheck_2531_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_snd_1950_);
lean_dec(v_b_1942_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_2531_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v_a_1955_; lean_object* v___x_1961_; lean_object* v_a_1963_; lean_object* v_a_1968_; 
v___x_1961_ = lean_box(0);
v_a_1968_ = lean_array_uget(v_as_1939_, v_i_1941_);
if (lean_obj_tag(v_a_1968_) == 0)
{
lean_del_object(v___x_1952_);
v_a_1963_ = v_snd_1950_;
goto v___jp_1962_;
}
else
{
lean_object* v_val_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2530_; 
v_val_1969_ = lean_ctor_get(v_a_1968_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_1971_ = v_a_1968_;
v_isShared_1972_ = v_isSharedCheck_2530_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_val_1969_);
lean_dec(v_a_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2530_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___y_1976_; uint8_t v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; uint8_t v___x_2001_; 
v___x_1973_ = lean_box(0);
v___x_1974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2001_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1969_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; uint8_t v___y_2004_; uint8_t v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; uint8_t v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; uint8_t v___y_2032_; lean_object* v_a_2033_; uint8_t v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; uint8_t v___y_2045_; lean_object* v___y_2046_; uint8_t v___y_2083_; uint8_t v_isHEq_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; uint8_t v_isEq_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___x_2467_; 
v___x_2002_ = l_Lean_LocalDecl_type(v_val_1969_);
lean_inc_ref(v___x_2002_);
v___x_2467_ = l_Lean_Meta_matchNot_x3f(v___x_2002_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2467_, 1);
if (lean_obj_tag(v_a_2468_) == 1)
{
lean_object* v_val_2469_; lean_object* v___x_2470_; 
v_val_2469_ = lean_ctor_get(v_a_2468_, 0);
lean_inc(v_val_2469_);
lean_dec_ref_known(v_a_2468_, 1);
v___x_2470_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2469_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
if (lean_obj_tag(v_a_2471_) == 1)
{
lean_object* v_val_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec_ref(v_config_1937_);
v_val_2472_ = lean_ctor_get(v_a_2471_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_a_2471_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2474_ = v_a_2471_;
v_isShared_2475_ = v_isSharedCheck_2513_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_val_2472_);
lean_dec(v_a_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2513_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; 
lean_inc(v_mvarId_1938_);
v___x_2476_ = l_Lean_MVarId_getType(v_mvarId_1938_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
v___x_2478_ = l_Lean_LocalDecl_toExpr(v_val_1969_);
v___x_2479_ = l_Lean_mkFVar(v_val_2472_);
v___x_2480_ = l_Lean_Expr_app___override(v___x_2478_, v___x_2479_);
v___x_2481_ = l_Lean_Meta_mkFalseElim(v_a_2477_, v___x_2480_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2483_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v___x_2483_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1938_, v_a_2482_, v___y_1944_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
lean_dec_ref_known(v___x_2483_, 1);
v___x_2484_ = lean_box(v___x_1948_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2484_);
v___x_2486_ = v___x_2474_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v___x_1973_);
v_a_1955_ = v___x_2487_;
goto v___jp_1954_;
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_del_object(v___x_2474_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_2489_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2483_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2483_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_del_object(v___x_2474_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2497_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2481_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2481_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_del_object(v___x_2474_);
lean_dec(v_val_2472_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2505_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2476_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2476_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
else
{
lean_dec(v_a_2471_);
v___y_2333_ = v___y_1943_;
v___y_2334_ = v___y_1944_;
v___y_2335_ = v___y_1945_;
v___y_2336_ = v___y_1946_;
goto v___jp_2332_;
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2514_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2470_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2470_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_dec(v_a_2468_);
v___y_2333_ = v___y_1943_;
v___y_2334_ = v___y_1944_;
v___y_2335_ = v___y_1945_;
v___y_2336_ = v___y_1946_;
goto v___jp_2332_;
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2522_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2467_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2467_);
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
v___jp_2003_:
{
uint8_t v_genDiseq_2010_; 
v_genDiseq_2010_ = lean_ctor_get_uint8(v_config_1937_, sizeof(void*)*1 + 2);
if (v_genDiseq_2010_ == 0)
{
lean_dec_ref(v___x_2002_);
v___y_1976_ = v___y_2004_;
v___y_1977_ = v___y_2005_;
v___y_1978_ = v___y_2006_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_2008_;
v___y_1981_ = v___y_2009_;
goto v___jp_1975_;
}
else
{
uint8_t v___x_2011_; 
v___x_2011_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2002_);
lean_dec_ref(v___x_2002_);
if (v___x_2011_ == 0)
{
v___y_1976_ = v___y_2004_;
v___y_1977_ = v___y_2005_;
v___y_1978_ = v___y_2006_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_2008_;
v___y_1981_ = v___y_2009_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2012_; 
lean_inc(v_val_1969_);
lean_inc(v_mvarId_1938_);
v___x_2012_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1938_, v_val_1969_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; uint8_t v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = lean_unbox(v_a_2013_);
lean_dec(v_a_2013_);
if (v___x_2014_ == 0)
{
v___y_1976_ = v___y_2004_;
v___y_1977_ = v___y_2005_;
v___y_1978_ = v___y_2006_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_2008_;
v___y_1981_ = v___y_2009_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v___x_2015_ = lean_box(v___x_1948_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v___x_1973_);
v_a_1955_ = v___x_2017_;
goto v___jp_1954_;
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2018_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2012_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2012_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
}
v___jp_2026_:
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_Exception_isInterrupt(v_a_2033_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; 
lean_inc_ref(v_a_2033_);
v___x_2035_ = l_Lean_Exception_isRuntime(v_a_2033_);
if (v___x_2035_ == 0)
{
lean_dec_ref(v_a_2033_);
v___y_2004_ = v___y_2027_;
v___y_2005_ = v___y_2032_;
v___y_2006_ = v___y_2030_;
v___y_2007_ = v___y_2029_;
v___y_2008_ = v___y_2031_;
v___y_2009_ = v___y_2028_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2036_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_a_2033_);
return v___x_2036_;
}
}
else
{
lean_object* v___x_2037_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v_a_2033_);
return v___x_2037_;
}
}
v___jp_2038_:
{
if (lean_obj_tag(v___y_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_a_2047_ = lean_ctor_get(v___y_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___y_2046_, 1);
v___x_2048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2049_ = l_Lean_Expr_isConstOf(v_a_2047_, v___x_2048_);
lean_dec(v_a_2047_);
if (v___x_2049_ == 0)
{
lean_dec_ref(v___y_2040_);
v___y_2004_ = v___y_2039_;
v___y_2005_ = v___y_2045_;
v___y_2006_ = v___y_2043_;
v___y_2007_ = v___y_2042_;
v___y_2008_ = v___y_2044_;
v___y_2009_ = v___y_2041_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2050_; 
lean_inc_ref(v___y_2040_);
v___x_2050_ = l_Lean_Meta_mkEqRefl(v___y_2040_, v___y_2043_, v___y_2042_, v___y_2044_, v___y_2041_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; lean_object* v_dummy_2053_; lean_object* v_nargs_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2053_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2054_ = l_Lean_Expr_getAppNumArgs(v___y_2040_);
lean_inc(v_nargs_2054_);
v___x_2055_ = lean_mk_array(v_nargs_2054_, v_dummy_2053_);
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = lean_nat_sub(v_nargs_2054_, v___x_2056_);
lean_dec(v_nargs_2054_);
v___x_2058_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2040_, v___x_2055_, v___x_2057_);
v___x_2059_ = lean_array_push(v___x_2058_, v_a_2051_);
v___x_2060_ = l_Lean_mkAppN(v___x_2052_, v___x_2059_);
lean_dec_ref(v___x_2059_);
lean_inc(v_mvarId_1938_);
v___x_2061_ = l_Lean_MVarId_getType(v_mvarId_1938_, v___y_2043_, v___y_2042_, v___y_2044_, v___y_2041_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
lean_inc(v_val_1969_);
v___x_2063_ = l_Lean_LocalDecl_toExpr(v_val_1969_);
v___x_2064_ = l_Lean_Meta_mkAbsurd(v_a_2062_, v___x_2063_, v___x_2060_, v___y_2043_, v___y_2042_, v___y_2044_, v___y_2041_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2066_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
lean_inc(v_mvarId_1938_);
v___x_2066_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1938_, v_a_2065_, v___y_2042_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v___x_2066_, 0);
lean_dec(v_unused_2076_);
v___x_2068_ = v___x_2066_;
v_isShared_2069_ = v_isSharedCheck_2075_;
goto v_resetjp_2067_;
}
else
{
lean_dec(v___x_2066_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2075_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_box(v___x_1948_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 1);
lean_ctor_set(v___x_2068_, 0, v___x_2070_);
v___x_2072_ = v___x_2068_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set(v___x_2073_, 1, v___x_1973_);
v_a_1955_ = v___x_2073_;
goto v___jp_1954_;
}
}
}
else
{
lean_object* v_a_2077_; 
v_a_2077_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2066_, 1);
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2041_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v___y_2032_ = v___y_2045_;
v_a_2033_ = v_a_2077_;
goto v___jp_2026_;
}
}
else
{
lean_object* v_a_2078_; 
v_a_2078_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2064_, 1);
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2041_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v___y_2032_ = v___y_2045_;
v_a_2033_ = v_a_2078_;
goto v___jp_2026_;
}
}
else
{
lean_object* v_a_2079_; 
lean_dec_ref(v___x_2060_);
v_a_2079_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2061_, 1);
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2041_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v___y_2032_ = v___y_2045_;
v_a_2033_ = v_a_2079_;
goto v___jp_2026_;
}
}
else
{
lean_object* v_a_2080_; 
lean_dec_ref(v___y_2040_);
v_a_2080_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2050_, 1);
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2041_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v___y_2032_ = v___y_2045_;
v_a_2033_ = v_a_2080_;
goto v___jp_2026_;
}
}
}
else
{
lean_object* v_a_2081_; 
lean_dec_ref(v___y_2040_);
v_a_2081_ = lean_ctor_get(v___y_2046_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___y_2046_, 1);
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2041_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v___y_2032_ = v___y_2045_;
v_a_2033_ = v_a_2081_;
goto v___jp_2026_;
}
}
v___jp_2082_:
{
uint8_t v_useDecide_2089_; 
v_useDecide_2089_ = lean_ctor_get_uint8(v_config_1937_, sizeof(void*)*1);
if (v_useDecide_2089_ == 0)
{
v___y_2004_ = v___y_2083_;
v___y_2005_ = v_isHEq_2084_;
v___y_2006_ = v___y_2085_;
v___y_2007_ = v___y_2086_;
v___y_2008_ = v___y_2087_;
v___y_2009_ = v___y_2088_;
goto v___jp_2003_;
}
else
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_Expr_hasFVar(v___x_2002_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_inc_ref(v___x_2002_);
v___x_2091_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2002_, v___y_2086_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; uint8_t v___x_2093_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = l_Lean_Expr_hasMVar(v_a_2092_);
if (v___x_2093_ == 0)
{
uint8_t v___x_2094_; 
v___x_2094_ = l_Lean_Expr_hasFVar(v_a_2092_);
lean_dec(v_a_2092_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; 
lean_inc_ref(v___x_2002_);
v___x_2095_ = l_Lean_Meta_mkDecide(v___x_2002_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; uint8_t v_transparency_2098_; uint8_t v___x_2099_; uint8_t v___x_2100_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = l_Lean_Meta_Context_config(v___y_2085_);
v_transparency_2098_ = lean_ctor_get_uint8(v___x_2097_, 9);
lean_dec_ref(v___x_2097_);
v___x_2099_ = 1;
v___x_2100_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2098_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v_keyedConfig_2101_; uint8_t v_trackZetaDelta_2102_; lean_object* v_zetaDeltaSet_2103_; lean_object* v_lctx_2104_; lean_object* v_localInstances_2105_; lean_object* v_defEqCtx_x3f_2106_; lean_object* v_synthPendingDepth_2107_; lean_object* v_customCanUnfoldPredicate_x3f_2108_; uint8_t v_univApprox_2109_; uint8_t v_inTypeClassResolution_2110_; uint8_t v_cacheInferType_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_keyedConfig_2101_ = lean_ctor_get(v___y_2085_, 0);
v_trackZetaDelta_2102_ = lean_ctor_get_uint8(v___y_2085_, sizeof(void*)*7);
v_zetaDeltaSet_2103_ = lean_ctor_get(v___y_2085_, 1);
v_lctx_2104_ = lean_ctor_get(v___y_2085_, 2);
v_localInstances_2105_ = lean_ctor_get(v___y_2085_, 3);
v_defEqCtx_x3f_2106_ = lean_ctor_get(v___y_2085_, 4);
v_synthPendingDepth_2107_ = lean_ctor_get(v___y_2085_, 5);
v_customCanUnfoldPredicate_x3f_2108_ = lean_ctor_get(v___y_2085_, 6);
v_univApprox_2109_ = lean_ctor_get_uint8(v___y_2085_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2110_ = lean_ctor_get_uint8(v___y_2085_, sizeof(void*)*7 + 2);
v_cacheInferType_2111_ = lean_ctor_get_uint8(v___y_2085_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2101_);
v___x_2112_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2099_, v_keyedConfig_2101_);
lean_inc(v_customCanUnfoldPredicate_x3f_2108_);
lean_inc(v_synthPendingDepth_2107_);
lean_inc(v_defEqCtx_x3f_2106_);
lean_inc_ref(v_localInstances_2105_);
lean_inc_ref(v_lctx_2104_);
lean_inc(v_zetaDeltaSet_2103_);
v___x_2113_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_zetaDeltaSet_2103_);
lean_ctor_set(v___x_2113_, 2, v_lctx_2104_);
lean_ctor_set(v___x_2113_, 3, v_localInstances_2105_);
lean_ctor_set(v___x_2113_, 4, v_defEqCtx_x3f_2106_);
lean_ctor_set(v___x_2113_, 5, v_synthPendingDepth_2107_);
lean_ctor_set(v___x_2113_, 6, v_customCanUnfoldPredicate_x3f_2108_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*7, v_trackZetaDelta_2102_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*7 + 1, v_univApprox_2109_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2110_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*7 + 3, v_cacheInferType_2111_);
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2087_);
lean_inc(v___y_2086_);
lean_inc(v_a_2096_);
v___x_2114_ = lean_whnf(v_a_2096_, v___x_2113_, v___y_2086_, v___y_2087_, v___y_2088_);
v___y_2039_ = v___y_2083_;
v___y_2040_ = v_a_2096_;
v___y_2041_ = v___y_2088_;
v___y_2042_ = v___y_2086_;
v___y_2043_ = v___y_2085_;
v___y_2044_ = v___y_2087_;
v___y_2045_ = v_isHEq_2084_;
v___y_2046_ = v___x_2114_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2115_; 
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2087_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
lean_inc(v_a_2096_);
v___x_2115_ = lean_whnf(v_a_2096_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
v___y_2039_ = v___y_2083_;
v___y_2040_ = v_a_2096_;
v___y_2041_ = v___y_2088_;
v___y_2042_ = v___y_2086_;
v___y_2043_ = v___y_2085_;
v___y_2044_ = v___y_2087_;
v___y_2045_ = v_isHEq_2084_;
v___y_2046_ = v___x_2115_;
goto v___jp_2038_;
}
}
else
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2095_, 1);
v___y_2027_ = v___y_2083_;
v___y_2028_ = v___y_2088_;
v___y_2029_ = v___y_2086_;
v___y_2030_ = v___y_2085_;
v___y_2031_ = v___y_2087_;
v___y_2032_ = v_isHEq_2084_;
v_a_2033_ = v_a_2116_;
goto v___jp_2026_;
}
}
else
{
v___y_2004_ = v___y_2083_;
v___y_2005_ = v_isHEq_2084_;
v___y_2006_ = v___y_2085_;
v___y_2007_ = v___y_2086_;
v___y_2008_ = v___y_2087_;
v___y_2009_ = v___y_2088_;
goto v___jp_2003_;
}
}
else
{
lean_dec(v_a_2092_);
v___y_2004_ = v___y_2083_;
v___y_2005_ = v_isHEq_2084_;
v___y_2006_ = v___y_2085_;
v___y_2007_ = v___y_2086_;
v___y_2008_ = v___y_2087_;
v___y_2009_ = v___y_2088_;
goto v___jp_2003_;
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2117_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2091_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2091_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
v___y_2004_ = v___y_2083_;
v___y_2005_ = v_isHEq_2084_;
v___y_2006_ = v___y_2085_;
v___y_2007_ = v___y_2086_;
v___y_2008_ = v___y_2087_;
v___y_2009_ = v___y_2088_;
goto v___jp_2003_;
}
}
}
v___jp_2125_:
{
lean_object* v___x_2131_; 
lean_inc_ref(v___x_2002_);
v___x_2131_ = l_Lean_Meta_matchHEq_x3f(v___x_2002_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
if (lean_obj_tag(v_a_2132_) == 1)
{
lean_object* v_val_2133_; lean_object* v_snd_2134_; lean_object* v_snd_2135_; lean_object* v_fst_2136_; lean_object* v_fst_2137_; lean_object* v_fst_2138_; lean_object* v_snd_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2232_; 
v_val_2133_ = lean_ctor_get(v_a_2132_, 0);
lean_inc(v_val_2133_);
lean_dec_ref_known(v_a_2132_, 1);
v_snd_2134_ = lean_ctor_get(v_val_2133_, 1);
lean_inc(v_snd_2134_);
v_snd_2135_ = lean_ctor_get(v_snd_2134_, 1);
lean_inc(v_snd_2135_);
v_fst_2136_ = lean_ctor_get(v_val_2133_, 0);
lean_inc(v_fst_2136_);
lean_dec(v_val_2133_);
v_fst_2137_ = lean_ctor_get(v_snd_2134_, 0);
lean_inc(v_fst_2137_);
lean_dec(v_snd_2134_);
v_fst_2138_ = lean_ctor_get(v_snd_2135_, 0);
v_snd_2139_ = lean_ctor_get(v_snd_2135_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_snd_2135_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2141_ = v_snd_2135_;
v_isShared_2142_ = v_isSharedCheck_2232_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_snd_2139_);
lean_inc(v_fst_2138_);
lean_dec(v_snd_2135_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2232_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2137_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
if (lean_obj_tag(v_a_2144_) == 1)
{
lean_object* v_val_2145_; lean_object* v___x_2146_; 
v_val_2145_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_a_2144_, 1);
v___x_2146_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2139_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
if (lean_obj_tag(v_a_2147_) == 1)
{
lean_object* v_toConstantVal_2148_; lean_object* v_val_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2215_; 
v_toConstantVal_2148_ = lean_ctor_get(v_val_2145_, 0);
lean_inc_ref(v_toConstantVal_2148_);
lean_dec(v_val_2145_);
v_val_2149_ = lean_ctor_get(v_a_2147_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_a_2147_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2151_ = v_a_2147_;
v_isShared_2152_ = v_isSharedCheck_2215_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_val_2149_);
lean_dec(v_a_2147_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2215_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_toConstantVal_2153_; lean_object* v_name_2154_; lean_object* v_name_2155_; uint8_t v___x_2156_; 
v_toConstantVal_2153_ = lean_ctor_get(v_val_2149_, 0);
lean_inc_ref(v_toConstantVal_2153_);
lean_dec(v_val_2149_);
v_name_2154_ = lean_ctor_get(v_toConstantVal_2148_, 0);
lean_inc(v_name_2154_);
lean_dec_ref(v_toConstantVal_2148_);
v_name_2155_ = lean_ctor_get(v_toConstantVal_2153_, 0);
lean_inc(v_name_2155_);
lean_dec_ref(v_toConstantVal_2153_);
v___x_2156_ = lean_name_eq(v_name_2154_, v_name_2155_);
lean_dec(v_name_2155_);
lean_dec(v_name_2154_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Meta_isExprDefEq(v_fst_2136_, v_fst_2138_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; uint8_t v___x_2159_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2159_ = lean_unbox(v_a_2158_);
lean_dec(v_a_2158_);
if (v___x_2159_ == 0)
{
lean_del_object(v___x_2151_);
lean_del_object(v___x_2141_);
v___y_2083_ = v_isEq_2126_;
v_isHEq_2084_ = v___x_1948_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
v___y_2088_ = v___y_2130_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2160_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec_ref(v_config_1937_);
lean_inc(v_mvarId_1938_);
v___x_2160_ = l_Lean_MVarId_getType(v_mvarId_1938_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = l_Lean_LocalDecl_toExpr(v_val_1969_);
v___x_2163_ = l_Lean_Meta_mkEqOfHEq(v___x_2162_, v___x_1948_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2165_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v___x_2165_ = l_Lean_Meta_mkNoConfusion(v_a_2161_, v_a_2164_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2167_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2167_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1938_, v_a_2166_, v___y_2128_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_dec_ref_known(v___x_2167_, 1);
v___x_2168_ = lean_box(v___x_1948_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2168_);
v___x_2170_ = v___x_2151_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v___x_1973_);
lean_ctor_set(v___x_2141_, 0, v___x_2170_);
v___x_2172_ = v___x_2141_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_1973_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
v_a_1955_ = v___x_2172_;
goto v___jp_1954_;
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_del_object(v___x_2151_);
lean_del_object(v___x_2141_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_2175_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2167_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2167_);
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
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2151_);
lean_del_object(v___x_2141_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2183_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2165_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2165_);
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
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v_a_2161_);
lean_del_object(v___x_2151_);
lean_del_object(v___x_2141_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2191_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2163_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2163_);
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
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_del_object(v___x_2151_);
lean_del_object(v___x_2141_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2199_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2160_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2160_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_del_object(v___x_2151_);
lean_del_object(v___x_2141_);
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2207_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2157_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2157_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_del_object(v___x_2151_);
lean_del_object(v___x_2141_);
lean_dec(v_fst_2138_);
lean_dec(v_fst_2136_);
v___y_2083_ = v_isEq_2126_;
v_isHEq_2084_ = v___x_1948_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
v___y_2088_ = v___y_2130_;
goto v___jp_2082_;
}
}
}
else
{
lean_dec(v_a_2147_);
lean_dec(v_val_2145_);
lean_del_object(v___x_2141_);
lean_dec(v_fst_2138_);
lean_dec(v_fst_2136_);
v___y_2083_ = v_isEq_2126_;
v_isHEq_2084_ = v___x_1948_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
v___y_2088_ = v___y_2130_;
goto v___jp_2082_;
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_val_2145_);
lean_del_object(v___x_2141_);
lean_dec(v_fst_2138_);
lean_dec(v_fst_2136_);
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2216_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2146_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2146_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
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
lean_dec(v_a_2144_);
lean_del_object(v___x_2141_);
lean_dec(v_snd_2139_);
lean_dec(v_fst_2138_);
lean_dec(v_fst_2136_);
v___y_2083_ = v_isEq_2126_;
v_isHEq_2084_ = v___x_1948_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
v___y_2088_ = v___y_2130_;
goto v___jp_2082_;
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_del_object(v___x_2141_);
lean_dec(v_snd_2139_);
lean_dec(v_fst_2138_);
lean_dec(v_fst_2136_);
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2224_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2143_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2143_);
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
}
else
{
lean_dec(v_a_2132_);
v___y_2083_ = v_isEq_2126_;
v_isHEq_2084_ = v___x_2001_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
v___y_2088_ = v___y_2130_;
goto v___jp_2082_;
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2233_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2131_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2131_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
v___jp_2241_:
{
lean_object* v___x_2246_; 
lean_inc_ref(v___x_2002_);
v___x_2246_ = l_Lean_Meta_matchEq_x3f(v___x_2002_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
if (lean_obj_tag(v_a_2247_) == 1)
{
lean_object* v_val_2248_; lean_object* v_snd_2249_; lean_object* v_fst_2250_; lean_object* v_snd_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2323_; 
v_val_2248_ = lean_ctor_get(v_a_2247_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v_a_2247_, 1);
v_snd_2249_ = lean_ctor_get(v_val_2248_, 1);
lean_inc(v_snd_2249_);
lean_dec(v_val_2248_);
v_fst_2250_ = lean_ctor_get(v_snd_2249_, 0);
v_snd_2251_ = lean_ctor_get(v_snd_2249_, 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_snd_2249_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2253_ = v_snd_2249_;
v_isShared_2254_ = v_isSharedCheck_2323_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_snd_2251_);
lean_inc(v_fst_2250_);
lean_dec(v_snd_2249_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2323_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2250_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2255_, 1);
if (lean_obj_tag(v_a_2256_) == 1)
{
lean_object* v_val_2257_; lean_object* v___x_2258_; 
v_val_2257_ = lean_ctor_get(v_a_2256_, 0);
lean_inc(v_val_2257_);
lean_dec_ref_known(v_a_2256_, 1);
v___x_2258_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2251_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2258_, 1);
if (lean_obj_tag(v_a_2259_) == 1)
{
lean_object* v_toConstantVal_2260_; lean_object* v_val_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2306_; 
v_toConstantVal_2260_ = lean_ctor_get(v_val_2257_, 0);
lean_inc_ref(v_toConstantVal_2260_);
lean_dec(v_val_2257_);
v_val_2261_ = lean_ctor_get(v_a_2259_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_a_2259_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2263_ = v_a_2259_;
v_isShared_2264_ = v_isSharedCheck_2306_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_val_2261_);
lean_dec(v_a_2259_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2306_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v_toConstantVal_2265_; lean_object* v_name_2266_; lean_object* v_name_2267_; uint8_t v___x_2268_; 
v_toConstantVal_2265_ = lean_ctor_get(v_val_2261_, 0);
lean_inc_ref(v_toConstantVal_2265_);
lean_dec(v_val_2261_);
v_name_2266_ = lean_ctor_get(v_toConstantVal_2260_, 0);
lean_inc(v_name_2266_);
lean_dec_ref(v_toConstantVal_2260_);
v_name_2267_ = lean_ctor_get(v_toConstantVal_2265_, 0);
lean_inc(v_name_2267_);
lean_dec_ref(v_toConstantVal_2265_);
v___x_2268_ = lean_name_eq(v_name_2266_, v_name_2267_);
lean_dec(v_name_2267_);
lean_dec(v_name_2266_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec_ref(v_config_1937_);
lean_inc(v_mvarId_1938_);
v___x_2269_ = l_Lean_MVarId_getType(v_mvarId_1938_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = l_Lean_LocalDecl_toExpr(v_val_1969_);
v___x_2272_ = l_Lean_Meta_mkNoConfusion(v_a_2270_, v___x_2271_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v___x_2274_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1938_, v_a_2273_, v___y_2243_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
lean_dec_ref_known(v___x_2274_, 1);
v___x_2275_ = lean_box(v___x_1948_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2275_);
v___x_2277_ = v___x_2263_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v___x_1973_);
lean_ctor_set(v___x_2253_, 0, v___x_2277_);
v___x_2279_ = v___x_2253_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_1973_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
v_a_1955_ = v___x_2279_;
goto v___jp_1954_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_del_object(v___x_2263_);
lean_del_object(v___x_2253_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_2282_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2274_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2274_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_del_object(v___x_2263_);
lean_del_object(v___x_2253_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2290_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2272_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2272_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_del_object(v___x_2263_);
lean_del_object(v___x_2253_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2298_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2269_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2269_);
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
lean_del_object(v___x_2263_);
lean_del_object(v___x_2253_);
v_isEq_2126_ = v___x_1948_;
v___y_2127_ = v___y_2242_;
v___y_2128_ = v___y_2243_;
v___y_2129_ = v___y_2244_;
v___y_2130_ = v___y_2245_;
goto v___jp_2125_;
}
}
}
else
{
lean_dec(v_a_2259_);
lean_dec(v_val_2257_);
lean_del_object(v___x_2253_);
v_isEq_2126_ = v___x_1948_;
v___y_2127_ = v___y_2242_;
v___y_2128_ = v___y_2243_;
v___y_2129_ = v___y_2244_;
v___y_2130_ = v___y_2245_;
goto v___jp_2125_;
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_val_2257_);
lean_del_object(v___x_2253_);
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2307_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2258_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2258_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_dec(v_a_2256_);
lean_del_object(v___x_2253_);
lean_dec(v_snd_2251_);
v_isEq_2126_ = v___x_1948_;
v___y_2127_ = v___y_2242_;
v___y_2128_ = v___y_2243_;
v___y_2129_ = v___y_2244_;
v___y_2130_ = v___y_2245_;
goto v___jp_2125_;
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_del_object(v___x_2253_);
lean_dec(v_snd_2251_);
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2315_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2255_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2255_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
else
{
lean_dec(v_a_2247_);
v_isEq_2126_ = v___x_2001_;
v___y_2127_ = v___y_2242_;
v___y_2128_ = v___y_2243_;
v___y_2129_ = v___y_2244_;
v___y_2130_ = v___y_2245_;
goto v___jp_2125_;
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2324_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2246_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2246_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
v___jp_2332_:
{
lean_object* v___x_2337_; 
lean_inc_ref(v___x_2002_);
v___x_2337_ = l_Lean_refutableHasNotBit_x3f(v___x_2002_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
if (lean_obj_tag(v_a_2338_) == 1)
{
lean_object* v_val_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec_ref(v_config_1937_);
v_val_2339_ = lean_ctor_get(v_a_2338_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_a_2338_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2341_ = v_a_2338_;
v_isShared_2342_ = v_isSharedCheck_2378_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_val_2339_);
lean_dec(v_a_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2378_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; 
lean_inc(v_mvarId_1938_);
v___x_2343_ = l_Lean_MVarId_getType(v_mvarId_1938_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v___x_2345_ = l_Lean_LocalDecl_toExpr(v_val_1969_);
v___x_2346_ = l_Lean_Meta_mkAbsurd(v_a_2344_, v_val_2339_, v___x_2345_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2348_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1938_, v_a_2347_, v___y_2334_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
lean_dec_ref_known(v___x_2348_, 1);
v___x_2349_ = lean_box(v___x_1948_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2349_);
v___x_2351_ = v___x_2341_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v___x_1973_);
v_a_1955_ = v___x_2352_;
goto v___jp_1954_;
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_del_object(v___x_2341_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_2354_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2348_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2348_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_del_object(v___x_2341_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2362_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2346_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2346_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_del_object(v___x_2341_);
lean_dec(v_val_2339_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2370_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2343_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2343_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
else
{
lean_object* v___x_2379_; 
lean_dec(v_a_2338_);
lean_inc_ref(v___x_2002_);
v___x_2379_ = l_Lean_Meta_matchNe_x3f(v___x_2002_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
if (lean_obj_tag(v_a_2380_) == 1)
{
lean_object* v_val_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2450_; 
v_val_2381_ = lean_ctor_get(v_a_2380_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_a_2380_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2383_ = v_a_2380_;
v_isShared_2384_ = v_isSharedCheck_2450_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_val_2381_);
lean_dec(v_a_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2450_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_snd_2385_; lean_object* v_fst_2386_; lean_object* v_snd_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2449_; 
v_snd_2385_ = lean_ctor_get(v_val_2381_, 1);
lean_inc(v_snd_2385_);
lean_dec(v_val_2381_);
v_fst_2386_ = lean_ctor_get(v_snd_2385_, 0);
v_snd_2387_ = lean_ctor_get(v_snd_2385_, 1);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_snd_2385_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2389_ = v_snd_2385_;
v_isShared_2390_ = v_isSharedCheck_2449_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_snd_2387_);
lean_inc(v_fst_2386_);
lean_dec(v_snd_2385_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2449_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; 
lean_inc(v_fst_2386_);
v___x_2391_ = l_Lean_Meta_isExprDefEq(v_fst_2386_, v_snd_2387_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; uint8_t v___x_2393_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = lean_unbox(v_a_2392_);
lean_dec(v_a_2392_);
if (v___x_2393_ == 0)
{
lean_del_object(v___x_2389_);
lean_dec(v_fst_2386_);
lean_del_object(v___x_2383_);
v___y_2242_ = v___y_2333_;
v___y_2243_ = v___y_2334_;
v___y_2244_ = v___y_2335_;
v___y_2245_ = v___y_2336_;
goto v___jp_2241_;
}
else
{
lean_object* v___x_2394_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec_ref(v_config_1937_);
lean_inc(v_mvarId_1938_);
v___x_2394_ = l_Lean_MVarId_getType(v_mvarId_1938_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = l_Lean_Meta_mkEqRefl(v_fst_2386_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2398_ = l_Lean_LocalDecl_toExpr(v_val_1969_);
v___x_2399_ = l_Lean_Meta_mkAbsurd(v_a_2395_, v_a_2397_, v___x_2398_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2401_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1938_, v_a_2400_, v___y_2334_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_dec_ref_known(v___x_2401_, 1);
v___x_2402_ = lean_box(v___x_1948_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2402_);
v___x_2404_ = v___x_2383_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2406_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 1, v___x_1973_);
lean_ctor_set(v___x_2389_, 0, v___x_2404_);
v___x_2406_ = v___x_2389_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___x_1973_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
v_a_1955_ = v___x_2406_;
goto v___jp_1954_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_del_object(v___x_2389_);
lean_del_object(v___x_2383_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_2409_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2401_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2401_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_del_object(v___x_2389_);
lean_del_object(v___x_2383_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2417_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2399_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2399_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_a_2395_);
lean_del_object(v___x_2389_);
lean_del_object(v___x_2383_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2425_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2396_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2396_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_del_object(v___x_2389_);
lean_dec(v_fst_2386_);
lean_del_object(v___x_2383_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
v_a_2433_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2394_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2394_);
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
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_del_object(v___x_2389_);
lean_dec(v_fst_2386_);
lean_del_object(v___x_2383_);
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2441_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2391_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2391_);
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
}
}
else
{
lean_dec(v_a_2380_);
v___y_2242_ = v___y_2333_;
v___y_2243_ = v___y_2334_;
v___y_2244_ = v___y_2335_;
v___y_2245_ = v___y_2336_;
goto v___jp_2241_;
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2451_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2379_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2379_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_2459_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2337_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2337_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
else
{
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_1963_ = v___x_1974_;
goto v___jp_1962_;
}
v___jp_1975_:
{
uint8_t v_emptyType_1982_; 
v_emptyType_1982_ = lean_ctor_get_uint8(v_config_1937_, sizeof(void*)*1 + 1);
if (v_emptyType_1982_ == 0)
{
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_1963_ = v___x_1974_;
goto v___jp_1962_;
}
else
{
if (v___y_1976_ == 0)
{
if (v___y_1977_ == 0)
{
lean_object* v_searchFuel_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_searchFuel_1983_ = lean_ctor_get(v_config_1937_, 0);
v___x_1984_ = l_Lean_LocalDecl_fvarId(v_val_1969_);
lean_dec(v_val_1969_);
lean_inc(v_searchFuel_1983_);
lean_inc(v_mvarId_1938_);
v___x_1985_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1938_, v___x_1984_, v_searchFuel_1983_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; uint8_t v___x_1987_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_1987_ = lean_unbox(v_a_1986_);
lean_dec(v_a_1986_);
if (v___x_1987_ == 0)
{
lean_del_object(v___x_1971_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_1963_ = v___x_1974_;
goto v___jp_1962_;
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v___x_1988_ = lean_box(v___x_1948_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1988_);
v___x_1990_ = v___x_1971_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; 
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v___x_1973_);
v_a_1955_ = v___x_1991_;
goto v___jp_1954_;
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_del_object(v___x_1971_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
lean_dec(v_mvarId_1938_);
lean_dec_ref(v_config_1937_);
v_a_1993_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1985_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1985_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_1963_ = v___x_1974_;
goto v___jp_1962_;
}
}
else
{
lean_del_object(v___x_1971_);
lean_dec(v_val_1969_);
lean_del_object(v___x_1952_);
lean_dec(v_snd_1950_);
v_a_1963_ = v___x_1974_;
goto v___jp_1962_;
}
}
}
}
}
v___jp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1956_, 0, v_a_1955_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1956_);
v___x_1958_ = v___x_1952_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_snd_1950_);
v___x_1958_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
}
v___jp_1962_:
{
lean_object* v___x_1964_; size_t v___x_1965_; size_t v___x_1966_; 
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1961_);
lean_ctor_set(v___x_1964_, 1, v_a_1963_);
v___x_1965_ = ((size_t)1ULL);
v___x_1966_ = lean_usize_add(v_i_1941_, v___x_1965_);
v_i_1941_ = v___x_1966_;
v_b_1942_ = v___x_1964_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2533_, lean_object* v_mvarId_2534_, lean_object* v_as_2535_, lean_object* v_sz_2536_, lean_object* v_i_2537_, lean_object* v_b_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
size_t v_sz_boxed_2544_; size_t v_i_boxed_2545_; lean_object* v_res_2546_; 
v_sz_boxed_2544_ = lean_unbox_usize(v_sz_2536_);
lean_dec(v_sz_2536_);
v_i_boxed_2545_ = lean_unbox_usize(v_i_2537_);
lean_dec(v_i_2537_);
v_res_2546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2533_, v_mvarId_2534_, v_as_2535_, v_sz_boxed_2544_, v_i_boxed_2545_, v_b_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec_ref(v_as_2535_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2547_, lean_object* v_mvarId_2548_, lean_object* v_as_2549_, size_t v_sz_2550_, size_t v_i_2551_, lean_object* v_b_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
uint8_t v___x_2558_; 
v___x_2558_ = lean_usize_dec_lt(v_i_2551_, v_sz_2550_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_b_2552_);
return v___x_2559_;
}
else
{
lean_object* v_snd_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_3141_; 
v_snd_2560_ = lean_ctor_get(v_b_2552_, 1);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_b_2552_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v_b_2552_, 0);
lean_dec(v_unused_3142_);
v___x_2562_ = v_b_2552_;
v_isShared_2563_ = v_isSharedCheck_3141_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snd_2560_);
lean_dec(v_b_2552_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_3141_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v_a_2565_; lean_object* v___x_2571_; lean_object* v_a_2573_; lean_object* v_a_2578_; 
v___x_2571_ = lean_box(0);
v_a_2578_ = lean_array_uget(v_as_2549_, v_i_2551_);
if (lean_obj_tag(v_a_2578_) == 0)
{
lean_del_object(v___x_2562_);
v_a_2573_ = v_snd_2560_;
goto v___jp_2572_;
}
else
{
lean_object* v_val_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_3140_; 
v_val_2579_ = lean_ctor_get(v_a_2578_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_a_2578_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_2581_ = v_a_2578_;
v_isShared_2582_ = v_isSharedCheck_3140_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_val_2579_);
lean_dec(v_a_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_3140_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___y_2586_; uint8_t v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; uint8_t v___x_2611_; 
v___x_2583_ = lean_box(0);
v___x_2584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2611_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2579_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; uint8_t v___y_2614_; uint8_t v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; uint8_t v___y_2637_; lean_object* v___y_2638_; uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v_a_2643_; uint8_t v___y_2649_; lean_object* v___y_2650_; uint8_t v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; uint8_t v___y_2693_; uint8_t v_isHEq_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; uint8_t v_isEq_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___x_3077_; 
v___x_2612_ = l_Lean_LocalDecl_type(v_val_2579_);
lean_inc_ref(v___x_2612_);
v___x_3077_ = l_Lean_Meta_matchNot_x3f(v___x_2612_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
if (lean_obj_tag(v_a_3078_) == 1)
{
lean_object* v_val_3079_; lean_object* v___x_3080_; 
v_val_3079_ = lean_ctor_get(v_a_3078_, 0);
lean_inc(v_val_3079_);
lean_dec_ref_known(v_a_3078_, 1);
v___x_3080_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3079_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
if (lean_obj_tag(v_a_3081_) == 1)
{
lean_object* v_val_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3123_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec_ref(v_config_2547_);
v_val_3082_ = lean_ctor_get(v_a_3081_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_a_3081_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3084_ = v_a_3081_;
v_isShared_3085_ = v_isSharedCheck_3123_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_val_3082_);
lean_dec(v_a_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3123_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; 
lean_inc(v_mvarId_2548_);
v___x_3086_ = l_Lean_MVarId_getType(v_mvarId_2548_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
v___x_3088_ = l_Lean_LocalDecl_toExpr(v_val_2579_);
v___x_3089_ = l_Lean_mkFVar(v_val_3082_);
v___x_3090_ = l_Lean_Expr_app___override(v___x_3088_, v___x_3089_);
v___x_3091_ = l_Lean_Meta_mkFalseElim(v_a_3087_, v___x_3090_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3093_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref_known(v___x_3091_, 1);
v___x_3093_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2548_, v_a_3092_, v___y_2554_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
lean_dec_ref_known(v___x_3093_, 1);
v___x_3094_ = lean_box(v___x_2558_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3094_);
v___x_3096_ = v___x_3084_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
lean_ctor_set(v___x_3097_, 1, v___x_2583_);
v_a_2565_ = v___x_3097_;
goto v___jp_2564_;
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_del_object(v___x_3084_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_3099_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3093_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3093_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_del_object(v___x_3084_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_3107_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3091_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3091_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_del_object(v___x_3084_);
lean_dec(v_val_3082_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_3115_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3086_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3086_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
else
{
lean_dec(v_a_3081_);
v___y_2943_ = v___y_2553_;
v___y_2944_ = v___y_2554_;
v___y_2945_ = v___y_2555_;
v___y_2946_ = v___y_2556_;
goto v___jp_2942_;
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_3124_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3080_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3080_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_dec(v_a_3078_);
v___y_2943_ = v___y_2553_;
v___y_2944_ = v___y_2554_;
v___y_2945_ = v___y_2555_;
v___y_2946_ = v___y_2556_;
goto v___jp_2942_;
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_3132_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3077_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3077_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
v___jp_2613_:
{
uint8_t v_genDiseq_2620_; 
v_genDiseq_2620_ = lean_ctor_get_uint8(v_config_2547_, sizeof(void*)*1 + 2);
if (v_genDiseq_2620_ == 0)
{
lean_dec_ref(v___x_2612_);
v___y_2586_ = v___y_2614_;
v___y_2587_ = v___y_2615_;
v___y_2588_ = v___y_2616_;
v___y_2589_ = v___y_2617_;
v___y_2590_ = v___y_2618_;
v___y_2591_ = v___y_2619_;
goto v___jp_2585_;
}
else
{
uint8_t v___x_2621_; 
v___x_2621_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2612_);
lean_dec_ref(v___x_2612_);
if (v___x_2621_ == 0)
{
v___y_2586_ = v___y_2614_;
v___y_2587_ = v___y_2615_;
v___y_2588_ = v___y_2616_;
v___y_2589_ = v___y_2617_;
v___y_2590_ = v___y_2618_;
v___y_2591_ = v___y_2619_;
goto v___jp_2585_;
}
else
{
lean_object* v___x_2622_; 
lean_inc(v_val_2579_);
lean_inc(v_mvarId_2548_);
v___x_2622_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2548_, v_val_2579_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; uint8_t v___x_2624_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2624_ = lean_unbox(v_a_2623_);
lean_dec(v_a_2623_);
if (v___x_2624_ == 0)
{
v___y_2586_ = v___y_2614_;
v___y_2587_ = v___y_2615_;
v___y_2588_ = v___y_2616_;
v___y_2589_ = v___y_2617_;
v___y_2590_ = v___y_2618_;
v___y_2591_ = v___y_2619_;
goto v___jp_2585_;
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v___x_2625_ = lean_box(v___x_2558_);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___x_2583_);
v_a_2565_ = v___x_2627_;
goto v___jp_2564_;
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2628_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2622_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2622_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
}
v___jp_2636_:
{
uint8_t v___x_2644_; 
v___x_2644_ = l_Lean_Exception_isInterrupt(v_a_2643_);
if (v___x_2644_ == 0)
{
uint8_t v___x_2645_; 
lean_inc_ref(v_a_2643_);
v___x_2645_ = l_Lean_Exception_isRuntime(v_a_2643_);
if (v___x_2645_ == 0)
{
lean_dec_ref(v_a_2643_);
v___y_2614_ = v___y_2637_;
v___y_2615_ = v___y_2639_;
v___y_2616_ = v___y_2641_;
v___y_2617_ = v___y_2638_;
v___y_2618_ = v___y_2640_;
v___y_2619_ = v___y_2642_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2646_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v___x_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_a_2643_);
return v___x_2646_;
}
}
else
{
lean_object* v___x_2647_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v___x_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2647_, 0, v_a_2643_);
return v___x_2647_;
}
}
v___jp_2648_:
{
if (lean_obj_tag(v___y_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_a_2657_ = lean_ctor_get(v___y_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___y_2656_, 1);
v___x_2658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2659_ = l_Lean_Expr_isConstOf(v_a_2657_, v___x_2658_);
lean_dec(v_a_2657_);
if (v___x_2659_ == 0)
{
lean_dec_ref(v___y_2654_);
v___y_2614_ = v___y_2649_;
v___y_2615_ = v___y_2651_;
v___y_2616_ = v___y_2653_;
v___y_2617_ = v___y_2650_;
v___y_2618_ = v___y_2652_;
v___y_2619_ = v___y_2655_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2660_; 
lean_inc_ref(v___y_2654_);
v___x_2660_ = l_Lean_Meta_mkEqRefl(v___y_2654_, v___y_2653_, v___y_2650_, v___y_2652_, v___y_2655_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2662_; lean_object* v_dummy_2663_; lean_object* v_nargs_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2660_, 1);
v___x_2662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2663_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2664_ = l_Lean_Expr_getAppNumArgs(v___y_2654_);
lean_inc(v_nargs_2664_);
v___x_2665_ = lean_mk_array(v_nargs_2664_, v_dummy_2663_);
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_nat_sub(v_nargs_2664_, v___x_2666_);
lean_dec(v_nargs_2664_);
v___x_2668_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2654_, v___x_2665_, v___x_2667_);
v___x_2669_ = lean_array_push(v___x_2668_, v_a_2661_);
v___x_2670_ = l_Lean_mkAppN(v___x_2662_, v___x_2669_);
lean_dec_ref(v___x_2669_);
lean_inc(v_mvarId_2548_);
v___x_2671_ = l_Lean_MVarId_getType(v_mvarId_2548_, v___y_2653_, v___y_2650_, v___y_2652_, v___y_2655_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
lean_inc(v_val_2579_);
v___x_2673_ = l_Lean_LocalDecl_toExpr(v_val_2579_);
v___x_2674_ = l_Lean_Meta_mkAbsurd(v_a_2672_, v___x_2673_, v___x_2670_, v___y_2653_, v___y_2650_, v___y_2652_, v___y_2655_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2676_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
lean_inc(v_mvarId_2548_);
v___x_2676_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2548_, v_a_2675_, v___y_2650_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2685_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v___x_2676_, 0);
lean_dec(v_unused_2686_);
v___x_2678_ = v___x_2676_;
v_isShared_2679_ = v_isSharedCheck_2685_;
goto v_resetjp_2677_;
}
else
{
lean_dec(v___x_2676_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2685_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2680_ = lean_box(v___x_2558_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set_tag(v___x_2678_, 1);
lean_ctor_set(v___x_2678_, 0, v___x_2680_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v___x_2583_);
v_a_2565_ = v___x_2683_;
goto v___jp_2564_;
}
}
}
else
{
lean_object* v_a_2687_; 
v_a_2687_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2676_, 1);
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2651_;
v___y_2640_ = v___y_2652_;
v___y_2641_ = v___y_2653_;
v___y_2642_ = v___y_2655_;
v_a_2643_ = v_a_2687_;
goto v___jp_2636_;
}
}
else
{
lean_object* v_a_2688_; 
v_a_2688_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2674_, 1);
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2651_;
v___y_2640_ = v___y_2652_;
v___y_2641_ = v___y_2653_;
v___y_2642_ = v___y_2655_;
v_a_2643_ = v_a_2688_;
goto v___jp_2636_;
}
}
else
{
lean_object* v_a_2689_; 
lean_dec_ref(v___x_2670_);
v_a_2689_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2671_, 1);
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2651_;
v___y_2640_ = v___y_2652_;
v___y_2641_ = v___y_2653_;
v___y_2642_ = v___y_2655_;
v_a_2643_ = v_a_2689_;
goto v___jp_2636_;
}
}
else
{
lean_object* v_a_2690_; 
lean_dec_ref(v___y_2654_);
v_a_2690_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2660_, 1);
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2651_;
v___y_2640_ = v___y_2652_;
v___y_2641_ = v___y_2653_;
v___y_2642_ = v___y_2655_;
v_a_2643_ = v_a_2690_;
goto v___jp_2636_;
}
}
}
else
{
lean_object* v_a_2691_; 
lean_dec_ref(v___y_2654_);
v_a_2691_ = lean_ctor_get(v___y_2656_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___y_2656_, 1);
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2651_;
v___y_2640_ = v___y_2652_;
v___y_2641_ = v___y_2653_;
v___y_2642_ = v___y_2655_;
v_a_2643_ = v_a_2691_;
goto v___jp_2636_;
}
}
v___jp_2692_:
{
uint8_t v_useDecide_2699_; 
v_useDecide_2699_ = lean_ctor_get_uint8(v_config_2547_, sizeof(void*)*1);
if (v_useDecide_2699_ == 0)
{
v___y_2614_ = v_isHEq_2694_;
v___y_2615_ = v___y_2693_;
v___y_2616_ = v___y_2695_;
v___y_2617_ = v___y_2696_;
v___y_2618_ = v___y_2697_;
v___y_2619_ = v___y_2698_;
goto v___jp_2613_;
}
else
{
uint8_t v___x_2700_; 
v___x_2700_ = l_Lean_Expr_hasFVar(v___x_2612_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_inc_ref(v___x_2612_);
v___x_2701_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2612_, v___y_2696_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; uint8_t v___x_2703_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = l_Lean_Expr_hasMVar(v_a_2702_);
if (v___x_2703_ == 0)
{
uint8_t v___x_2704_; 
v___x_2704_ = l_Lean_Expr_hasFVar(v_a_2702_);
lean_dec(v_a_2702_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
lean_inc_ref(v___x_2612_);
v___x_2705_ = l_Lean_Meta_mkDecide(v___x_2612_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; uint8_t v_transparency_2708_; uint8_t v___x_2709_; uint8_t v___x_2710_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = l_Lean_Meta_Context_config(v___y_2695_);
v_transparency_2708_ = lean_ctor_get_uint8(v___x_2707_, 9);
lean_dec_ref(v___x_2707_);
v___x_2709_ = 1;
v___x_2710_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2708_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v_keyedConfig_2711_; uint8_t v_trackZetaDelta_2712_; lean_object* v_zetaDeltaSet_2713_; lean_object* v_lctx_2714_; lean_object* v_localInstances_2715_; lean_object* v_defEqCtx_x3f_2716_; lean_object* v_synthPendingDepth_2717_; lean_object* v_customCanUnfoldPredicate_x3f_2718_; uint8_t v_univApprox_2719_; uint8_t v_inTypeClassResolution_2720_; uint8_t v_cacheInferType_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_keyedConfig_2711_ = lean_ctor_get(v___y_2695_, 0);
v_trackZetaDelta_2712_ = lean_ctor_get_uint8(v___y_2695_, sizeof(void*)*7);
v_zetaDeltaSet_2713_ = lean_ctor_get(v___y_2695_, 1);
v_lctx_2714_ = lean_ctor_get(v___y_2695_, 2);
v_localInstances_2715_ = lean_ctor_get(v___y_2695_, 3);
v_defEqCtx_x3f_2716_ = lean_ctor_get(v___y_2695_, 4);
v_synthPendingDepth_2717_ = lean_ctor_get(v___y_2695_, 5);
v_customCanUnfoldPredicate_x3f_2718_ = lean_ctor_get(v___y_2695_, 6);
v_univApprox_2719_ = lean_ctor_get_uint8(v___y_2695_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2720_ = lean_ctor_get_uint8(v___y_2695_, sizeof(void*)*7 + 2);
v_cacheInferType_2721_ = lean_ctor_get_uint8(v___y_2695_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2711_);
v___x_2722_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2709_, v_keyedConfig_2711_);
lean_inc(v_customCanUnfoldPredicate_x3f_2718_);
lean_inc(v_synthPendingDepth_2717_);
lean_inc(v_defEqCtx_x3f_2716_);
lean_inc_ref(v_localInstances_2715_);
lean_inc_ref(v_lctx_2714_);
lean_inc(v_zetaDeltaSet_2713_);
v___x_2723_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v_zetaDeltaSet_2713_);
lean_ctor_set(v___x_2723_, 2, v_lctx_2714_);
lean_ctor_set(v___x_2723_, 3, v_localInstances_2715_);
lean_ctor_set(v___x_2723_, 4, v_defEqCtx_x3f_2716_);
lean_ctor_set(v___x_2723_, 5, v_synthPendingDepth_2717_);
lean_ctor_set(v___x_2723_, 6, v_customCanUnfoldPredicate_x3f_2718_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7, v_trackZetaDelta_2712_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7 + 1, v_univApprox_2719_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2720_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7 + 3, v_cacheInferType_2721_);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc(v_a_2706_);
v___x_2724_ = lean_whnf(v_a_2706_, v___x_2723_, v___y_2696_, v___y_2697_, v___y_2698_);
v___y_2649_ = v_isHEq_2694_;
v___y_2650_ = v___y_2696_;
v___y_2651_ = v___y_2693_;
v___y_2652_ = v___y_2697_;
v___y_2653_ = v___y_2695_;
v___y_2654_ = v_a_2706_;
v___y_2655_ = v___y_2698_;
v___y_2656_ = v___x_2724_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2725_; 
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v_a_2706_);
v___x_2725_ = lean_whnf(v_a_2706_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
v___y_2649_ = v_isHEq_2694_;
v___y_2650_ = v___y_2696_;
v___y_2651_ = v___y_2693_;
v___y_2652_ = v___y_2697_;
v___y_2653_ = v___y_2695_;
v___y_2654_ = v_a_2706_;
v___y_2655_ = v___y_2698_;
v___y_2656_ = v___x_2725_;
goto v___jp_2648_;
}
}
else
{
lean_object* v_a_2726_; 
v_a_2726_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2705_, 1);
v___y_2637_ = v_isHEq_2694_;
v___y_2638_ = v___y_2696_;
v___y_2639_ = v___y_2693_;
v___y_2640_ = v___y_2697_;
v___y_2641_ = v___y_2695_;
v___y_2642_ = v___y_2698_;
v_a_2643_ = v_a_2726_;
goto v___jp_2636_;
}
}
else
{
v___y_2614_ = v_isHEq_2694_;
v___y_2615_ = v___y_2693_;
v___y_2616_ = v___y_2695_;
v___y_2617_ = v___y_2696_;
v___y_2618_ = v___y_2697_;
v___y_2619_ = v___y_2698_;
goto v___jp_2613_;
}
}
else
{
lean_dec(v_a_2702_);
v___y_2614_ = v_isHEq_2694_;
v___y_2615_ = v___y_2693_;
v___y_2616_ = v___y_2695_;
v___y_2617_ = v___y_2696_;
v___y_2618_ = v___y_2697_;
v___y_2619_ = v___y_2698_;
goto v___jp_2613_;
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2727_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2701_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2701_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
else
{
v___y_2614_ = v_isHEq_2694_;
v___y_2615_ = v___y_2693_;
v___y_2616_ = v___y_2695_;
v___y_2617_ = v___y_2696_;
v___y_2618_ = v___y_2697_;
v___y_2619_ = v___y_2698_;
goto v___jp_2613_;
}
}
}
v___jp_2735_:
{
lean_object* v___x_2741_; 
lean_inc_ref(v___x_2612_);
v___x_2741_ = l_Lean_Meta_matchHEq_x3f(v___x_2612_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v___x_2741_, 1);
if (lean_obj_tag(v_a_2742_) == 1)
{
lean_object* v_val_2743_; lean_object* v_snd_2744_; lean_object* v_snd_2745_; lean_object* v_fst_2746_; lean_object* v_fst_2747_; lean_object* v_fst_2748_; lean_object* v_snd_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2842_; 
v_val_2743_ = lean_ctor_get(v_a_2742_, 0);
lean_inc(v_val_2743_);
lean_dec_ref_known(v_a_2742_, 1);
v_snd_2744_ = lean_ctor_get(v_val_2743_, 1);
lean_inc(v_snd_2744_);
v_snd_2745_ = lean_ctor_get(v_snd_2744_, 1);
lean_inc(v_snd_2745_);
v_fst_2746_ = lean_ctor_get(v_val_2743_, 0);
lean_inc(v_fst_2746_);
lean_dec(v_val_2743_);
v_fst_2747_ = lean_ctor_get(v_snd_2744_, 0);
lean_inc(v_fst_2747_);
lean_dec(v_snd_2744_);
v_fst_2748_ = lean_ctor_get(v_snd_2745_, 0);
v_snd_2749_ = lean_ctor_get(v_snd_2745_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_snd_2745_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2751_ = v_snd_2745_;
v_isShared_2752_ = v_isSharedCheck_2842_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_snd_2749_);
lean_inc(v_fst_2748_);
lean_dec(v_snd_2745_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2842_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2747_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
if (lean_obj_tag(v_a_2754_) == 1)
{
lean_object* v_val_2755_; lean_object* v___x_2756_; 
v_val_2755_ = lean_ctor_get(v_a_2754_, 0);
lean_inc(v_val_2755_);
lean_dec_ref_known(v_a_2754_, 1);
v___x_2756_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2749_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
if (lean_obj_tag(v_a_2757_) == 1)
{
lean_object* v_toConstantVal_2758_; lean_object* v_val_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2825_; 
v_toConstantVal_2758_ = lean_ctor_get(v_val_2755_, 0);
lean_inc_ref(v_toConstantVal_2758_);
lean_dec(v_val_2755_);
v_val_2759_ = lean_ctor_get(v_a_2757_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_a_2757_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2761_ = v_a_2757_;
v_isShared_2762_ = v_isSharedCheck_2825_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_val_2759_);
lean_dec(v_a_2757_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2825_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v_toConstantVal_2763_; lean_object* v_name_2764_; lean_object* v_name_2765_; uint8_t v___x_2766_; 
v_toConstantVal_2763_ = lean_ctor_get(v_val_2759_, 0);
lean_inc_ref(v_toConstantVal_2763_);
lean_dec(v_val_2759_);
v_name_2764_ = lean_ctor_get(v_toConstantVal_2758_, 0);
lean_inc(v_name_2764_);
lean_dec_ref(v_toConstantVal_2758_);
v_name_2765_ = lean_ctor_get(v_toConstantVal_2763_, 0);
lean_inc(v_name_2765_);
lean_dec_ref(v_toConstantVal_2763_);
v___x_2766_ = lean_name_eq(v_name_2764_, v_name_2765_);
lean_dec(v_name_2765_);
lean_dec(v_name_2764_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_Meta_isExprDefEq(v_fst_2746_, v_fst_2748_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; uint8_t v___x_2769_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = lean_unbox(v_a_2768_);
lean_dec(v_a_2768_);
if (v___x_2769_ == 0)
{
lean_del_object(v___x_2761_);
lean_del_object(v___x_2751_);
v___y_2693_ = v_isEq_2736_;
v_isHEq_2694_ = v___x_2558_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
v___y_2698_ = v___y_2740_;
goto v___jp_2692_;
}
else
{
lean_object* v___x_2770_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec_ref(v_config_2547_);
lean_inc(v_mvarId_2548_);
v___x_2770_ = l_Lean_MVarId_getType(v_mvarId_2548_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2772_ = l_Lean_LocalDecl_toExpr(v_val_2579_);
v___x_2773_ = l_Lean_Meta_mkEqOfHEq(v___x_2772_, v___x_2558_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = l_Lean_Meta_mkNoConfusion(v_a_2771_, v_a_2774_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2548_, v_a_2776_, v___y_2738_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2780_; 
lean_dec_ref_known(v___x_2777_, 1);
v___x_2778_ = lean_box(v___x_2558_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2778_);
v___x_2780_ = v___x_2761_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2782_; 
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 1, v___x_2583_);
lean_ctor_set(v___x_2751_, 0, v___x_2780_);
v___x_2782_ = v___x_2751_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v___x_2583_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
v_a_2565_ = v___x_2782_;
goto v___jp_2564_;
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_del_object(v___x_2761_);
lean_del_object(v___x_2751_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_2785_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2777_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2777_);
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
lean_del_object(v___x_2761_);
lean_del_object(v___x_2751_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_2793_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2775_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2775_);
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
lean_dec(v_a_2771_);
lean_del_object(v___x_2761_);
lean_del_object(v___x_2751_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_2801_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2773_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2773_);
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
lean_del_object(v___x_2761_);
lean_del_object(v___x_2751_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_2809_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2770_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2770_);
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
lean_del_object(v___x_2761_);
lean_del_object(v___x_2751_);
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2817_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2767_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2767_);
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
else
{
lean_del_object(v___x_2761_);
lean_del_object(v___x_2751_);
lean_dec(v_fst_2748_);
lean_dec(v_fst_2746_);
v___y_2693_ = v_isEq_2736_;
v_isHEq_2694_ = v___x_2558_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
v___y_2698_ = v___y_2740_;
goto v___jp_2692_;
}
}
}
else
{
lean_dec(v_a_2757_);
lean_dec(v_val_2755_);
lean_del_object(v___x_2751_);
lean_dec(v_fst_2748_);
lean_dec(v_fst_2746_);
v___y_2693_ = v_isEq_2736_;
v_isHEq_2694_ = v___x_2558_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
v___y_2698_ = v___y_2740_;
goto v___jp_2692_;
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_val_2755_);
lean_del_object(v___x_2751_);
lean_dec(v_fst_2748_);
lean_dec(v_fst_2746_);
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2826_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2756_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2756_);
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
lean_dec(v_a_2754_);
lean_del_object(v___x_2751_);
lean_dec(v_snd_2749_);
lean_dec(v_fst_2748_);
lean_dec(v_fst_2746_);
v___y_2693_ = v_isEq_2736_;
v_isHEq_2694_ = v___x_2558_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
v___y_2698_ = v___y_2740_;
goto v___jp_2692_;
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_del_object(v___x_2751_);
lean_dec(v_snd_2749_);
lean_dec(v_fst_2748_);
lean_dec(v_fst_2746_);
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2834_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2753_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2753_);
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
}
else
{
lean_dec(v_a_2742_);
v___y_2693_ = v_isEq_2736_;
v_isHEq_2694_ = v___x_2611_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
v___y_2698_ = v___y_2740_;
goto v___jp_2692_;
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2843_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2741_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2741_);
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
v___jp_2851_:
{
lean_object* v___x_2856_; 
lean_inc_ref(v___x_2612_);
v___x_2856_ = l_Lean_Meta_matchEq_x3f(v___x_2612_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
if (lean_obj_tag(v_a_2857_) == 1)
{
lean_object* v_val_2858_; lean_object* v_snd_2859_; lean_object* v_fst_2860_; lean_object* v_snd_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2933_; 
v_val_2858_ = lean_ctor_get(v_a_2857_, 0);
lean_inc(v_val_2858_);
lean_dec_ref_known(v_a_2857_, 1);
v_snd_2859_ = lean_ctor_get(v_val_2858_, 1);
lean_inc(v_snd_2859_);
lean_dec(v_val_2858_);
v_fst_2860_ = lean_ctor_get(v_snd_2859_, 0);
v_snd_2861_ = lean_ctor_get(v_snd_2859_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_snd_2859_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2863_ = v_snd_2859_;
v_isShared_2864_ = v_isSharedCheck_2933_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_snd_2861_);
lean_inc(v_fst_2860_);
lean_dec(v_snd_2859_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2933_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2860_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
if (lean_obj_tag(v_a_2866_) == 1)
{
lean_object* v_val_2867_; lean_object* v___x_2868_; 
v_val_2867_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v_a_2866_, 1);
v___x_2868_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2861_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
if (lean_obj_tag(v_a_2869_) == 1)
{
lean_object* v_toConstantVal_2870_; lean_object* v_val_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2916_; 
v_toConstantVal_2870_ = lean_ctor_get(v_val_2867_, 0);
lean_inc_ref(v_toConstantVal_2870_);
lean_dec(v_val_2867_);
v_val_2871_ = lean_ctor_get(v_a_2869_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_a_2869_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2873_ = v_a_2869_;
v_isShared_2874_ = v_isSharedCheck_2916_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_val_2871_);
lean_dec(v_a_2869_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2916_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v_toConstantVal_2875_; lean_object* v_name_2876_; lean_object* v_name_2877_; uint8_t v___x_2878_; 
v_toConstantVal_2875_ = lean_ctor_get(v_val_2871_, 0);
lean_inc_ref(v_toConstantVal_2875_);
lean_dec(v_val_2871_);
v_name_2876_ = lean_ctor_get(v_toConstantVal_2870_, 0);
lean_inc(v_name_2876_);
lean_dec_ref(v_toConstantVal_2870_);
v_name_2877_ = lean_ctor_get(v_toConstantVal_2875_, 0);
lean_inc(v_name_2877_);
lean_dec_ref(v_toConstantVal_2875_);
v___x_2878_ = lean_name_eq(v_name_2876_, v_name_2877_);
lean_dec(v_name_2877_);
lean_dec(v_name_2876_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec_ref(v_config_2547_);
lean_inc(v_mvarId_2548_);
v___x_2879_ = l_Lean_MVarId_getType(v_mvarId_2548_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = l_Lean_LocalDecl_toExpr(v_val_2579_);
v___x_2882_ = l_Lean_Meta_mkNoConfusion(v_a_2880_, v___x_2881_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v___x_2884_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2548_, v_a_2883_, v___y_2853_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2887_; 
lean_dec_ref_known(v___x_2884_, 1);
v___x_2885_ = lean_box(v___x_2558_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v___x_2885_);
v___x_2887_ = v___x_2873_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2885_);
v___x_2887_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2889_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v___x_2583_);
lean_ctor_set(v___x_2863_, 0, v___x_2887_);
v___x_2889_ = v___x_2863_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2583_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
v_a_2565_ = v___x_2889_;
goto v___jp_2564_;
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_del_object(v___x_2873_);
lean_del_object(v___x_2863_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_2892_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2884_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2884_);
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
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_del_object(v___x_2873_);
lean_del_object(v___x_2863_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_2900_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2882_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2882_);
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
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_del_object(v___x_2873_);
lean_del_object(v___x_2863_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_2908_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2879_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2879_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_del_object(v___x_2873_);
lean_del_object(v___x_2863_);
v_isEq_2736_ = v___x_2558_;
v___y_2737_ = v___y_2852_;
v___y_2738_ = v___y_2853_;
v___y_2739_ = v___y_2854_;
v___y_2740_ = v___y_2855_;
goto v___jp_2735_;
}
}
}
else
{
lean_dec(v_a_2869_);
lean_dec(v_val_2867_);
lean_del_object(v___x_2863_);
v_isEq_2736_ = v___x_2558_;
v___y_2737_ = v___y_2852_;
v___y_2738_ = v___y_2853_;
v___y_2739_ = v___y_2854_;
v___y_2740_ = v___y_2855_;
goto v___jp_2735_;
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_val_2867_);
lean_del_object(v___x_2863_);
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2917_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2868_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2868_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_dec(v_a_2866_);
lean_del_object(v___x_2863_);
lean_dec(v_snd_2861_);
v_isEq_2736_ = v___x_2558_;
v___y_2737_ = v___y_2852_;
v___y_2738_ = v___y_2853_;
v___y_2739_ = v___y_2854_;
v___y_2740_ = v___y_2855_;
goto v___jp_2735_;
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_del_object(v___x_2863_);
lean_dec(v_snd_2861_);
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2925_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2865_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2865_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
else
{
lean_dec(v_a_2857_);
v_isEq_2736_ = v___x_2611_;
v___y_2737_ = v___y_2852_;
v___y_2738_ = v___y_2853_;
v___y_2739_ = v___y_2854_;
v___y_2740_ = v___y_2855_;
goto v___jp_2735_;
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2934_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2856_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2856_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
v___jp_2942_:
{
lean_object* v___x_2947_; 
lean_inc_ref(v___x_2612_);
v___x_2947_ = l_Lean_refutableHasNotBit_x3f(v___x_2612_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
if (lean_obj_tag(v_a_2948_) == 1)
{
lean_object* v_val_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec_ref(v_config_2547_);
v_val_2949_ = lean_ctor_get(v_a_2948_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_a_2948_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2951_ = v_a_2948_;
v_isShared_2952_ = v_isSharedCheck_2988_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_val_2949_);
lean_dec(v_a_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2988_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; 
lean_inc(v_mvarId_2548_);
v___x_2953_ = l_Lean_MVarId_getType(v_mvarId_2548_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = l_Lean_LocalDecl_toExpr(v_val_2579_);
v___x_2956_ = l_Lean_Meta_mkAbsurd(v_a_2954_, v_val_2949_, v___x_2955_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v___x_2958_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2548_, v_a_2957_, v___y_2944_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
lean_dec_ref_known(v___x_2958_, 1);
v___x_2959_ = lean_box(v___x_2558_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2959_);
v___x_2961_ = v___x_2951_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v___x_2583_);
v_a_2565_ = v___x_2962_;
goto v___jp_2564_;
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_del_object(v___x_2951_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_2964_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2958_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2958_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_del_object(v___x_2951_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_2972_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2956_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2956_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_del_object(v___x_2951_);
lean_dec(v_val_2949_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_2980_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2953_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2953_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
else
{
lean_object* v___x_2989_; 
lean_dec(v_a_2948_);
lean_inc_ref(v___x_2612_);
v___x_2989_ = l_Lean_Meta_matchNe_x3f(v___x_2612_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
if (lean_obj_tag(v_a_2990_) == 1)
{
lean_object* v_val_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3060_; 
v_val_2991_ = lean_ctor_get(v_a_2990_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_a_2990_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_2993_ = v_a_2990_;
v_isShared_2994_ = v_isSharedCheck_3060_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_val_2991_);
lean_dec(v_a_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3060_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v_snd_2995_; lean_object* v_fst_2996_; lean_object* v_snd_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3059_; 
v_snd_2995_ = lean_ctor_get(v_val_2991_, 1);
lean_inc(v_snd_2995_);
lean_dec(v_val_2991_);
v_fst_2996_ = lean_ctor_get(v_snd_2995_, 0);
v_snd_2997_ = lean_ctor_get(v_snd_2995_, 1);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_snd_2995_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_2999_ = v_snd_2995_;
v_isShared_3000_ = v_isSharedCheck_3059_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_snd_2997_);
lean_inc(v_fst_2996_);
lean_dec(v_snd_2995_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3059_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; 
lean_inc(v_fst_2996_);
v___x_3001_ = l_Lean_Meta_isExprDefEq(v_fst_2996_, v_snd_2997_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; uint8_t v___x_3003_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = lean_unbox(v_a_3002_);
lean_dec(v_a_3002_);
if (v___x_3003_ == 0)
{
lean_del_object(v___x_2999_);
lean_dec(v_fst_2996_);
lean_del_object(v___x_2993_);
v___y_2852_ = v___y_2943_;
v___y_2853_ = v___y_2944_;
v___y_2854_ = v___y_2945_;
v___y_2855_ = v___y_2946_;
goto v___jp_2851_;
}
else
{
lean_object* v___x_3004_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec_ref(v_config_2547_);
lean_inc(v_mvarId_2548_);
v___x_3004_ = l_Lean_MVarId_getType(v_mvarId_2548_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = l_Lean_Meta_mkEqRefl(v_fst_2996_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = l_Lean_LocalDecl_toExpr(v_val_2579_);
v___x_3009_ = l_Lean_Meta_mkAbsurd(v_a_3005_, v_a_3007_, v___x_3008_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3011_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2548_, v_a_3010_, v___y_2944_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v___x_3012_; lean_object* v___x_3014_; 
lean_dec_ref_known(v___x_3011_, 1);
v___x_3012_ = lean_box(v___x_2558_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_3012_);
v___x_3014_ = v___x_2993_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3016_; 
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 1, v___x_2583_);
lean_ctor_set(v___x_2999_, 0, v___x_3014_);
v___x_3016_ = v___x_2999_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_2583_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
v_a_2565_ = v___x_3016_;
goto v___jp_2564_;
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_del_object(v___x_2999_);
lean_del_object(v___x_2993_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_3019_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3011_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3011_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_del_object(v___x_2999_);
lean_del_object(v___x_2993_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_3027_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3009_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3009_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_a_3005_);
lean_del_object(v___x_2999_);
lean_del_object(v___x_2993_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_3035_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3006_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3006_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_del_object(v___x_2999_);
lean_dec(v_fst_2996_);
lean_del_object(v___x_2993_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
v_a_3043_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3004_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3004_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_del_object(v___x_2999_);
lean_dec(v_fst_2996_);
lean_del_object(v___x_2993_);
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_3051_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3001_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3001_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2990_);
v___y_2852_ = v___y_2943_;
v___y_2853_ = v___y_2944_;
v___y_2854_ = v___y_2945_;
v___y_2855_ = v___y_2946_;
goto v___jp_2851_;
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_3061_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_2989_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_2989_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec_ref(v___x_2612_);
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_3069_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_2947_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_2947_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
else
{
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_2573_ = v___x_2584_;
goto v___jp_2572_;
}
v___jp_2585_:
{
uint8_t v_emptyType_2592_; 
v_emptyType_2592_ = lean_ctor_get_uint8(v_config_2547_, sizeof(void*)*1 + 1);
if (v_emptyType_2592_ == 0)
{
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_2573_ = v___x_2584_;
goto v___jp_2572_;
}
else
{
if (v___y_2587_ == 0)
{
if (v___y_2586_ == 0)
{
lean_object* v_searchFuel_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_searchFuel_2593_ = lean_ctor_get(v_config_2547_, 0);
v___x_2594_ = l_Lean_LocalDecl_fvarId(v_val_2579_);
lean_dec(v_val_2579_);
lean_inc(v_searchFuel_2593_);
lean_inc(v_mvarId_2548_);
v___x_2595_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2548_, v___x_2594_, v_searchFuel_2593_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; uint8_t v___x_2597_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = lean_unbox(v_a_2596_);
lean_dec(v_a_2596_);
if (v___x_2597_ == 0)
{
lean_del_object(v___x_2581_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_2573_ = v___x_2584_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v___x_2598_ = lean_box(v___x_2558_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2598_);
v___x_2600_ = v___x_2581_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___x_2583_);
v_a_2565_ = v___x_2601_;
goto v___jp_2564_;
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_del_object(v___x_2581_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2548_);
lean_dec_ref(v_config_2547_);
v_a_2603_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2595_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2595_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_2573_ = v___x_2584_;
goto v___jp_2572_;
}
}
else
{
lean_del_object(v___x_2581_);
lean_dec(v_val_2579_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v_a_2573_ = v___x_2584_;
goto v___jp_2572_;
}
}
}
}
}
v___jp_2564_:
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2565_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2566_);
v___x_2568_ = v___x_2562_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_snd_2560_);
v___x_2568_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
return v___x_2569_;
}
}
v___jp_2572_:
{
lean_object* v___x_2574_; size_t v___x_2575_; size_t v___x_2576_; lean_object* v___x_2577_; 
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2571_);
lean_ctor_set(v___x_2574_, 1, v_a_2573_);
v___x_2575_ = ((size_t)1ULL);
v___x_2576_ = lean_usize_add(v_i_2551_, v___x_2575_);
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2547_, v_mvarId_2548_, v_as_2549_, v_sz_2550_, v___x_2576_, v___x_2574_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
return v___x_2577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3143_, lean_object* v_mvarId_3144_, lean_object* v_as_3145_, lean_object* v_sz_3146_, lean_object* v_i_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
size_t v_sz_boxed_3154_; size_t v_i_boxed_3155_; lean_object* v_res_3156_; 
v_sz_boxed_3154_ = lean_unbox_usize(v_sz_3146_);
lean_dec(v_sz_3146_);
v_i_boxed_3155_ = lean_unbox_usize(v_i_3147_);
lean_dec(v_i_3147_);
v_res_3156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3143_, v_mvarId_3144_, v_as_3145_, v_sz_boxed_3154_, v_i_boxed_3155_, v_b_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec_ref(v_as_3145_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3160_, lean_object* v_mvarId_3161_, lean_object* v_as_3162_, size_t v_sz_3163_, size_t v_i_3164_, lean_object* v_b_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
uint8_t v___x_3171_; 
v___x_3171_ = lean_usize_dec_lt(v_i_3164_, v_sz_3163_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; 
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v_b_3165_);
return v___x_3172_;
}
else
{
lean_object* v_snd_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3786_; 
v_snd_3173_ = lean_ctor_get(v_b_3165_, 1);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_b_3165_);
if (v_isSharedCheck_3786_ == 0)
{
lean_object* v_unused_3787_; 
v_unused_3787_ = lean_ctor_get(v_b_3165_, 0);
lean_dec(v_unused_3787_);
v___x_3175_ = v_b_3165_;
v_isShared_3176_ = v_isSharedCheck_3786_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_snd_3173_);
lean_dec(v_b_3165_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3786_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_a_3178_; lean_object* v___x_3184_; lean_object* v_a_3186_; lean_object* v_a_3191_; 
v___x_3184_ = lean_box(0);
v_a_3191_ = lean_array_uget(v_as_3162_, v_i_3164_);
if (lean_obj_tag(v_a_3191_) == 0)
{
lean_del_object(v___x_3175_);
v_a_3186_ = v_snd_3173_;
goto v___jp_3185_;
}
else
{
lean_object* v_val_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3785_; 
v_val_3192_ = lean_ctor_get(v_a_3191_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_a_3191_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3194_ = v_a_3191_;
v_isShared_3195_ = v_isSharedCheck_3785_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_val_3192_);
lean_dec(v_a_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3785_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___y_3199_; uint8_t v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; uint8_t v___x_3225_; 
v___x_3196_ = lean_box(0);
v___x_3197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3225_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3192_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; uint8_t v___y_3228_; uint8_t v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; uint8_t v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; lean_object* v_a_3258_; uint8_t v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; uint8_t v___y_3270_; lean_object* v___y_3271_; uint8_t v___y_3315_; uint8_t v_isHEq_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; uint8_t v_isEq_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___x_3715_; 
v___x_3226_ = l_Lean_LocalDecl_type(v_val_3192_);
lean_inc_ref(v___x_3226_);
v___x_3715_ = l_Lean_Meta_matchNot_x3f(v___x_3226_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
if (lean_obj_tag(v_a_3716_) == 1)
{
lean_object* v_val_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3776_; 
v_val_3717_ = lean_ctor_get(v_a_3716_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_a_3716_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3719_ = v_a_3716_;
v_isShared_3720_ = v_isSharedCheck_3776_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_val_3717_);
lean_dec(v_a_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3776_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3717_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
if (lean_obj_tag(v_a_3722_) == 1)
{
lean_object* v_val_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3767_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec_ref(v_config_3160_);
v_val_3723_ = lean_ctor_get(v_a_3722_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_a_3722_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3725_ = v_a_3722_;
v_isShared_3726_ = v_isSharedCheck_3767_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_val_3723_);
lean_dec(v_a_3722_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3767_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3727_; 
lean_inc(v_mvarId_3161_);
v___x_3727_ = l_Lean_MVarId_getType(v_mvarId_3161_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = l_Lean_LocalDecl_toExpr(v_val_3192_);
v___x_3730_ = l_Lean_mkFVar(v_val_3723_);
v___x_3731_ = l_Lean_Expr_app___override(v___x_3729_, v___x_3730_);
v___x_3732_ = l_Lean_Meta_mkFalseElim(v_a_3728_, v___x_3731_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3734_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___x_3732_, 1);
v___x_3734_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3161_, v_a_3733_, v___y_3167_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v___x_3735_; lean_object* v___x_3737_; 
lean_dec_ref_known(v___x_3734_, 1);
v___x_3735_ = lean_box(v___x_3171_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3735_);
v___x_3737_ = v___x_3725_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3735_);
v___x_3737_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3738_; lean_object* v___x_3740_; 
v___x_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
lean_ctor_set(v___x_3738_, 1, v___x_3196_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set_tag(v___x_3719_, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3738_);
v___x_3740_ = v___x_3719_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
v_a_3178_ = v___x_3740_;
goto v___jp_3177_;
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_del_object(v___x_3725_);
lean_del_object(v___x_3719_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3743_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3734_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3734_);
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
lean_del_object(v___x_3725_);
lean_del_object(v___x_3719_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3751_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3732_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3732_);
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
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_del_object(v___x_3725_);
lean_dec(v_val_3723_);
lean_del_object(v___x_3719_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3759_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3727_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3727_);
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
else
{
lean_dec(v_a_3722_);
lean_del_object(v___x_3719_);
v___y_3579_ = v___y_3166_;
v___y_3580_ = v___y_3167_;
v___y_3581_ = v___y_3168_;
v___y_3582_ = v___y_3169_;
goto v___jp_3578_;
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_del_object(v___x_3719_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3768_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3721_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3721_);
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
lean_dec(v_a_3716_);
v___y_3579_ = v___y_3166_;
v___y_3580_ = v___y_3167_;
v___y_3581_ = v___y_3168_;
v___y_3582_ = v___y_3169_;
goto v___jp_3578_;
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3777_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3715_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3715_);
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
v___jp_3227_:
{
uint8_t v_genDiseq_3234_; 
v_genDiseq_3234_ = lean_ctor_get_uint8(v_config_3160_, sizeof(void*)*1 + 2);
if (v_genDiseq_3234_ == 0)
{
lean_dec_ref(v___x_3226_);
v___y_3199_ = v___y_3228_;
v___y_3200_ = v___y_3229_;
v___y_3201_ = v___y_3230_;
v___y_3202_ = v___y_3231_;
v___y_3203_ = v___y_3232_;
v___y_3204_ = v___y_3233_;
goto v___jp_3198_;
}
else
{
uint8_t v___x_3235_; 
v___x_3235_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3226_);
lean_dec_ref(v___x_3226_);
if (v___x_3235_ == 0)
{
v___y_3199_ = v___y_3228_;
v___y_3200_ = v___y_3229_;
v___y_3201_ = v___y_3230_;
v___y_3202_ = v___y_3231_;
v___y_3203_ = v___y_3232_;
v___y_3204_ = v___y_3233_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3236_; 
lean_inc(v_val_3192_);
lean_inc(v_mvarId_3161_);
v___x_3236_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3161_, v_val_3192_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; uint8_t v___x_3238_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3236_, 1);
v___x_3238_ = lean_unbox(v_a_3237_);
lean_dec(v_a_3237_);
if (v___x_3238_ == 0)
{
v___y_3199_ = v___y_3228_;
v___y_3200_ = v___y_3229_;
v___y_3201_ = v___y_3230_;
v___y_3202_ = v___y_3231_;
v___y_3203_ = v___y_3232_;
v___y_3204_ = v___y_3233_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v___x_3239_ = lean_box(v___x_3171_);
v___x_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
lean_ctor_set(v___x_3241_, 1, v___x_3196_);
v___x_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
v_a_3178_ = v___x_3242_;
goto v___jp_3177_;
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3243_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3236_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3236_);
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
v___jp_3251_:
{
uint8_t v___x_3259_; 
v___x_3259_ = l_Lean_Exception_isInterrupt(v_a_3258_);
if (v___x_3259_ == 0)
{
uint8_t v___x_3260_; 
lean_inc_ref(v_a_3258_);
v___x_3260_ = l_Lean_Exception_isRuntime(v_a_3258_);
if (v___x_3260_ == 0)
{
lean_dec_ref(v_a_3258_);
v___y_3228_ = v___y_3252_;
v___y_3229_ = v___y_3257_;
v___y_3230_ = v___y_3253_;
v___y_3231_ = v___y_3254_;
v___y_3232_ = v___y_3256_;
v___y_3233_ = v___y_3255_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3261_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v___x_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_a_3258_);
return v___x_3261_;
}
}
else
{
lean_object* v___x_3262_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v___x_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3262_, 0, v_a_3258_);
return v___x_3262_;
}
}
v___jp_3263_:
{
if (lean_obj_tag(v___y_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v_a_3272_ = lean_ctor_get(v___y_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___y_3271_, 1);
v___x_3273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3274_ = l_Lean_Expr_isConstOf(v_a_3272_, v___x_3273_);
lean_dec(v_a_3272_);
if (v___x_3274_ == 0)
{
lean_dec_ref(v___y_3267_);
v___y_3228_ = v___y_3264_;
v___y_3229_ = v___y_3270_;
v___y_3230_ = v___y_3265_;
v___y_3231_ = v___y_3266_;
v___y_3232_ = v___y_3269_;
v___y_3233_ = v___y_3268_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3275_; 
lean_inc_ref(v___y_3267_);
v___x_3275_ = l_Lean_Meta_mkEqRefl(v___y_3267_, v___y_3265_, v___y_3266_, v___y_3269_, v___y_3268_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3277_; lean_object* v_dummy_3278_; lean_object* v_nargs_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v___x_3277_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3278_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3279_ = l_Lean_Expr_getAppNumArgs(v___y_3267_);
lean_inc(v_nargs_3279_);
v___x_3280_ = lean_mk_array(v_nargs_3279_, v_dummy_3278_);
v___x_3281_ = lean_unsigned_to_nat(1u);
v___x_3282_ = lean_nat_sub(v_nargs_3279_, v___x_3281_);
lean_dec(v_nargs_3279_);
v___x_3283_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3267_, v___x_3280_, v___x_3282_);
v___x_3284_ = lean_array_push(v___x_3283_, v_a_3276_);
v___x_3285_ = l_Lean_mkAppN(v___x_3277_, v___x_3284_);
lean_dec_ref(v___x_3284_);
lean_inc(v_mvarId_3161_);
v___x_3286_ = l_Lean_MVarId_getType(v_mvarId_3161_, v___y_3265_, v___y_3266_, v___y_3269_, v___y_3268_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
lean_inc(v_val_3192_);
v___x_3288_ = l_Lean_LocalDecl_toExpr(v_val_3192_);
v___x_3289_ = l_Lean_Meta_mkAbsurd(v_a_3287_, v___x_3288_, v___x_3285_, v___y_3265_, v___y_3266_, v___y_3269_, v___y_3268_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3309_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3309_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3309_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; 
lean_inc(v_mvarId_3161_);
v___x_3294_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3161_, v_a_3290_, v___y_3266_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3306_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; 
v_unused_3307_ = lean_ctor_get(v___x_3294_, 0);
lean_dec(v_unused_3307_);
v___x_3296_ = v___x_3294_;
v_isShared_3297_ = v_isSharedCheck_3306_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v___x_3294_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3306_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3298_ = lean_box(v___x_3171_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set_tag(v___x_3296_, 1);
lean_ctor_set(v___x_3296_, 0, v___x_3298_);
v___x_3300_ = v___x_3296_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3196_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3301_);
v___x_3303_ = v___x_3292_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
v_a_3178_ = v___x_3303_;
goto v___jp_3177_;
}
}
}
}
else
{
lean_object* v_a_3308_; 
lean_del_object(v___x_3292_);
v_a_3308_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v___x_3294_, 1);
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3268_;
v___y_3256_ = v___y_3269_;
v___y_3257_ = v___y_3270_;
v_a_3258_ = v_a_3308_;
goto v___jp_3251_;
}
}
}
else
{
lean_object* v_a_3310_; 
v_a_3310_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3289_, 1);
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3268_;
v___y_3256_ = v___y_3269_;
v___y_3257_ = v___y_3270_;
v_a_3258_ = v_a_3310_;
goto v___jp_3251_;
}
}
else
{
lean_object* v_a_3311_; 
lean_dec_ref(v___x_3285_);
v_a_3311_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3286_, 1);
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3268_;
v___y_3256_ = v___y_3269_;
v___y_3257_ = v___y_3270_;
v_a_3258_ = v_a_3311_;
goto v___jp_3251_;
}
}
else
{
lean_object* v_a_3312_; 
lean_dec_ref(v___y_3267_);
v_a_3312_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3275_, 1);
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3268_;
v___y_3256_ = v___y_3269_;
v___y_3257_ = v___y_3270_;
v_a_3258_ = v_a_3312_;
goto v___jp_3251_;
}
}
}
else
{
lean_object* v_a_3313_; 
lean_dec_ref(v___y_3267_);
v_a_3313_ = lean_ctor_get(v___y_3271_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___y_3271_, 1);
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3268_;
v___y_3256_ = v___y_3269_;
v___y_3257_ = v___y_3270_;
v_a_3258_ = v_a_3313_;
goto v___jp_3251_;
}
}
v___jp_3314_:
{
uint8_t v_useDecide_3321_; 
v_useDecide_3321_ = lean_ctor_get_uint8(v_config_3160_, sizeof(void*)*1);
if (v_useDecide_3321_ == 0)
{
v___y_3228_ = v_isHEq_3316_;
v___y_3229_ = v___y_3315_;
v___y_3230_ = v___y_3317_;
v___y_3231_ = v___y_3318_;
v___y_3232_ = v___y_3319_;
v___y_3233_ = v___y_3320_;
goto v___jp_3227_;
}
else
{
uint8_t v___x_3322_; 
v___x_3322_ = l_Lean_Expr_hasFVar(v___x_3226_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; 
lean_inc_ref(v___x_3226_);
v___x_3323_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3226_, v___y_3318_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; uint8_t v___x_3325_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3323_, 1);
v___x_3325_ = l_Lean_Expr_hasMVar(v_a_3324_);
if (v___x_3325_ == 0)
{
uint8_t v___x_3326_; 
v___x_3326_ = l_Lean_Expr_hasFVar(v_a_3324_);
lean_dec(v_a_3324_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; 
lean_inc_ref(v___x_3226_);
v___x_3327_ = l_Lean_Meta_mkDecide(v___x_3226_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3329_; uint8_t v_transparency_3330_; uint8_t v___x_3331_; uint8_t v___x_3332_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = l_Lean_Meta_Context_config(v___y_3317_);
v_transparency_3330_ = lean_ctor_get_uint8(v___x_3329_, 9);
lean_dec_ref(v___x_3329_);
v___x_3331_ = 1;
v___x_3332_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3330_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_object* v_keyedConfig_3333_; uint8_t v_trackZetaDelta_3334_; lean_object* v_zetaDeltaSet_3335_; lean_object* v_lctx_3336_; lean_object* v_localInstances_3337_; lean_object* v_defEqCtx_x3f_3338_; lean_object* v_synthPendingDepth_3339_; lean_object* v_customCanUnfoldPredicate_x3f_3340_; uint8_t v_univApprox_3341_; uint8_t v_inTypeClassResolution_3342_; uint8_t v_cacheInferType_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v_keyedConfig_3333_ = lean_ctor_get(v___y_3317_, 0);
v_trackZetaDelta_3334_ = lean_ctor_get_uint8(v___y_3317_, sizeof(void*)*7);
v_zetaDeltaSet_3335_ = lean_ctor_get(v___y_3317_, 1);
v_lctx_3336_ = lean_ctor_get(v___y_3317_, 2);
v_localInstances_3337_ = lean_ctor_get(v___y_3317_, 3);
v_defEqCtx_x3f_3338_ = lean_ctor_get(v___y_3317_, 4);
v_synthPendingDepth_3339_ = lean_ctor_get(v___y_3317_, 5);
v_customCanUnfoldPredicate_x3f_3340_ = lean_ctor_get(v___y_3317_, 6);
v_univApprox_3341_ = lean_ctor_get_uint8(v___y_3317_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3342_ = lean_ctor_get_uint8(v___y_3317_, sizeof(void*)*7 + 2);
v_cacheInferType_3343_ = lean_ctor_get_uint8(v___y_3317_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3333_);
v___x_3344_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3331_, v_keyedConfig_3333_);
lean_inc(v_customCanUnfoldPredicate_x3f_3340_);
lean_inc(v_synthPendingDepth_3339_);
lean_inc(v_defEqCtx_x3f_3338_);
lean_inc_ref(v_localInstances_3337_);
lean_inc_ref(v_lctx_3336_);
lean_inc(v_zetaDeltaSet_3335_);
v___x_3345_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
lean_ctor_set(v___x_3345_, 1, v_zetaDeltaSet_3335_);
lean_ctor_set(v___x_3345_, 2, v_lctx_3336_);
lean_ctor_set(v___x_3345_, 3, v_localInstances_3337_);
lean_ctor_set(v___x_3345_, 4, v_defEqCtx_x3f_3338_);
lean_ctor_set(v___x_3345_, 5, v_synthPendingDepth_3339_);
lean_ctor_set(v___x_3345_, 6, v_customCanUnfoldPredicate_x3f_3340_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*7, v_trackZetaDelta_3334_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*7 + 1, v_univApprox_3341_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3342_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*7 + 3, v_cacheInferType_3343_);
lean_inc(v___y_3320_);
lean_inc_ref(v___y_3319_);
lean_inc(v___y_3318_);
lean_inc(v_a_3328_);
v___x_3346_ = lean_whnf(v_a_3328_, v___x_3345_, v___y_3318_, v___y_3319_, v___y_3320_);
v___y_3264_ = v_isHEq_3316_;
v___y_3265_ = v___y_3317_;
v___y_3266_ = v___y_3318_;
v___y_3267_ = v_a_3328_;
v___y_3268_ = v___y_3320_;
v___y_3269_ = v___y_3319_;
v___y_3270_ = v___y_3315_;
v___y_3271_ = v___x_3346_;
goto v___jp_3263_;
}
else
{
lean_object* v___x_3347_; 
lean_inc(v___y_3320_);
lean_inc_ref(v___y_3319_);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3317_);
lean_inc(v_a_3328_);
v___x_3347_ = lean_whnf(v_a_3328_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
v___y_3264_ = v_isHEq_3316_;
v___y_3265_ = v___y_3317_;
v___y_3266_ = v___y_3318_;
v___y_3267_ = v_a_3328_;
v___y_3268_ = v___y_3320_;
v___y_3269_ = v___y_3319_;
v___y_3270_ = v___y_3315_;
v___y_3271_ = v___x_3347_;
goto v___jp_3263_;
}
}
else
{
lean_object* v_a_3348_; 
v_a_3348_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3327_, 1);
v___y_3252_ = v_isHEq_3316_;
v___y_3253_ = v___y_3317_;
v___y_3254_ = v___y_3318_;
v___y_3255_ = v___y_3320_;
v___y_3256_ = v___y_3319_;
v___y_3257_ = v___y_3315_;
v_a_3258_ = v_a_3348_;
goto v___jp_3251_;
}
}
else
{
v___y_3228_ = v_isHEq_3316_;
v___y_3229_ = v___y_3315_;
v___y_3230_ = v___y_3317_;
v___y_3231_ = v___y_3318_;
v___y_3232_ = v___y_3319_;
v___y_3233_ = v___y_3320_;
goto v___jp_3227_;
}
}
else
{
lean_dec(v_a_3324_);
v___y_3228_ = v_isHEq_3316_;
v___y_3229_ = v___y_3315_;
v___y_3230_ = v___y_3317_;
v___y_3231_ = v___y_3318_;
v___y_3232_ = v___y_3319_;
v___y_3233_ = v___y_3320_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3349_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3323_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3323_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
v___y_3228_ = v_isHEq_3316_;
v___y_3229_ = v___y_3315_;
v___y_3230_ = v___y_3317_;
v___y_3231_ = v___y_3318_;
v___y_3232_ = v___y_3319_;
v___y_3233_ = v___y_3320_;
goto v___jp_3227_;
}
}
}
v___jp_3357_:
{
lean_object* v___x_3363_; 
lean_inc_ref(v___x_3226_);
v___x_3363_ = l_Lean_Meta_matchHEq_x3f(v___x_3226_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
if (lean_obj_tag(v_a_3364_) == 1)
{
lean_object* v_val_3365_; lean_object* v_snd_3366_; lean_object* v_snd_3367_; lean_object* v_fst_3368_; lean_object* v_fst_3369_; lean_object* v_fst_3370_; lean_object* v_snd_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3471_; 
v_val_3365_ = lean_ctor_get(v_a_3364_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v_a_3364_, 1);
v_snd_3366_ = lean_ctor_get(v_val_3365_, 1);
lean_inc(v_snd_3366_);
v_snd_3367_ = lean_ctor_get(v_snd_3366_, 1);
lean_inc(v_snd_3367_);
v_fst_3368_ = lean_ctor_get(v_val_3365_, 0);
lean_inc(v_fst_3368_);
lean_dec(v_val_3365_);
v_fst_3369_ = lean_ctor_get(v_snd_3366_, 0);
lean_inc(v_fst_3369_);
lean_dec(v_snd_3366_);
v_fst_3370_ = lean_ctor_get(v_snd_3367_, 0);
v_snd_3371_ = lean_ctor_get(v_snd_3367_, 1);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_snd_3367_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3373_ = v_snd_3367_;
v_isShared_3374_ = v_isSharedCheck_3471_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_snd_3371_);
lean_inc(v_fst_3370_);
lean_dec(v_snd_3367_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3471_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3369_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
if (lean_obj_tag(v_a_3376_) == 1)
{
lean_object* v_val_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3462_; 
v_val_3377_ = lean_ctor_get(v_a_3376_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_a_3376_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3379_ = v_a_3376_;
v_isShared_3380_ = v_isSharedCheck_3462_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_val_3377_);
lean_dec(v_a_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3462_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3371_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
if (lean_obj_tag(v_a_3382_) == 1)
{
lean_object* v_toConstantVal_3383_; lean_object* v_val_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3453_; 
v_toConstantVal_3383_ = lean_ctor_get(v_val_3377_, 0);
lean_inc_ref(v_toConstantVal_3383_);
lean_dec(v_val_3377_);
v_val_3384_ = lean_ctor_get(v_a_3382_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3386_ = v_a_3382_;
v_isShared_3387_ = v_isSharedCheck_3453_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_val_3384_);
lean_dec(v_a_3382_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3453_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v_toConstantVal_3388_; lean_object* v_name_3389_; lean_object* v_name_3390_; uint8_t v___x_3391_; 
v_toConstantVal_3388_ = lean_ctor_get(v_val_3384_, 0);
lean_inc_ref(v_toConstantVal_3388_);
lean_dec(v_val_3384_);
v_name_3389_ = lean_ctor_get(v_toConstantVal_3383_, 0);
lean_inc(v_name_3389_);
lean_dec_ref(v_toConstantVal_3383_);
v_name_3390_ = lean_ctor_get(v_toConstantVal_3388_, 0);
lean_inc(v_name_3390_);
lean_dec_ref(v_toConstantVal_3388_);
v___x_3391_ = lean_name_eq(v_name_3389_, v_name_3390_);
lean_dec(v_name_3390_);
lean_dec(v_name_3389_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Meta_isExprDefEq(v_fst_3368_, v_fst_3370_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; uint8_t v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v___x_3394_ = lean_unbox(v_a_3393_);
lean_dec(v_a_3393_);
if (v___x_3394_ == 0)
{
lean_del_object(v___x_3386_);
lean_del_object(v___x_3379_);
lean_del_object(v___x_3373_);
v___y_3315_ = v_isEq_3358_;
v_isHEq_3316_ = v___x_3171_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
v___y_3320_ = v___y_3362_;
goto v___jp_3314_;
}
else
{
lean_object* v___x_3395_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec_ref(v_config_3160_);
lean_inc(v_mvarId_3161_);
v___x_3395_ = l_Lean_MVarId_getType(v_mvarId_3161_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3395_, 1);
v___x_3397_ = l_Lean_LocalDecl_toExpr(v_val_3192_);
v___x_3398_ = l_Lean_Meta_mkEqOfHEq(v___x_3397_, v___x_3171_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
v___x_3400_ = l_Lean_Meta_mkNoConfusion(v_a_3396_, v_a_3399_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v___x_3402_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3161_, v_a_3401_, v___y_3360_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
lean_dec_ref_known(v___x_3402_, 1);
v___x_3403_ = lean_box(v___x_3171_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3403_);
v___x_3405_ = v___x_3386_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
lean_object* v___x_3407_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 1, v___x_3196_);
lean_ctor_set(v___x_3373_, 0, v___x_3405_);
v___x_3407_ = v___x_3373_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v___x_3196_);
v___x_3407_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3409_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set_tag(v___x_3379_, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3407_);
v___x_3409_ = v___x_3379_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
v_a_3178_ = v___x_3409_;
goto v___jp_3177_;
}
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_del_object(v___x_3386_);
lean_del_object(v___x_3379_);
lean_del_object(v___x_3373_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3413_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3402_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3402_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_del_object(v___x_3386_);
lean_del_object(v___x_3379_);
lean_del_object(v___x_3373_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3421_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3400_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3400_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec(v_a_3396_);
lean_del_object(v___x_3386_);
lean_del_object(v___x_3379_);
lean_del_object(v___x_3373_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3429_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3398_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3398_);
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
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_del_object(v___x_3386_);
lean_del_object(v___x_3379_);
lean_del_object(v___x_3373_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3437_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3395_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3395_);
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
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_del_object(v___x_3386_);
lean_del_object(v___x_3379_);
lean_del_object(v___x_3373_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3445_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3392_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3392_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_del_object(v___x_3386_);
lean_del_object(v___x_3379_);
lean_del_object(v___x_3373_);
lean_dec(v_fst_3370_);
lean_dec(v_fst_3368_);
v___y_3315_ = v_isEq_3358_;
v_isHEq_3316_ = v___x_3171_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
v___y_3320_ = v___y_3362_;
goto v___jp_3314_;
}
}
}
else
{
lean_dec(v_a_3382_);
lean_del_object(v___x_3379_);
lean_dec(v_val_3377_);
lean_del_object(v___x_3373_);
lean_dec(v_fst_3370_);
lean_dec(v_fst_3368_);
v___y_3315_ = v_isEq_3358_;
v_isHEq_3316_ = v___x_3171_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
v___y_3320_ = v___y_3362_;
goto v___jp_3314_;
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_del_object(v___x_3379_);
lean_dec(v_val_3377_);
lean_del_object(v___x_3373_);
lean_dec(v_fst_3370_);
lean_dec(v_fst_3368_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3454_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3381_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3381_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
}
else
{
lean_dec(v_a_3376_);
lean_del_object(v___x_3373_);
lean_dec(v_snd_3371_);
lean_dec(v_fst_3370_);
lean_dec(v_fst_3368_);
v___y_3315_ = v_isEq_3358_;
v_isHEq_3316_ = v___x_3171_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
v___y_3320_ = v___y_3362_;
goto v___jp_3314_;
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_del_object(v___x_3373_);
lean_dec(v_snd_3371_);
lean_dec(v_fst_3370_);
lean_dec(v_fst_3368_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3463_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3375_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3375_);
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
}
else
{
lean_dec(v_a_3364_);
v___y_3315_ = v_isEq_3358_;
v_isHEq_3316_ = v___x_3225_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
v___y_3320_ = v___y_3362_;
goto v___jp_3314_;
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3472_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3363_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3363_);
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
v___jp_3480_:
{
lean_object* v___x_3485_; 
lean_inc_ref(v___x_3226_);
v___x_3485_ = l_Lean_Meta_matchEq_x3f(v___x_3226_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
if (lean_obj_tag(v_a_3486_) == 1)
{
lean_object* v_val_3487_; lean_object* v_snd_3488_; lean_object* v_fst_3489_; lean_object* v_snd_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3569_; 
v_val_3487_ = lean_ctor_get(v_a_3486_, 0);
lean_inc(v_val_3487_);
lean_dec_ref_known(v_a_3486_, 1);
v_snd_3488_ = lean_ctor_get(v_val_3487_, 1);
lean_inc(v_snd_3488_);
lean_dec(v_val_3487_);
v_fst_3489_ = lean_ctor_get(v_snd_3488_, 0);
v_snd_3490_ = lean_ctor_get(v_snd_3488_, 1);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_snd_3488_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3492_ = v_snd_3488_;
v_isShared_3493_ = v_isSharedCheck_3569_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_snd_3490_);
lean_inc(v_fst_3489_);
lean_dec(v_snd_3488_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3569_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3489_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
if (lean_obj_tag(v_a_3495_) == 1)
{
lean_object* v_val_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3560_; 
v_val_3496_ = lean_ctor_get(v_a_3495_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_a_3495_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3498_ = v_a_3495_;
v_isShared_3499_ = v_isSharedCheck_3560_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_val_3496_);
lean_dec(v_a_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3560_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3490_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
if (lean_obj_tag(v_a_3501_) == 1)
{
lean_object* v_toConstantVal_3502_; lean_object* v_val_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3551_; 
v_toConstantVal_3502_ = lean_ctor_get(v_val_3496_, 0);
lean_inc_ref(v_toConstantVal_3502_);
lean_dec(v_val_3496_);
v_val_3503_ = lean_ctor_get(v_a_3501_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v_a_3501_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3505_ = v_a_3501_;
v_isShared_3506_ = v_isSharedCheck_3551_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_val_3503_);
lean_dec(v_a_3501_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3551_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_toConstantVal_3507_; lean_object* v_name_3508_; lean_object* v_name_3509_; uint8_t v___x_3510_; 
v_toConstantVal_3507_ = lean_ctor_get(v_val_3503_, 0);
lean_inc_ref(v_toConstantVal_3507_);
lean_dec(v_val_3503_);
v_name_3508_ = lean_ctor_get(v_toConstantVal_3502_, 0);
lean_inc(v_name_3508_);
lean_dec_ref(v_toConstantVal_3502_);
v_name_3509_ = lean_ctor_get(v_toConstantVal_3507_, 0);
lean_inc(v_name_3509_);
lean_dec_ref(v_toConstantVal_3507_);
v___x_3510_ = lean_name_eq(v_name_3508_, v_name_3509_);
lean_dec(v_name_3509_);
lean_dec(v_name_3508_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec_ref(v_config_3160_);
lean_inc(v_mvarId_3161_);
v___x_3511_ = l_Lean_MVarId_getType(v_mvarId_3161_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l_Lean_LocalDecl_toExpr(v_val_3192_);
v___x_3514_ = l_Lean_Meta_mkNoConfusion(v_a_3512_, v___x_3513_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3516_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___x_3516_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3161_, v_a_3515_, v___y_3482_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
lean_dec_ref_known(v___x_3516_, 1);
v___x_3517_ = lean_box(v___x_3171_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3517_);
v___x_3519_ = v___x_3505_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v___x_3196_);
lean_ctor_set(v___x_3492_, 0, v___x_3519_);
v___x_3521_ = v___x_3492_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v___x_3196_);
v___x_3521_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set_tag(v___x_3498_, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3521_);
v___x_3523_ = v___x_3498_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
v_a_3178_ = v___x_3523_;
goto v___jp_3177_;
}
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_del_object(v___x_3505_);
lean_del_object(v___x_3498_);
lean_del_object(v___x_3492_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3527_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3516_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3516_);
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
lean_del_object(v___x_3505_);
lean_del_object(v___x_3498_);
lean_del_object(v___x_3492_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3535_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3514_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3514_);
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
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_del_object(v___x_3505_);
lean_del_object(v___x_3498_);
lean_del_object(v___x_3492_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3543_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3511_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3511_);
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
else
{
lean_del_object(v___x_3505_);
lean_del_object(v___x_3498_);
lean_del_object(v___x_3492_);
v_isEq_3358_ = v___x_3171_;
v___y_3359_ = v___y_3481_;
v___y_3360_ = v___y_3482_;
v___y_3361_ = v___y_3483_;
v___y_3362_ = v___y_3484_;
goto v___jp_3357_;
}
}
}
else
{
lean_dec(v_a_3501_);
lean_del_object(v___x_3498_);
lean_dec(v_val_3496_);
lean_del_object(v___x_3492_);
v_isEq_3358_ = v___x_3171_;
v___y_3359_ = v___y_3481_;
v___y_3360_ = v___y_3482_;
v___y_3361_ = v___y_3483_;
v___y_3362_ = v___y_3484_;
goto v___jp_3357_;
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_del_object(v___x_3498_);
lean_dec(v_val_3496_);
lean_del_object(v___x_3492_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3552_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3500_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3500_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
}
else
{
lean_dec(v_a_3495_);
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
v_isEq_3358_ = v___x_3171_;
v___y_3359_ = v___y_3481_;
v___y_3360_ = v___y_3482_;
v___y_3361_ = v___y_3483_;
v___y_3362_ = v___y_3484_;
goto v___jp_3357_;
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_del_object(v___x_3492_);
lean_dec(v_snd_3490_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3561_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3494_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3494_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
else
{
lean_dec(v_a_3486_);
v_isEq_3358_ = v___x_3225_;
v___y_3359_ = v___y_3481_;
v___y_3360_ = v___y_3482_;
v___y_3361_ = v___y_3483_;
v___y_3362_ = v___y_3484_;
goto v___jp_3357_;
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3570_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3485_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3485_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
v___jp_3578_:
{
lean_object* v___x_3583_; 
lean_inc_ref(v___x_3226_);
v___x_3583_ = l_Lean_refutableHasNotBit_x3f(v___x_3226_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___x_3583_, 1);
if (lean_obj_tag(v_a_3584_) == 1)
{
lean_object* v_val_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec_ref(v_config_3160_);
v_val_3585_ = lean_ctor_get(v_a_3584_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_a_3584_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3587_ = v_a_3584_;
v_isShared_3588_ = v_isSharedCheck_3625_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_val_3585_);
lean_dec(v_a_3584_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3625_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; 
lean_inc(v_mvarId_3161_);
v___x_3589_ = l_Lean_MVarId_getType(v_mvarId_3161_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3589_, 1);
v___x_3591_ = l_Lean_LocalDecl_toExpr(v_val_3192_);
v___x_3592_ = l_Lean_Meta_mkAbsurd(v_a_3590_, v_val_3585_, v___x_3591_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3594_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3594_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3161_, v_a_3593_, v___y_3580_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3597_; 
lean_dec_ref_known(v___x_3594_, 1);
v___x_3595_ = lean_box(v___x_3171_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v___x_3595_);
v___x_3597_ = v___x_3587_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3595_);
v___x_3597_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
lean_ctor_set(v___x_3598_, 1, v___x_3196_);
v___x_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
v_a_3178_ = v___x_3599_;
goto v___jp_3177_;
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_del_object(v___x_3587_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3601_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3594_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3594_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
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
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_del_object(v___x_3587_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3609_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3592_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3592_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_del_object(v___x_3587_);
lean_dec(v_val_3585_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3617_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3589_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3589_);
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
}
else
{
lean_object* v___x_3626_; 
lean_dec(v_a_3584_);
lean_inc_ref(v___x_3226_);
v___x_3626_ = l_Lean_Meta_matchNe_x3f(v___x_3226_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref_known(v___x_3626_, 1);
if (lean_obj_tag(v_a_3627_) == 1)
{
lean_object* v_val_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3698_; 
v_val_3628_ = lean_ctor_get(v_a_3627_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_a_3627_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3630_ = v_a_3627_;
v_isShared_3631_ = v_isSharedCheck_3698_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_val_3628_);
lean_dec(v_a_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3698_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v_snd_3632_; lean_object* v_fst_3633_; lean_object* v_snd_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3697_; 
v_snd_3632_ = lean_ctor_get(v_val_3628_, 1);
lean_inc(v_snd_3632_);
lean_dec(v_val_3628_);
v_fst_3633_ = lean_ctor_get(v_snd_3632_, 0);
v_snd_3634_ = lean_ctor_get(v_snd_3632_, 1);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_snd_3632_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3636_ = v_snd_3632_;
v_isShared_3637_ = v_isSharedCheck_3697_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_snd_3634_);
lean_inc(v_fst_3633_);
lean_dec(v_snd_3632_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3697_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; 
lean_inc(v_fst_3633_);
v___x_3638_ = l_Lean_Meta_isExprDefEq(v_fst_3633_, v_snd_3634_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; uint8_t v___x_3640_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3638_, 1);
v___x_3640_ = lean_unbox(v_a_3639_);
lean_dec(v_a_3639_);
if (v___x_3640_ == 0)
{
lean_del_object(v___x_3636_);
lean_dec(v_fst_3633_);
lean_del_object(v___x_3630_);
v___y_3481_ = v___y_3579_;
v___y_3482_ = v___y_3580_;
v___y_3483_ = v___y_3581_;
v___y_3484_ = v___y_3582_;
goto v___jp_3480_;
}
else
{
lean_object* v___x_3641_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec_ref(v_config_3160_);
lean_inc(v_mvarId_3161_);
v___x_3641_ = l_Lean_MVarId_getType(v_mvarId_3161_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3643_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
v___x_3643_ = l_Lean_Meta_mkEqRefl(v_fst_3633_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
v___x_3645_ = l_Lean_LocalDecl_toExpr(v_val_3192_);
v___x_3646_ = l_Lean_Meta_mkAbsurd(v_a_3642_, v_a_3644_, v___x_3645_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3646_, 1);
v___x_3648_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3161_, v_a_3647_, v___y_3580_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3651_; 
lean_dec_ref_known(v___x_3648_, 1);
v___x_3649_ = lean_box(v___x_3171_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3649_);
v___x_3651_ = v___x_3630_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3653_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 1, v___x_3196_);
lean_ctor_set(v___x_3636_, 0, v___x_3651_);
v___x_3653_ = v___x_3636_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v___x_3196_);
v___x_3653_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3654_; 
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
v_a_3178_ = v___x_3654_;
goto v___jp_3177_;
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_del_object(v___x_3636_);
lean_del_object(v___x_3630_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3657_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3648_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3648_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_del_object(v___x_3636_);
lean_del_object(v___x_3630_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3665_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3646_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3646_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec(v_a_3642_);
lean_del_object(v___x_3636_);
lean_del_object(v___x_3630_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3673_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3643_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3643_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3636_);
lean_dec(v_fst_3633_);
lean_del_object(v___x_3630_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
v_a_3681_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3641_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3641_);
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
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_del_object(v___x_3636_);
lean_dec(v_fst_3633_);
lean_del_object(v___x_3630_);
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3689_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3638_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3638_);
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
}
}
else
{
lean_dec(v_a_3627_);
v___y_3481_ = v___y_3579_;
v___y_3482_ = v___y_3580_;
v___y_3483_ = v___y_3581_;
v___y_3484_ = v___y_3582_;
goto v___jp_3480_;
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3699_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3626_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3626_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec_ref(v___x_3226_);
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3707_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3583_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3583_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
}
else
{
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3186_ = v___x_3197_;
goto v___jp_3185_;
}
v___jp_3198_:
{
uint8_t v_emptyType_3205_; 
v_emptyType_3205_ = lean_ctor_get_uint8(v_config_3160_, sizeof(void*)*1 + 1);
if (v_emptyType_3205_ == 0)
{
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3186_ = v___x_3197_;
goto v___jp_3185_;
}
else
{
if (v___y_3200_ == 0)
{
if (v___y_3199_ == 0)
{
lean_object* v_searchFuel_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_searchFuel_3206_ = lean_ctor_get(v_config_3160_, 0);
v___x_3207_ = l_Lean_LocalDecl_fvarId(v_val_3192_);
lean_dec(v_val_3192_);
lean_inc(v_searchFuel_3206_);
lean_inc(v_mvarId_3161_);
v___x_3208_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3161_, v___x_3207_, v_searchFuel_3206_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; uint8_t v___x_3210_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3209_);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = lean_unbox(v_a_3209_);
lean_dec(v_a_3209_);
if (v___x_3210_ == 0)
{
lean_del_object(v___x_3194_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3186_ = v___x_3197_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v___x_3211_ = lean_box(v___x_3171_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3211_);
v___x_3213_ = v___x_3194_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v___x_3196_);
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
v_a_3178_ = v___x_3215_;
goto v___jp_3177_;
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_del_object(v___x_3194_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
lean_dec(v_mvarId_3161_);
lean_dec_ref(v_config_3160_);
v_a_3217_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3208_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3208_);
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
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3186_ = v___x_3197_;
goto v___jp_3185_;
}
}
else
{
lean_del_object(v___x_3194_);
lean_dec(v_val_3192_);
lean_del_object(v___x_3175_);
lean_dec(v_snd_3173_);
v_a_3186_ = v___x_3197_;
goto v___jp_3185_;
}
}
}
}
}
v___jp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3179_, 0, v_a_3178_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3179_);
v___x_3181_ = v___x_3175_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_snd_3173_);
v___x_3181_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
return v___x_3182_;
}
}
v___jp_3185_:
{
lean_object* v___x_3187_; size_t v___x_3188_; size_t v___x_3189_; 
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3184_);
lean_ctor_set(v___x_3187_, 1, v_a_3186_);
v___x_3188_ = ((size_t)1ULL);
v___x_3189_ = lean_usize_add(v_i_3164_, v___x_3188_);
v_i_3164_ = v___x_3189_;
v_b_3165_ = v___x_3187_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3788_, lean_object* v_mvarId_3789_, lean_object* v_as_3790_, lean_object* v_sz_3791_, lean_object* v_i_3792_, lean_object* v_b_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
size_t v_sz_boxed_3799_; size_t v_i_boxed_3800_; lean_object* v_res_3801_; 
v_sz_boxed_3799_ = lean_unbox_usize(v_sz_3791_);
lean_dec(v_sz_3791_);
v_i_boxed_3800_ = lean_unbox_usize(v_i_3792_);
lean_dec(v_i_3792_);
v_res_3801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3788_, v_mvarId_3789_, v_as_3790_, v_sz_boxed_3799_, v_i_boxed_3800_, v_b_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v_as_3790_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3802_, lean_object* v_mvarId_3803_, lean_object* v_as_3804_, size_t v_sz_3805_, size_t v_i_3806_, lean_object* v_b_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
uint8_t v___x_3813_; 
v___x_3813_ = lean_usize_dec_lt(v_i_3806_, v_sz_3805_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; 
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v___x_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3814_, 0, v_b_3807_);
return v___x_3814_;
}
else
{
lean_object* v_snd_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_4428_; 
v_snd_3815_ = lean_ctor_get(v_b_3807_, 1);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_b_3807_);
if (v_isSharedCheck_4428_ == 0)
{
lean_object* v_unused_4429_; 
v_unused_4429_ = lean_ctor_get(v_b_3807_, 0);
lean_dec(v_unused_4429_);
v___x_3817_ = v_b_3807_;
v_isShared_3818_ = v_isSharedCheck_4428_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_snd_3815_);
lean_dec(v_b_3807_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_4428_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v_a_3820_; lean_object* v___x_3826_; lean_object* v_a_3828_; lean_object* v_a_3833_; 
v___x_3826_ = lean_box(0);
v_a_3833_ = lean_array_uget(v_as_3804_, v_i_3806_);
if (lean_obj_tag(v_a_3833_) == 0)
{
lean_del_object(v___x_3817_);
v_a_3828_ = v_snd_3815_;
goto v___jp_3827_;
}
else
{
lean_object* v_val_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_4427_; 
v_val_3834_ = lean_ctor_get(v_a_3833_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_a_3833_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_3836_ = v_a_3833_;
v_isShared_3837_ = v_isSharedCheck_4427_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_val_3834_);
lean_dec(v_a_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_4427_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___y_3841_; uint8_t v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; uint8_t v___x_3867_; 
v___x_3838_ = lean_box(0);
v___x_3839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3867_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3834_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; uint8_t v___y_3870_; uint8_t v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; uint8_t v___y_3897_; lean_object* v___y_3898_; uint8_t v___y_3899_; lean_object* v_a_3900_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; uint8_t v___y_3910_; lean_object* v___y_3911_; uint8_t v___y_3912_; lean_object* v___y_3913_; uint8_t v___y_3957_; uint8_t v_isHEq_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; uint8_t v_isEq_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___x_4357_; 
v___x_3868_ = l_Lean_LocalDecl_type(v_val_3834_);
lean_inc_ref(v___x_3868_);
v___x_4357_ = l_Lean_Meta_matchNot_x3f(v___x_3868_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
if (lean_obj_tag(v_a_4358_) == 1)
{
lean_object* v_val_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4418_; 
v_val_4359_ = lean_ctor_get(v_a_4358_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_a_4358_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4361_ = v_a_4358_;
v_isShared_4362_ = v_isSharedCheck_4418_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_val_4359_);
lean_dec(v_a_4358_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4418_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4363_; 
v___x_4363_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4359_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4363_, 1);
if (lean_obj_tag(v_a_4364_) == 1)
{
lean_object* v_val_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4409_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec_ref(v_config_3802_);
v_val_4365_ = lean_ctor_get(v_a_4364_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v_a_4364_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4367_ = v_a_4364_;
v_isShared_4368_ = v_isSharedCheck_4409_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_val_4365_);
lean_dec(v_a_4364_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4409_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4369_; 
lean_inc(v_mvarId_3803_);
v___x_4369_ = l_Lean_MVarId_getType(v_mvarId_3803_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___x_4369_, 1);
v___x_4371_ = l_Lean_LocalDecl_toExpr(v_val_3834_);
v___x_4372_ = l_Lean_mkFVar(v_val_4365_);
v___x_4373_ = l_Lean_Expr_app___override(v___x_4371_, v___x_4372_);
v___x_4374_ = l_Lean_Meta_mkFalseElim(v_a_4370_, v___x_4373_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4376_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref_known(v___x_4374_, 1);
v___x_4376_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3803_, v_a_4375_, v___y_3809_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_object* v___x_4377_; lean_object* v___x_4379_; 
lean_dec_ref_known(v___x_4376_, 1);
v___x_4377_ = lean_box(v___x_3813_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 0, v___x_4377_);
v___x_4379_ = v___x_4367_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4377_);
v___x_4379_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
lean_object* v___x_4380_; lean_object* v___x_4382_; 
v___x_4380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
lean_ctor_set(v___x_4380_, 1, v___x_3838_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set_tag(v___x_4361_, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4380_);
v___x_4382_ = v___x_4361_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4380_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
v_a_3820_ = v___x_4382_;
goto v___jp_3819_;
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_del_object(v___x_4367_);
lean_del_object(v___x_4361_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_4385_ = lean_ctor_get(v___x_4376_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4376_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4376_);
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
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_del_object(v___x_4367_);
lean_del_object(v___x_4361_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4393_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4374_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4374_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_del_object(v___x_4367_);
lean_dec(v_val_4365_);
lean_del_object(v___x_4361_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4401_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4369_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4369_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
}
else
{
lean_dec(v_a_4364_);
lean_del_object(v___x_4361_);
v___y_4221_ = v___y_3808_;
v___y_4222_ = v___y_3809_;
v___y_4223_ = v___y_3810_;
v___y_4224_ = v___y_3811_;
goto v___jp_4220_;
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_del_object(v___x_4361_);
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4410_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4363_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4363_);
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
}
else
{
lean_dec(v_a_4358_);
v___y_4221_ = v___y_3808_;
v___y_4222_ = v___y_3809_;
v___y_4223_ = v___y_3810_;
v___y_4224_ = v___y_3811_;
goto v___jp_4220_;
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4419_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4357_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4357_);
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
v___jp_3869_:
{
uint8_t v_genDiseq_3876_; 
v_genDiseq_3876_ = lean_ctor_get_uint8(v_config_3802_, sizeof(void*)*1 + 2);
if (v_genDiseq_3876_ == 0)
{
lean_dec_ref(v___x_3868_);
v___y_3841_ = v___y_3870_;
v___y_3842_ = v___y_3871_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
v___y_3846_ = v___y_3875_;
goto v___jp_3840_;
}
else
{
uint8_t v___x_3877_; 
v___x_3877_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3868_);
lean_dec_ref(v___x_3868_);
if (v___x_3877_ == 0)
{
v___y_3841_ = v___y_3870_;
v___y_3842_ = v___y_3871_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
v___y_3846_ = v___y_3875_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3878_; 
lean_inc(v_val_3834_);
lean_inc(v_mvarId_3803_);
v___x_3878_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3803_, v_val_3834_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; uint8_t v___x_3880_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v___x_3880_ = lean_unbox(v_a_3879_);
lean_dec(v_a_3879_);
if (v___x_3880_ == 0)
{
v___y_3841_ = v___y_3870_;
v___y_3842_ = v___y_3871_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
v___y_3846_ = v___y_3875_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v___x_3881_ = lean_box(v___x_3813_);
v___x_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
lean_ctor_set(v___x_3883_, 1, v___x_3838_);
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
v_a_3820_ = v___x_3884_;
goto v___jp_3819_;
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_3885_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3878_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3878_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
}
v___jp_3893_:
{
uint8_t v___x_3901_; 
v___x_3901_ = l_Lean_Exception_isInterrupt(v_a_3900_);
if (v___x_3901_ == 0)
{
uint8_t v___x_3902_; 
lean_inc_ref(v_a_3900_);
v___x_3902_ = l_Lean_Exception_isRuntime(v_a_3900_);
if (v___x_3902_ == 0)
{
lean_dec_ref(v_a_3900_);
v___y_3870_ = v___y_3897_;
v___y_3871_ = v___y_3899_;
v___y_3872_ = v___y_3895_;
v___y_3873_ = v___y_3898_;
v___y_3874_ = v___y_3896_;
v___y_3875_ = v___y_3894_;
goto v___jp_3869_;
}
else
{
lean_object* v___x_3903_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v___x_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_a_3900_);
return v___x_3903_;
}
}
else
{
lean_object* v___x_3904_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v___x_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3904_, 0, v_a_3900_);
return v___x_3904_;
}
}
v___jp_3905_:
{
if (lean_obj_tag(v___y_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v_a_3914_ = lean_ctor_get(v___y_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___y_3913_, 1);
v___x_3915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3916_ = l_Lean_Expr_isConstOf(v_a_3914_, v___x_3915_);
lean_dec(v_a_3914_);
if (v___x_3916_ == 0)
{
lean_dec_ref(v___y_3908_);
v___y_3870_ = v___y_3910_;
v___y_3871_ = v___y_3912_;
v___y_3872_ = v___y_3907_;
v___y_3873_ = v___y_3911_;
v___y_3874_ = v___y_3909_;
v___y_3875_ = v___y_3906_;
goto v___jp_3869_;
}
else
{
lean_object* v___x_3917_; 
lean_inc_ref(v___y_3908_);
v___x_3917_ = l_Lean_Meta_mkEqRefl(v___y_3908_, v___y_3907_, v___y_3911_, v___y_3909_, v___y_3906_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3919_; lean_object* v_dummy_3920_; lean_object* v_nargs_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
v___x_3919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3921_ = l_Lean_Expr_getAppNumArgs(v___y_3908_);
lean_inc(v_nargs_3921_);
v___x_3922_ = lean_mk_array(v_nargs_3921_, v_dummy_3920_);
v___x_3923_ = lean_unsigned_to_nat(1u);
v___x_3924_ = lean_nat_sub(v_nargs_3921_, v___x_3923_);
lean_dec(v_nargs_3921_);
v___x_3925_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3908_, v___x_3922_, v___x_3924_);
v___x_3926_ = lean_array_push(v___x_3925_, v_a_3918_);
v___x_3927_ = l_Lean_mkAppN(v___x_3919_, v___x_3926_);
lean_dec_ref(v___x_3926_);
lean_inc(v_mvarId_3803_);
v___x_3928_ = l_Lean_MVarId_getType(v_mvarId_3803_, v___y_3907_, v___y_3911_, v___y_3909_, v___y_3906_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3928_, 1);
lean_inc(v_val_3834_);
v___x_3930_ = l_Lean_LocalDecl_toExpr(v_val_3834_);
v___x_3931_ = l_Lean_Meta_mkAbsurd(v_a_3929_, v___x_3930_, v___x_3927_, v___y_3907_, v___y_3911_, v___y_3909_, v___y_3906_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3951_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3934_ = v___x_3931_;
v_isShared_3935_ = v_isSharedCheck_3951_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3931_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3951_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3936_; 
lean_inc(v_mvarId_3803_);
v___x_3936_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3803_, v_a_3932_, v___y_3911_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3948_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; 
v_unused_3949_ = lean_ctor_get(v___x_3936_, 0);
lean_dec(v_unused_3949_);
v___x_3938_ = v___x_3936_;
v_isShared_3939_ = v_isSharedCheck_3948_;
goto v_resetjp_3937_;
}
else
{
lean_dec(v___x_3936_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3948_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3940_ = lean_box(v___x_3813_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set_tag(v___x_3938_, 1);
lean_ctor_set(v___x_3938_, 0, v___x_3940_);
v___x_3942_ = v___x_3938_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
lean_ctor_set(v___x_3943_, 1, v___x_3838_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 0, v___x_3943_);
v___x_3945_ = v___x_3934_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
v_a_3820_ = v___x_3945_;
goto v___jp_3819_;
}
}
}
}
else
{
lean_object* v_a_3950_; 
lean_del_object(v___x_3934_);
v_a_3950_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3936_, 1);
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3907_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v___y_3899_ = v___y_3912_;
v_a_3900_ = v_a_3950_;
goto v___jp_3893_;
}
}
}
else
{
lean_object* v_a_3952_; 
v_a_3952_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3931_, 1);
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3907_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v___y_3899_ = v___y_3912_;
v_a_3900_ = v_a_3952_;
goto v___jp_3893_;
}
}
else
{
lean_object* v_a_3953_; 
lean_dec_ref(v___x_3927_);
v_a_3953_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3928_, 1);
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3907_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v___y_3899_ = v___y_3912_;
v_a_3900_ = v_a_3953_;
goto v___jp_3893_;
}
}
else
{
lean_object* v_a_3954_; 
lean_dec_ref(v___y_3908_);
v_a_3954_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3917_, 1);
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3907_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v___y_3899_ = v___y_3912_;
v_a_3900_ = v_a_3954_;
goto v___jp_3893_;
}
}
}
else
{
lean_object* v_a_3955_; 
lean_dec_ref(v___y_3908_);
v_a_3955_ = lean_ctor_get(v___y_3913_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___y_3913_, 1);
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3907_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v___y_3899_ = v___y_3912_;
v_a_3900_ = v_a_3955_;
goto v___jp_3893_;
}
}
v___jp_3956_:
{
uint8_t v_useDecide_3963_; 
v_useDecide_3963_ = lean_ctor_get_uint8(v_config_3802_, sizeof(void*)*1);
if (v_useDecide_3963_ == 0)
{
v___y_3870_ = v___y_3957_;
v___y_3871_ = v_isHEq_3958_;
v___y_3872_ = v___y_3959_;
v___y_3873_ = v___y_3960_;
v___y_3874_ = v___y_3961_;
v___y_3875_ = v___y_3962_;
goto v___jp_3869_;
}
else
{
uint8_t v___x_3964_; 
v___x_3964_ = l_Lean_Expr_hasFVar(v___x_3868_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; 
lean_inc_ref(v___x_3868_);
v___x_3965_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3868_, v___y_3960_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; uint8_t v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v___x_3967_ = l_Lean_Expr_hasMVar(v_a_3966_);
if (v___x_3967_ == 0)
{
uint8_t v___x_3968_; 
v___x_3968_ = l_Lean_Expr_hasFVar(v_a_3966_);
lean_dec(v_a_3966_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_inc_ref(v___x_3868_);
v___x_3969_ = l_Lean_Meta_mkDecide(v___x_3868_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3971_; uint8_t v_transparency_3972_; uint8_t v___x_3973_; uint8_t v___x_3974_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v___x_3969_, 1);
v___x_3971_ = l_Lean_Meta_Context_config(v___y_3959_);
v_transparency_3972_ = lean_ctor_get_uint8(v___x_3971_, 9);
lean_dec_ref(v___x_3971_);
v___x_3973_ = 1;
v___x_3974_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3972_, v___x_3973_);
if (v___x_3974_ == 0)
{
lean_object* v_keyedConfig_3975_; uint8_t v_trackZetaDelta_3976_; lean_object* v_zetaDeltaSet_3977_; lean_object* v_lctx_3978_; lean_object* v_localInstances_3979_; lean_object* v_defEqCtx_x3f_3980_; lean_object* v_synthPendingDepth_3981_; lean_object* v_customCanUnfoldPredicate_x3f_3982_; uint8_t v_univApprox_3983_; uint8_t v_inTypeClassResolution_3984_; uint8_t v_cacheInferType_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_keyedConfig_3975_ = lean_ctor_get(v___y_3959_, 0);
v_trackZetaDelta_3976_ = lean_ctor_get_uint8(v___y_3959_, sizeof(void*)*7);
v_zetaDeltaSet_3977_ = lean_ctor_get(v___y_3959_, 1);
v_lctx_3978_ = lean_ctor_get(v___y_3959_, 2);
v_localInstances_3979_ = lean_ctor_get(v___y_3959_, 3);
v_defEqCtx_x3f_3980_ = lean_ctor_get(v___y_3959_, 4);
v_synthPendingDepth_3981_ = lean_ctor_get(v___y_3959_, 5);
v_customCanUnfoldPredicate_x3f_3982_ = lean_ctor_get(v___y_3959_, 6);
v_univApprox_3983_ = lean_ctor_get_uint8(v___y_3959_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3984_ = lean_ctor_get_uint8(v___y_3959_, sizeof(void*)*7 + 2);
v_cacheInferType_3985_ = lean_ctor_get_uint8(v___y_3959_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3975_);
v___x_3986_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3973_, v_keyedConfig_3975_);
lean_inc(v_customCanUnfoldPredicate_x3f_3982_);
lean_inc(v_synthPendingDepth_3981_);
lean_inc(v_defEqCtx_x3f_3980_);
lean_inc_ref(v_localInstances_3979_);
lean_inc_ref(v_lctx_3978_);
lean_inc(v_zetaDeltaSet_3977_);
v___x_3987_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
lean_ctor_set(v___x_3987_, 1, v_zetaDeltaSet_3977_);
lean_ctor_set(v___x_3987_, 2, v_lctx_3978_);
lean_ctor_set(v___x_3987_, 3, v_localInstances_3979_);
lean_ctor_set(v___x_3987_, 4, v_defEqCtx_x3f_3980_);
lean_ctor_set(v___x_3987_, 5, v_synthPendingDepth_3981_);
lean_ctor_set(v___x_3987_, 6, v_customCanUnfoldPredicate_x3f_3982_);
lean_ctor_set_uint8(v___x_3987_, sizeof(void*)*7, v_trackZetaDelta_3976_);
lean_ctor_set_uint8(v___x_3987_, sizeof(void*)*7 + 1, v_univApprox_3983_);
lean_ctor_set_uint8(v___x_3987_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3984_);
lean_ctor_set_uint8(v___x_3987_, sizeof(void*)*7 + 3, v_cacheInferType_3985_);
lean_inc(v___y_3962_);
lean_inc_ref(v___y_3961_);
lean_inc(v___y_3960_);
lean_inc(v_a_3970_);
v___x_3988_ = lean_whnf(v_a_3970_, v___x_3987_, v___y_3960_, v___y_3961_, v___y_3962_);
v___y_3906_ = v___y_3962_;
v___y_3907_ = v___y_3959_;
v___y_3908_ = v_a_3970_;
v___y_3909_ = v___y_3961_;
v___y_3910_ = v___y_3957_;
v___y_3911_ = v___y_3960_;
v___y_3912_ = v_isHEq_3958_;
v___y_3913_ = v___x_3988_;
goto v___jp_3905_;
}
else
{
lean_object* v___x_3989_; 
lean_inc(v___y_3962_);
lean_inc_ref(v___y_3961_);
lean_inc(v___y_3960_);
lean_inc_ref(v___y_3959_);
lean_inc(v_a_3970_);
v___x_3989_ = lean_whnf(v_a_3970_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
v___y_3906_ = v___y_3962_;
v___y_3907_ = v___y_3959_;
v___y_3908_ = v_a_3970_;
v___y_3909_ = v___y_3961_;
v___y_3910_ = v___y_3957_;
v___y_3911_ = v___y_3960_;
v___y_3912_ = v_isHEq_3958_;
v___y_3913_ = v___x_3989_;
goto v___jp_3905_;
}
}
else
{
lean_object* v_a_3990_; 
v_a_3990_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3969_, 1);
v___y_3894_ = v___y_3962_;
v___y_3895_ = v___y_3959_;
v___y_3896_ = v___y_3961_;
v___y_3897_ = v___y_3957_;
v___y_3898_ = v___y_3960_;
v___y_3899_ = v_isHEq_3958_;
v_a_3900_ = v_a_3990_;
goto v___jp_3893_;
}
}
else
{
v___y_3870_ = v___y_3957_;
v___y_3871_ = v_isHEq_3958_;
v___y_3872_ = v___y_3959_;
v___y_3873_ = v___y_3960_;
v___y_3874_ = v___y_3961_;
v___y_3875_ = v___y_3962_;
goto v___jp_3869_;
}
}
else
{
lean_dec(v_a_3966_);
v___y_3870_ = v___y_3957_;
v___y_3871_ = v_isHEq_3958_;
v___y_3872_ = v___y_3959_;
v___y_3873_ = v___y_3960_;
v___y_3874_ = v___y_3961_;
v___y_3875_ = v___y_3962_;
goto v___jp_3869_;
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_3991_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3965_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3965_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
else
{
v___y_3870_ = v___y_3957_;
v___y_3871_ = v_isHEq_3958_;
v___y_3872_ = v___y_3959_;
v___y_3873_ = v___y_3960_;
v___y_3874_ = v___y_3961_;
v___y_3875_ = v___y_3962_;
goto v___jp_3869_;
}
}
}
v___jp_3999_:
{
lean_object* v___x_4005_; 
lean_inc_ref(v___x_3868_);
v___x_4005_ = l_Lean_Meta_matchHEq_x3f(v___x_3868_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
if (lean_obj_tag(v_a_4006_) == 1)
{
lean_object* v_val_4007_; lean_object* v_snd_4008_; lean_object* v_snd_4009_; lean_object* v_fst_4010_; lean_object* v_fst_4011_; lean_object* v_fst_4012_; lean_object* v_snd_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4113_; 
v_val_4007_ = lean_ctor_get(v_a_4006_, 0);
lean_inc(v_val_4007_);
lean_dec_ref_known(v_a_4006_, 1);
v_snd_4008_ = lean_ctor_get(v_val_4007_, 1);
lean_inc(v_snd_4008_);
v_snd_4009_ = lean_ctor_get(v_snd_4008_, 1);
lean_inc(v_snd_4009_);
v_fst_4010_ = lean_ctor_get(v_val_4007_, 0);
lean_inc(v_fst_4010_);
lean_dec(v_val_4007_);
v_fst_4011_ = lean_ctor_get(v_snd_4008_, 0);
lean_inc(v_fst_4011_);
lean_dec(v_snd_4008_);
v_fst_4012_ = lean_ctor_get(v_snd_4009_, 0);
v_snd_4013_ = lean_ctor_get(v_snd_4009_, 1);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_snd_4009_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4015_ = v_snd_4009_;
v_isShared_4016_ = v_isSharedCheck_4113_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_snd_4013_);
lean_inc(v_fst_4012_);
lean_dec(v_snd_4009_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4113_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4011_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_a_4018_; 
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
lean_inc(v_a_4018_);
lean_dec_ref_known(v___x_4017_, 1);
if (lean_obj_tag(v_a_4018_) == 1)
{
lean_object* v_val_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4104_; 
v_val_4019_ = lean_ctor_get(v_a_4018_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_a_4018_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4021_ = v_a_4018_;
v_isShared_4022_ = v_isSharedCheck_4104_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_val_4019_);
lean_dec(v_a_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4104_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4013_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
if (lean_obj_tag(v_a_4024_) == 1)
{
lean_object* v_toConstantVal_4025_; lean_object* v_val_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4095_; 
v_toConstantVal_4025_ = lean_ctor_get(v_val_4019_, 0);
lean_inc_ref(v_toConstantVal_4025_);
lean_dec(v_val_4019_);
v_val_4026_ = lean_ctor_get(v_a_4024_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v_a_4024_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4028_ = v_a_4024_;
v_isShared_4029_ = v_isSharedCheck_4095_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_val_4026_);
lean_dec(v_a_4024_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4095_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v_toConstantVal_4030_; lean_object* v_name_4031_; lean_object* v_name_4032_; uint8_t v___x_4033_; 
v_toConstantVal_4030_ = lean_ctor_get(v_val_4026_, 0);
lean_inc_ref(v_toConstantVal_4030_);
lean_dec(v_val_4026_);
v_name_4031_ = lean_ctor_get(v_toConstantVal_4025_, 0);
lean_inc(v_name_4031_);
lean_dec_ref(v_toConstantVal_4025_);
v_name_4032_ = lean_ctor_get(v_toConstantVal_4030_, 0);
lean_inc(v_name_4032_);
lean_dec_ref(v_toConstantVal_4030_);
v___x_4033_ = lean_name_eq(v_name_4031_, v_name_4032_);
lean_dec(v_name_4032_);
lean_dec(v_name_4031_);
if (v___x_4033_ == 0)
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Lean_Meta_isExprDefEq(v_fst_4010_, v_fst_4012_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; uint8_t v___x_4036_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
v___x_4036_ = lean_unbox(v_a_4035_);
lean_dec(v_a_4035_);
if (v___x_4036_ == 0)
{
lean_del_object(v___x_4028_);
lean_del_object(v___x_4021_);
lean_del_object(v___x_4015_);
v___y_3957_ = v_isEq_4000_;
v_isHEq_3958_ = v___x_3813_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
v___y_3962_ = v___y_4004_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_4037_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec_ref(v_config_3802_);
lean_inc(v_mvarId_3803_);
v___x_4037_ = l_Lean_MVarId_getType(v_mvarId_3803_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v___x_4039_ = l_Lean_LocalDecl_toExpr(v_val_3834_);
v___x_4040_ = l_Lean_Meta_mkEqOfHEq(v___x_4039_, v___x_3813_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
v___x_4042_ = l_Lean_Meta_mkNoConfusion(v_a_4038_, v_a_4041_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4044_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4042_, 1);
v___x_4044_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3803_, v_a_4043_, v___y_4002_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v___x_4045_; lean_object* v___x_4047_; 
lean_dec_ref_known(v___x_4044_, 1);
v___x_4045_ = lean_box(v___x_3813_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v___x_4045_);
v___x_4047_ = v___x_4028_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4045_);
v___x_4047_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_object* v___x_4049_; 
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 1, v___x_3838_);
lean_ctor_set(v___x_4015_, 0, v___x_4047_);
v___x_4049_ = v___x_4015_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v___x_3838_);
v___x_4049_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
lean_object* v___x_4051_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set_tag(v___x_4021_, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4049_);
v___x_4051_ = v___x_4021_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
v_a_3820_ = v___x_4051_;
goto v___jp_3819_;
}
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_del_object(v___x_4028_);
lean_del_object(v___x_4021_);
lean_del_object(v___x_4015_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_4055_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4044_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4044_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_del_object(v___x_4028_);
lean_del_object(v___x_4021_);
lean_del_object(v___x_4015_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4063_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4042_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4042_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v_a_4038_);
lean_del_object(v___x_4028_);
lean_del_object(v___x_4021_);
lean_del_object(v___x_4015_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4071_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4040_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4040_);
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
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_del_object(v___x_4028_);
lean_del_object(v___x_4021_);
lean_del_object(v___x_4015_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4079_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4037_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4037_);
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
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_del_object(v___x_4028_);
lean_del_object(v___x_4021_);
lean_del_object(v___x_4015_);
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4087_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4034_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4034_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
else
{
lean_del_object(v___x_4028_);
lean_del_object(v___x_4021_);
lean_del_object(v___x_4015_);
lean_dec(v_fst_4012_);
lean_dec(v_fst_4010_);
v___y_3957_ = v_isEq_4000_;
v_isHEq_3958_ = v___x_3813_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
v___y_3962_ = v___y_4004_;
goto v___jp_3956_;
}
}
}
else
{
lean_dec(v_a_4024_);
lean_del_object(v___x_4021_);
lean_dec(v_val_4019_);
lean_del_object(v___x_4015_);
lean_dec(v_fst_4012_);
lean_dec(v_fst_4010_);
v___y_3957_ = v_isEq_4000_;
v_isHEq_3958_ = v___x_3813_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
v___y_3962_ = v___y_4004_;
goto v___jp_3956_;
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_del_object(v___x_4021_);
lean_dec(v_val_4019_);
lean_del_object(v___x_4015_);
lean_dec(v_fst_4012_);
lean_dec(v_fst_4010_);
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4096_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4023_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4023_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
}
else
{
lean_dec(v_a_4018_);
lean_del_object(v___x_4015_);
lean_dec(v_snd_4013_);
lean_dec(v_fst_4012_);
lean_dec(v_fst_4010_);
v___y_3957_ = v_isEq_4000_;
v_isHEq_3958_ = v___x_3813_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
v___y_3962_ = v___y_4004_;
goto v___jp_3956_;
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_del_object(v___x_4015_);
lean_dec(v_snd_4013_);
lean_dec(v_fst_4012_);
lean_dec(v_fst_4010_);
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4105_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4017_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4017_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
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
}
else
{
lean_dec(v_a_4006_);
v___y_3957_ = v_isEq_4000_;
v_isHEq_3958_ = v___x_3867_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
v___y_3962_ = v___y_4004_;
goto v___jp_3956_;
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4114_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4005_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4005_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
v___jp_4122_:
{
lean_object* v___x_4127_; 
lean_inc_ref(v___x_3868_);
v___x_4127_ = l_Lean_Meta_matchEq_x3f(v___x_3868_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
if (lean_obj_tag(v_a_4128_) == 1)
{
lean_object* v_val_4129_; lean_object* v_snd_4130_; lean_object* v_fst_4131_; lean_object* v_snd_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4211_; 
v_val_4129_ = lean_ctor_get(v_a_4128_, 0);
lean_inc(v_val_4129_);
lean_dec_ref_known(v_a_4128_, 1);
v_snd_4130_ = lean_ctor_get(v_val_4129_, 1);
lean_inc(v_snd_4130_);
lean_dec(v_val_4129_);
v_fst_4131_ = lean_ctor_get(v_snd_4130_, 0);
v_snd_4132_ = lean_ctor_get(v_snd_4130_, 1);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_snd_4130_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4134_ = v_snd_4130_;
v_isShared_4135_ = v_isSharedCheck_4211_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_snd_4132_);
lean_inc(v_fst_4131_);
lean_dec(v_snd_4130_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4211_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4131_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v___x_4136_, 1);
if (lean_obj_tag(v_a_4137_) == 1)
{
lean_object* v_val_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4202_; 
v_val_4138_ = lean_ctor_get(v_a_4137_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v_a_4137_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4140_ = v_a_4137_;
v_isShared_4141_ = v_isSharedCheck_4202_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_val_4138_);
lean_dec(v_a_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4202_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4142_; 
v___x_4142_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4132_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
if (lean_obj_tag(v_a_4143_) == 1)
{
lean_object* v_toConstantVal_4144_; lean_object* v_val_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4193_; 
v_toConstantVal_4144_ = lean_ctor_get(v_val_4138_, 0);
lean_inc_ref(v_toConstantVal_4144_);
lean_dec(v_val_4138_);
v_val_4145_ = lean_ctor_get(v_a_4143_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v_a_4143_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4147_ = v_a_4143_;
v_isShared_4148_ = v_isSharedCheck_4193_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_val_4145_);
lean_dec(v_a_4143_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4193_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v_toConstantVal_4149_; lean_object* v_name_4150_; lean_object* v_name_4151_; uint8_t v___x_4152_; 
v_toConstantVal_4149_ = lean_ctor_get(v_val_4145_, 0);
lean_inc_ref(v_toConstantVal_4149_);
lean_dec(v_val_4145_);
v_name_4150_ = lean_ctor_get(v_toConstantVal_4144_, 0);
lean_inc(v_name_4150_);
lean_dec_ref(v_toConstantVal_4144_);
v_name_4151_ = lean_ctor_get(v_toConstantVal_4149_, 0);
lean_inc(v_name_4151_);
lean_dec_ref(v_toConstantVal_4149_);
v___x_4152_ = lean_name_eq(v_name_4150_, v_name_4151_);
lean_dec(v_name_4151_);
lean_dec(v_name_4150_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec_ref(v_config_3802_);
lean_inc(v_mvarId_3803_);
v___x_4153_ = l_Lean_MVarId_getType(v_mvarId_3803_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4153_, 1);
v___x_4155_ = l_Lean_LocalDecl_toExpr(v_val_3834_);
v___x_4156_ = l_Lean_Meta_mkNoConfusion(v_a_4154_, v___x_4155_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4158_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v___x_4158_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3803_, v_a_4157_, v___y_4124_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v___x_4159_; lean_object* v___x_4161_; 
lean_dec_ref_known(v___x_4158_, 1);
v___x_4159_ = lean_box(v___x_3813_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4159_);
v___x_4161_ = v___x_4147_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4163_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 1, v___x_3838_);
lean_ctor_set(v___x_4134_, 0, v___x_4161_);
v___x_4163_ = v___x_4134_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v___x_3838_);
v___x_4163_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4165_; 
if (v_isShared_4141_ == 0)
{
lean_ctor_set_tag(v___x_4140_, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4163_);
v___x_4165_ = v___x_4140_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
v_a_3820_ = v___x_4165_;
goto v___jp_3819_;
}
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_del_object(v___x_4147_);
lean_del_object(v___x_4140_);
lean_del_object(v___x_4134_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_4169_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4158_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4158_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_del_object(v___x_4147_);
lean_del_object(v___x_4140_);
lean_del_object(v___x_4134_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4177_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4156_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4156_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_del_object(v___x_4147_);
lean_del_object(v___x_4140_);
lean_del_object(v___x_4134_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4185_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4153_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4153_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_del_object(v___x_4147_);
lean_del_object(v___x_4140_);
lean_del_object(v___x_4134_);
v_isEq_4000_ = v___x_3813_;
v___y_4001_ = v___y_4123_;
v___y_4002_ = v___y_4124_;
v___y_4003_ = v___y_4125_;
v___y_4004_ = v___y_4126_;
goto v___jp_3999_;
}
}
}
else
{
lean_dec(v_a_4143_);
lean_del_object(v___x_4140_);
lean_dec(v_val_4138_);
lean_del_object(v___x_4134_);
v_isEq_4000_ = v___x_3813_;
v___y_4001_ = v___y_4123_;
v___y_4002_ = v___y_4124_;
v___y_4003_ = v___y_4125_;
v___y_4004_ = v___y_4126_;
goto v___jp_3999_;
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_del_object(v___x_4140_);
lean_dec(v_val_4138_);
lean_del_object(v___x_4134_);
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4194_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4142_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4142_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
else
{
lean_dec(v_a_4137_);
lean_del_object(v___x_4134_);
lean_dec(v_snd_4132_);
v_isEq_4000_ = v___x_3813_;
v___y_4001_ = v___y_4123_;
v___y_4002_ = v___y_4124_;
v___y_4003_ = v___y_4125_;
v___y_4004_ = v___y_4126_;
goto v___jp_3999_;
}
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_del_object(v___x_4134_);
lean_dec(v_snd_4132_);
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4203_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4136_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4136_);
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
}
else
{
lean_dec(v_a_4128_);
v_isEq_4000_ = v___x_3867_;
v___y_4001_ = v___y_4123_;
v___y_4002_ = v___y_4124_;
v___y_4003_ = v___y_4125_;
v___y_4004_ = v___y_4126_;
goto v___jp_3999_;
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4212_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4127_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4127_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
v___jp_4220_:
{
lean_object* v___x_4225_; 
lean_inc_ref(v___x_3868_);
v___x_4225_ = l_Lean_refutableHasNotBit_x3f(v___x_3868_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
if (lean_obj_tag(v_a_4226_) == 1)
{
lean_object* v_val_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4267_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec_ref(v_config_3802_);
v_val_4227_ = lean_ctor_get(v_a_4226_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v_a_4226_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4229_ = v_a_4226_;
v_isShared_4230_ = v_isSharedCheck_4267_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_val_4227_);
lean_dec(v_a_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4267_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4231_; 
lean_inc(v_mvarId_3803_);
v___x_4231_ = l_Lean_MVarId_getType(v_mvarId_3803_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v___x_4233_ = l_Lean_LocalDecl_toExpr(v_val_3834_);
v___x_4234_ = l_Lean_Meta_mkAbsurd(v_a_4232_, v_val_4227_, v___x_4233_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4236_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_a_4235_);
lean_dec_ref_known(v___x_4234_, 1);
v___x_4236_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3803_, v_a_4235_, v___y_4222_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v___x_4237_; lean_object* v___x_4239_; 
lean_dec_ref_known(v___x_4236_, 1);
v___x_4237_ = lean_box(v___x_3813_);
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v___x_4237_);
v___x_4239_ = v___x_4229_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
lean_ctor_set(v___x_4240_, 1, v___x_3838_);
v___x_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
v_a_3820_ = v___x_4241_;
goto v___jp_3819_;
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_del_object(v___x_4229_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_4243_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4236_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4236_);
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
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_del_object(v___x_4229_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4251_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4234_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4234_);
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
lean_del_object(v___x_4229_);
lean_dec(v_val_4227_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4259_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4231_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4231_);
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
}
else
{
lean_object* v___x_4268_; 
lean_dec(v_a_4226_);
lean_inc_ref(v___x_3868_);
v___x_4268_ = l_Lean_Meta_matchNe_x3f(v___x_3868_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4268_, 1);
if (lean_obj_tag(v_a_4269_) == 1)
{
lean_object* v_val_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4340_; 
v_val_4270_ = lean_ctor_get(v_a_4269_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_a_4269_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4272_ = v_a_4269_;
v_isShared_4273_ = v_isSharedCheck_4340_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_val_4270_);
lean_dec(v_a_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4340_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v_snd_4274_; lean_object* v_fst_4275_; lean_object* v_snd_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4339_; 
v_snd_4274_ = lean_ctor_get(v_val_4270_, 1);
lean_inc(v_snd_4274_);
lean_dec(v_val_4270_);
v_fst_4275_ = lean_ctor_get(v_snd_4274_, 0);
v_snd_4276_ = lean_ctor_get(v_snd_4274_, 1);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_snd_4274_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4278_ = v_snd_4274_;
v_isShared_4279_ = v_isSharedCheck_4339_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_snd_4276_);
lean_inc(v_fst_4275_);
lean_dec(v_snd_4274_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4339_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4280_; 
lean_inc(v_fst_4275_);
v___x_4280_ = l_Lean_Meta_isExprDefEq(v_fst_4275_, v_snd_4276_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; uint8_t v___x_4282_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v___x_4280_, 1);
v___x_4282_ = lean_unbox(v_a_4281_);
lean_dec(v_a_4281_);
if (v___x_4282_ == 0)
{
lean_del_object(v___x_4278_);
lean_dec(v_fst_4275_);
lean_del_object(v___x_4272_);
v___y_4123_ = v___y_4221_;
v___y_4124_ = v___y_4222_;
v___y_4125_ = v___y_4223_;
v___y_4126_ = v___y_4224_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4283_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec_ref(v_config_3802_);
lean_inc(v_mvarId_3803_);
v___x_4283_ = l_Lean_MVarId_getType(v_mvarId_3803_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; lean_object* v___x_4285_; 
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4284_);
lean_dec_ref_known(v___x_4283_, 1);
v___x_4285_ = l_Lean_Meta_mkEqRefl(v_fst_4275_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___x_4285_, 1);
v___x_4287_ = l_Lean_LocalDecl_toExpr(v_val_3834_);
v___x_4288_ = l_Lean_Meta_mkAbsurd(v_a_4284_, v_a_4286_, v___x_4287_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4290_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v___x_4288_, 1);
v___x_4290_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3803_, v_a_4289_, v___y_4222_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v___x_4291_; lean_object* v___x_4293_; 
lean_dec_ref_known(v___x_4290_, 1);
v___x_4291_ = lean_box(v___x_3813_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___x_4291_);
v___x_4293_ = v___x_4272_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4291_);
v___x_4293_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
lean_object* v___x_4295_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 1, v___x_3838_);
lean_ctor_set(v___x_4278_, 0, v___x_4293_);
v___x_4295_ = v___x_4278_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4293_);
lean_ctor_set(v_reuseFailAlloc_4297_, 1, v___x_3838_);
v___x_4295_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4296_; 
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
v_a_3820_ = v___x_4296_;
goto v___jp_3819_;
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_del_object(v___x_4278_);
lean_del_object(v___x_4272_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_4299_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4290_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4290_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
lean_del_object(v___x_4278_);
lean_del_object(v___x_4272_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4307_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4288_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4288_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v_a_4284_);
lean_del_object(v___x_4278_);
lean_del_object(v___x_4272_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4315_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4285_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4285_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_del_object(v___x_4278_);
lean_dec(v_fst_4275_);
lean_del_object(v___x_4272_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
v_a_4323_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4283_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4283_);
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
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_del_object(v___x_4278_);
lean_dec(v_fst_4275_);
lean_del_object(v___x_4272_);
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4331_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4280_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4280_);
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
}
}
else
{
lean_dec(v_a_4269_);
v___y_4123_ = v___y_4221_;
v___y_4124_ = v___y_4222_;
v___y_4125_ = v___y_4223_;
v___y_4126_ = v___y_4224_;
goto v___jp_4122_;
}
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4341_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4268_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4268_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_dec_ref(v___x_3868_);
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_4349_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4225_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4225_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
}
else
{
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_3828_ = v___x_3839_;
goto v___jp_3827_;
}
v___jp_3840_:
{
uint8_t v_emptyType_3847_; 
v_emptyType_3847_ = lean_ctor_get_uint8(v_config_3802_, sizeof(void*)*1 + 1);
if (v_emptyType_3847_ == 0)
{
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_3828_ = v___x_3839_;
goto v___jp_3827_;
}
else
{
if (v___y_3841_ == 0)
{
if (v___y_3842_ == 0)
{
lean_object* v_searchFuel_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v_searchFuel_3848_ = lean_ctor_get(v_config_3802_, 0);
v___x_3849_ = l_Lean_LocalDecl_fvarId(v_val_3834_);
lean_dec(v_val_3834_);
lean_inc(v_searchFuel_3848_);
lean_inc(v_mvarId_3803_);
v___x_3850_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3803_, v___x_3849_, v_searchFuel_3848_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; uint8_t v___x_3852_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v___x_3852_ = lean_unbox(v_a_3851_);
lean_dec(v_a_3851_);
if (v___x_3852_ == 0)
{
lean_del_object(v___x_3836_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_3828_ = v___x_3839_;
goto v___jp_3827_;
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3855_; 
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v___x_3853_ = lean_box(v___x_3813_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v___x_3853_);
v___x_3855_ = v___x_3836_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
lean_ctor_set(v___x_3856_, 1, v___x_3838_);
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
v_a_3820_ = v___x_3857_;
goto v___jp_3819_;
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_del_object(v___x_3836_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
lean_dec(v_mvarId_3803_);
lean_dec_ref(v_config_3802_);
v_a_3859_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3850_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3850_);
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
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_3828_ = v___x_3839_;
goto v___jp_3827_;
}
}
else
{
lean_del_object(v___x_3836_);
lean_dec(v_val_3834_);
lean_del_object(v___x_3817_);
lean_dec(v_snd_3815_);
v_a_3828_ = v___x_3839_;
goto v___jp_3827_;
}
}
}
}
}
v___jp_3819_:
{
lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3821_, 0, v_a_3820_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v___x_3821_);
v___x_3823_ = v___x_3817_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v_snd_3815_);
v___x_3823_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
return v___x_3824_;
}
}
v___jp_3827_:
{
lean_object* v___x_3829_; size_t v___x_3830_; size_t v___x_3831_; lean_object* v___x_3832_; 
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3826_);
lean_ctor_set(v___x_3829_, 1, v_a_3828_);
v___x_3830_ = ((size_t)1ULL);
v___x_3831_ = lean_usize_add(v_i_3806_, v___x_3830_);
v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3802_, v_mvarId_3803_, v_as_3804_, v_sz_3805_, v___x_3831_, v___x_3829_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
return v___x_3832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4430_, lean_object* v_mvarId_4431_, lean_object* v_as_4432_, lean_object* v_sz_4433_, lean_object* v_i_4434_, lean_object* v_b_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
size_t v_sz_boxed_4441_; size_t v_i_boxed_4442_; lean_object* v_res_4443_; 
v_sz_boxed_4441_ = lean_unbox_usize(v_sz_4433_);
lean_dec(v_sz_4433_);
v_i_boxed_4442_ = lean_unbox_usize(v_i_4434_);
lean_dec(v_i_4434_);
v_res_4443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4430_, v_mvarId_4431_, v_as_4432_, v_sz_boxed_4441_, v_i_boxed_4442_, v_b_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v_as_4432_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4444_, lean_object* v_config_4445_, lean_object* v_mvarId_4446_, lean_object* v_n_4447_, lean_object* v_b_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
if (lean_obj_tag(v_n_4447_) == 0)
{
lean_object* v_cs_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; size_t v_sz_4457_; size_t v___x_4458_; lean_object* v___x_4459_; 
v_cs_4454_ = lean_ctor_get(v_n_4447_, 0);
v___x_4455_ = lean_box(0);
v___x_4456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4455_);
lean_ctor_set(v___x_4456_, 1, v_b_4448_);
v_sz_4457_ = lean_array_size(v_cs_4454_);
v___x_4458_ = ((size_t)0ULL);
v___x_4459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4444_, v_config_4445_, v_mvarId_4446_, v_cs_4454_, v_sz_4457_, v___x_4458_, v___x_4456_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4474_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4462_ = v___x_4459_;
v_isShared_4463_ = v_isSharedCheck_4474_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4459_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4474_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v_fst_4464_; 
v_fst_4464_ = lean_ctor_get(v_a_4460_, 0);
if (lean_obj_tag(v_fst_4464_) == 0)
{
lean_object* v_snd_4465_; lean_object* v___x_4466_; lean_object* v___x_4468_; 
v_snd_4465_ = lean_ctor_get(v_a_4460_, 1);
lean_inc(v_snd_4465_);
lean_dec(v_a_4460_);
v___x_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4466_, 0, v_snd_4465_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4466_);
v___x_4468_ = v___x_4462_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
else
{
lean_object* v_val_4470_; lean_object* v___x_4472_; 
lean_inc_ref(v_fst_4464_);
lean_dec(v_a_4460_);
v_val_4470_ = lean_ctor_get(v_fst_4464_, 0);
lean_inc(v_val_4470_);
lean_dec_ref_known(v_fst_4464_, 1);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v_val_4470_);
v___x_4472_ = v___x_4462_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_val_4470_);
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
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
v_a_4475_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4459_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4459_);
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
else
{
lean_object* v_vs_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; size_t v_sz_4486_; size_t v___x_4487_; lean_object* v___x_4488_; 
v_vs_4483_ = lean_ctor_get(v_n_4447_, 0);
v___x_4484_ = lean_box(0);
v___x_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
lean_ctor_set(v___x_4485_, 1, v_b_4448_);
v_sz_4486_ = lean_array_size(v_vs_4483_);
v___x_4487_ = ((size_t)0ULL);
v___x_4488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4445_, v_mvarId_4446_, v_vs_4483_, v_sz_4486_, v___x_4487_, v___x_4485_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4503_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4491_ = v___x_4488_;
v_isShared_4492_ = v_isSharedCheck_4503_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4488_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4503_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v_fst_4493_; 
v_fst_4493_ = lean_ctor_get(v_a_4489_, 0);
if (lean_obj_tag(v_fst_4493_) == 0)
{
lean_object* v_snd_4494_; lean_object* v___x_4495_; lean_object* v___x_4497_; 
v_snd_4494_ = lean_ctor_get(v_a_4489_, 1);
lean_inc(v_snd_4494_);
lean_dec(v_a_4489_);
v___x_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4495_, 0, v_snd_4494_);
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 0, v___x_4495_);
v___x_4497_ = v___x_4491_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4495_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
else
{
lean_object* v_val_4499_; lean_object* v___x_4501_; 
lean_inc_ref(v_fst_4493_);
lean_dec(v_a_4489_);
v_val_4499_ = lean_ctor_get(v_fst_4493_, 0);
lean_inc(v_val_4499_);
lean_dec_ref_known(v_fst_4493_, 1);
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 0, v_val_4499_);
v___x_4501_ = v___x_4491_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_val_4499_);
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
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
v_a_4504_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4488_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4488_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4512_, lean_object* v_config_4513_, lean_object* v_mvarId_4514_, lean_object* v_as_4515_, size_t v_sz_4516_, size_t v_i_4517_, lean_object* v_b_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
uint8_t v___x_4524_; 
v___x_4524_ = lean_usize_dec_lt(v_i_4517_, v_sz_4516_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4525_; 
lean_dec(v_mvarId_4514_);
lean_dec_ref(v_config_4513_);
v___x_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4525_, 0, v_b_4518_);
return v___x_4525_;
}
else
{
lean_object* v_snd_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4560_; 
v_snd_4526_ = lean_ctor_get(v_b_4518_, 1);
v_isSharedCheck_4560_ = !lean_is_exclusive(v_b_4518_);
if (v_isSharedCheck_4560_ == 0)
{
lean_object* v_unused_4561_; 
v_unused_4561_ = lean_ctor_get(v_b_4518_, 0);
lean_dec(v_unused_4561_);
v___x_4528_ = v_b_4518_;
v_isShared_4529_ = v_isSharedCheck_4560_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_snd_4526_);
lean_dec(v_b_4518_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4560_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4530_; lean_object* v_a_4531_; lean_object* v___x_4532_; 
v___x_4530_ = lean_box(0);
v_a_4531_ = lean_array_uget_borrowed(v_as_4515_, v_i_4517_);
lean_inc(v_snd_4526_);
lean_inc(v_mvarId_4514_);
lean_inc_ref(v_config_4513_);
v___x_4532_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4512_, v_config_4513_, v_mvarId_4514_, v_a_4531_, v_snd_4526_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4551_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4535_ = v___x_4532_;
v_isShared_4536_ = v_isSharedCheck_4551_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4532_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4551_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
if (lean_obj_tag(v_a_4533_) == 0)
{
lean_object* v___x_4537_; lean_object* v___x_4539_; 
lean_dec(v_mvarId_4514_);
lean_dec_ref(v_config_4513_);
v___x_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4537_, 0, v_a_4533_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v___x_4537_);
v___x_4539_ = v___x_4528_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4537_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_snd_4526_);
v___x_4539_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
lean_object* v___x_4541_; 
if (v_isShared_4536_ == 0)
{
lean_ctor_set(v___x_4535_, 0, v___x_4539_);
v___x_4541_ = v___x_4535_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4539_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; 
lean_del_object(v___x_4535_);
lean_dec(v_snd_4526_);
v_a_4544_ = lean_ctor_get(v_a_4533_, 0);
lean_inc(v_a_4544_);
lean_dec_ref_known(v_a_4533_, 1);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 1, v_a_4544_);
lean_ctor_set(v___x_4528_, 0, v___x_4530_);
v___x_4546_ = v___x_4528_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4530_);
lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_a_4544_);
v___x_4546_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
size_t v___x_4547_; size_t v___x_4548_; 
v___x_4547_ = ((size_t)1ULL);
v___x_4548_ = lean_usize_add(v_i_4517_, v___x_4547_);
v_i_4517_ = v___x_4548_;
v_b_4518_ = v___x_4546_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_del_object(v___x_4528_);
lean_dec(v_snd_4526_);
lean_dec(v_mvarId_4514_);
lean_dec_ref(v_config_4513_);
v_a_4552_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4532_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4532_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4562_, lean_object* v_config_4563_, lean_object* v_mvarId_4564_, lean_object* v_as_4565_, lean_object* v_sz_4566_, lean_object* v_i_4567_, lean_object* v_b_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
size_t v_sz_boxed_4574_; size_t v_i_boxed_4575_; lean_object* v_res_4576_; 
v_sz_boxed_4574_ = lean_unbox_usize(v_sz_4566_);
lean_dec(v_sz_4566_);
v_i_boxed_4575_ = lean_unbox_usize(v_i_4567_);
lean_dec(v_i_4567_);
v_res_4576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4562_, v_config_4563_, v_mvarId_4564_, v_as_4565_, v_sz_boxed_4574_, v_i_boxed_4575_, v_b_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v_as_4565_);
lean_dec_ref(v_init_4562_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4577_, lean_object* v_config_4578_, lean_object* v_mvarId_4579_, lean_object* v_n_4580_, lean_object* v_b_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4577_, v_config_4578_, v_mvarId_4579_, v_n_4580_, v_b_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec_ref(v_n_4580_);
lean_dec_ref(v_init_4577_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4588_, lean_object* v_mvarId_4589_, lean_object* v_t_4590_, lean_object* v_init_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v_root_4597_; lean_object* v_tail_4598_; lean_object* v___x_4599_; 
v_root_4597_ = lean_ctor_get(v_t_4590_, 0);
v_tail_4598_ = lean_ctor_get(v_t_4590_, 1);
lean_inc(v_mvarId_4589_);
lean_inc_ref(v_config_4588_);
lean_inc_ref(v_init_4591_);
v___x_4599_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4591_, v_config_4588_, v_mvarId_4589_, v_root_4597_, v_init_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
lean_dec_ref(v_init_4591_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4636_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4602_ = v___x_4599_;
v_isShared_4603_ = v_isSharedCheck_4636_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4599_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4636_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
if (lean_obj_tag(v_a_4600_) == 0)
{
lean_object* v_a_4604_; lean_object* v___x_4606_; 
lean_dec(v_mvarId_4589_);
lean_dec_ref(v_config_4588_);
v_a_4604_ = lean_ctor_get(v_a_4600_, 0);
lean_inc(v_a_4604_);
lean_dec_ref_known(v_a_4600_, 1);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v_a_4604_);
v___x_4606_ = v___x_4602_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; size_t v_sz_4611_; size_t v___x_4612_; lean_object* v___x_4613_; 
lean_del_object(v___x_4602_);
v_a_4608_ = lean_ctor_get(v_a_4600_, 0);
lean_inc(v_a_4608_);
lean_dec_ref_known(v_a_4600_, 1);
v___x_4609_ = lean_box(0);
v___x_4610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4609_);
lean_ctor_set(v___x_4610_, 1, v_a_4608_);
v_sz_4611_ = lean_array_size(v_tail_4598_);
v___x_4612_ = ((size_t)0ULL);
v___x_4613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4588_, v_mvarId_4589_, v_tail_4598_, v_sz_4611_, v___x_4612_, v___x_4610_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4627_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4627_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4627_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v_fst_4618_; 
v_fst_4618_ = lean_ctor_get(v_a_4614_, 0);
if (lean_obj_tag(v_fst_4618_) == 0)
{
lean_object* v_snd_4619_; lean_object* v___x_4621_; 
v_snd_4619_ = lean_ctor_get(v_a_4614_, 1);
lean_inc(v_snd_4619_);
lean_dec(v_a_4614_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v_snd_4619_);
v___x_4621_ = v___x_4616_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_snd_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
else
{
lean_object* v_val_4623_; lean_object* v___x_4625_; 
lean_inc_ref(v_fst_4618_);
lean_dec(v_a_4614_);
v_val_4623_ = lean_ctor_get(v_fst_4618_, 0);
lean_inc(v_val_4623_);
lean_dec_ref_known(v_fst_4618_, 1);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v_val_4623_);
v___x_4625_ = v___x_4616_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_val_4623_);
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
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
v_a_4628_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4613_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4613_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_dec(v_mvarId_4589_);
lean_dec_ref(v_config_4588_);
v_a_4637_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4599_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4599_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4645_, lean_object* v_mvarId_4646_, lean_object* v_t_4647_, lean_object* v_init_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4645_, v_mvarId_4646_, v_t_4647_, v_init_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec_ref(v_t_4647_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4655_, lean_object* v___x_4656_, lean_object* v_config_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v___x_4663_; 
lean_inc(v_mvarId_4655_);
v___x_4663_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4655_, v___x_4656_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v___x_4664_; 
lean_dec_ref_known(v___x_4663_, 1);
lean_inc(v_mvarId_4655_);
v___x_4664_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4655_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4698_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4667_ = v___x_4664_;
v_isShared_4668_ = v_isSharedCheck_4698_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4664_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4698_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
uint8_t v___x_4669_; 
v___x_4669_ = lean_unbox(v_a_4665_);
if (v___x_4669_ == 0)
{
lean_object* v_lctx_4670_; lean_object* v_decls_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
lean_del_object(v___x_4667_);
v_lctx_4670_ = lean_ctor_get(v___y_4658_, 2);
v_decls_4671_ = lean_ctor_get(v_lctx_4670_, 1);
v___x_4672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4673_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4657_, v_mvarId_4655_, v_decls_4671_, v___x_4672_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4686_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4676_ = v___x_4673_;
v_isShared_4677_ = v_isSharedCheck_4686_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4673_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4686_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v_fst_4678_; 
v_fst_4678_ = lean_ctor_get(v_a_4674_, 0);
lean_inc(v_fst_4678_);
lean_dec(v_a_4674_);
if (lean_obj_tag(v_fst_4678_) == 0)
{
lean_object* v___x_4680_; 
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 0, v_a_4665_);
v___x_4680_ = v___x_4676_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4665_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
else
{
lean_object* v_val_4682_; lean_object* v___x_4684_; 
lean_dec(v_a_4665_);
v_val_4682_ = lean_ctor_get(v_fst_4678_, 0);
lean_inc(v_val_4682_);
lean_dec_ref_known(v_fst_4678_, 1);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 0, v_val_4682_);
v___x_4684_ = v___x_4676_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_val_4682_);
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
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec(v_a_4665_);
v_a_4687_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4673_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4673_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
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
lean_object* v___x_4696_; 
lean_dec_ref(v_config_4657_);
lean_dec(v_mvarId_4655_);
if (v_isShared_4668_ == 0)
{
v___x_4696_ = v___x_4667_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4665_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
}
else
{
lean_dec_ref(v_config_4657_);
lean_dec(v_mvarId_4655_);
return v___x_4664_;
}
}
else
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4706_; 
lean_dec_ref(v_config_4657_);
lean_dec(v_mvarId_4655_);
v_a_4699_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4701_ = v___x_4663_;
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4663_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4702_ == 0)
{
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4707_, lean_object* v___x_4708_, lean_object* v_config_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4707_, v___x_4708_, v_config_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4718_, lean_object* v_config_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
lean_object* v___x_4725_; lean_object* v___f_4726_; lean_object* v___x_4727_; 
v___x_4725_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4718_);
v___f_4726_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4726_, 0, v_mvarId_4718_);
lean_closure_set(v___f_4726_, 1, v___x_4725_);
lean_closure_set(v___f_4726_, 2, v_config_4719_);
v___x_4727_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4718_, v___f_4726_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4728_, lean_object* v_config_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l_Lean_MVarId_contradictionCore(v_mvarId_4728_, v_config_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_);
lean_dec(v_a_4733_);
lean_dec_ref(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4736_, lean_object* v_config_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v___x_4743_; 
lean_inc(v_mvarId_4736_);
v___x_4743_ = l_Lean_MVarId_contradictionCore(v_mvarId_4736_, v_config_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4756_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4746_ = v___x_4743_;
v_isShared_4747_ = v_isSharedCheck_4756_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4743_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4756_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
uint8_t v___x_4748_; 
v___x_4748_ = lean_unbox(v_a_4744_);
lean_dec(v_a_4744_);
if (v___x_4748_ == 0)
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
lean_del_object(v___x_4746_);
v___x_4749_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4750_ = lean_box(0);
v___x_4751_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4749_, v_mvarId_4736_, v___x_4750_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
return v___x_4751_;
}
else
{
lean_object* v___x_4752_; lean_object* v___x_4754_; 
lean_dec(v_mvarId_4736_);
v___x_4752_ = lean_box(0);
if (v_isShared_4747_ == 0)
{
lean_ctor_set(v___x_4746_, 0, v___x_4752_);
v___x_4754_ = v___x_4746_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4752_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
lean_dec(v_mvarId_4736_);
v_a_4757_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4743_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4743_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4765_, lean_object* v_config_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Lean_MVarId_contradiction(v_mvarId_4765_, v_config_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4835_; uint8_t v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4835_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4836_ = 0;
v___x_4837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4838_ = l_Lean_registerTraceClass(v___x_4835_, v___x_4836_, v___x_4837_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4840_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_LitValues(builtin);
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
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
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
res = initialize_Lean_Meta_LitValues(builtin);
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
