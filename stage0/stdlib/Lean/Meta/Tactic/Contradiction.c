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
size_t v_sz_boxed_673_; size_t v___x_16000__boxed_674_; uint8_t v___x_16002__boxed_675_; lean_object* v_res_676_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_663_);
lean_dec(v_sz_663_);
v___x_16000__boxed_674_ = lean_unbox_usize(v___x_664_);
lean_dec(v___x_664_);
v___x_16002__boxed_675_ = lean_unbox(v___x_666_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_660_, v_mvarId_661_, v_fields_662_, v_sz_boxed_673_, v___x_16000__boxed_674_, v___x_665_, v___x_16002__boxed_675_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
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
uint8_t v___x_16122__boxed_879_; uint8_t v___x_16125__boxed_880_; lean_object* v_res_881_; 
v___x_16122__boxed_879_ = lean_unbox(v___x_869_);
v___x_16125__boxed_880_ = lean_unbox(v___x_872_);
v_res_881_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_866_, v_fvarId_867_, v___x_868_, v___x_16122__boxed_879_, v___x_870_, v_val_871_, v___x_16125__boxed_880_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
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
lean_dec_ref(v_e_1273_);
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
v___x_1732_ = lean_unsigned_to_nat(121u);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(lean_object* v_x_1788_, lean_object* v_x_1789_){
_start:
{
if (lean_obj_tag(v_x_1788_) == 0)
{
if (lean_obj_tag(v_x_1789_) == 0)
{
uint8_t v___x_1790_; 
v___x_1790_ = 1;
return v___x_1790_;
}
else
{
uint8_t v___x_1791_; 
v___x_1791_ = 0;
return v___x_1791_;
}
}
else
{
if (lean_obj_tag(v_x_1789_) == 0)
{
uint8_t v___x_1792_; 
v___x_1792_ = 0;
return v___x_1792_;
}
else
{
lean_object* v_val_1793_; uint8_t v___x_1794_; 
v_val_1793_ = lean_ctor_get(v_x_1789_, 0);
v___x_1794_ = lean_unbox(v_val_1793_);
if (v___x_1794_ == 0)
{
lean_object* v_val_1795_; uint8_t v___x_1796_; 
v_val_1795_ = lean_ctor_get(v_x_1788_, 0);
v___x_1796_ = lean_unbox(v_val_1795_);
if (v___x_1796_ == 0)
{
uint8_t v___x_1797_; 
v___x_1797_ = 1;
return v___x_1797_;
}
else
{
uint8_t v___x_1798_; 
v___x_1798_ = lean_unbox(v_val_1793_);
return v___x_1798_;
}
}
else
{
lean_object* v_val_1799_; uint8_t v___x_1800_; 
v_val_1799_ = lean_ctor_get(v_x_1788_, 0);
v___x_1800_ = lean_unbox(v_val_1799_);
return v___x_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0___boxed(lean_object* v_x_1801_, lean_object* v_x_1802_){
_start:
{
uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(v_x_1801_, v_x_1802_);
lean_dec(v_x_1802_);
lean_dec(v_x_1801_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0(lean_object* v_lhs_1808_, lean_object* v_rhs_1809_, lean_object* v_mvarId_1810_, lean_object* v_h_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
lean_inc_ref(v_rhs_1809_);
lean_inc_ref(v_lhs_1808_);
v___x_1817_ = l_Lean_Meta_floatLitValuesEq_x3f(v_lhs_1808_, v_rhs_1809_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1880_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1880_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1880_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
uint8_t v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1822_ = 0;
v___x_1823_ = ((lean_object*)(l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___closed__0));
v___x_1824_ = l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(v_a_1818_, v___x_1823_);
lean_dec(v_a_1818_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
lean_dec_ref(v_h_1811_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_rhs_1809_);
lean_dec_ref(v_lhs_1808_);
v___x_1825_ = lean_box(v___x_1822_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1825_);
v___x_1827_ = v___x_1820_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
else
{
lean_object* v___x_1829_; 
lean_del_object(v___x_1820_);
v___x_1829_ = l_Lean_Meta_mkEq(v_lhs_1808_, v_rhs_1809_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1831_ = l_Lean_mkNot(v_a_1830_);
v___x_1832_ = l_Lean_Meta_mkDecideProof(v___x_1831_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1834_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
lean_inc(v_mvarId_1810_);
v___x_1834_ = l_Lean_MVarId_getType(v_mvarId_1810_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1836_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1836_ = l_Lean_Meta_mkAbsurd(v_a_1835_, v_h_1811_, v_a_1833_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1846_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1810_, v_a_1837_, v___y_1813_);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; 
v_unused_1847_ = lean_ctor_get(v___x_1838_, 0);
lean_dec(v_unused_1847_);
v___x_1840_ = v___x_1838_;
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
else
{
lean_dec(v___x_1838_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_box(v___x_1824_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_mvarId_1810_);
v_a_1848_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1836_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1836_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v_a_1833_);
lean_dec_ref(v_h_1811_);
lean_dec(v_mvarId_1810_);
v_a_1856_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1834_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1834_);
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
lean_dec_ref(v_h_1811_);
lean_dec(v_mvarId_1810_);
v_a_1864_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1832_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1832_);
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
lean_dec_ref(v_h_1811_);
lean_dec(v_mvarId_1810_);
v_a_1872_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1829_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1829_);
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
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v_h_1811_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_rhs_1809_);
lean_dec_ref(v_lhs_1808_);
v_a_1881_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1817_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1817_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___boxed(lean_object* v_lhs_1889_, lean_object* v_rhs_1890_, lean_object* v_mvarId_1891_, lean_object* v_h_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_MVarId_closeIfDistinctFloatLits___lam__0(v_lhs_1889_, v_rhs_1890_, v_mvarId_1891_, v_h_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits(lean_object* v_mvarId_1899_, lean_object* v_h_1900_, lean_object* v_lhs_1901_, lean_object* v_rhs_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___f_1908_; lean_object* v___x_1909_; 
lean_inc(v_mvarId_1899_);
v___f_1908_ = lean_alloc_closure((void*)(l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1908_, 0, v_lhs_1901_);
lean_closure_set(v___f_1908_, 1, v_rhs_1902_);
lean_closure_set(v___f_1908_, 2, v_mvarId_1899_);
lean_closure_set(v___f_1908_, 3, v_h_1900_);
v___x_1909_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1899_, v___f_1908_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___boxed(lean_object* v_mvarId_1910_, lean_object* v_h_1911_, lean_object* v_lhs_1912_, lean_object* v_rhs_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_MVarId_closeIfDistinctFloatLits(v_mvarId_1910_, v_h_1911_, v_lhs_1912_, v_rhs_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
return v_res_1919_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1933_ = l_Lean_mkConst(v___x_1932_, v___x_1931_);
return v___x_1933_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1934_; lean_object* v_dummy_1935_; 
v___x_1934_ = lean_box(0);
v_dummy_1935_ = l_Lean_Expr_sort___override(v___x_1934_);
return v_dummy_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1936_, lean_object* v_mvarId_1937_, lean_object* v_as_1938_, size_t v_sz_1939_, size_t v_i_1940_, lean_object* v_b_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_usize_dec_lt(v_i_1940_, v_sz_1939_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; 
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v_b_1941_);
return v___x_1948_;
}
else
{
lean_object* v_snd_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_2530_; 
v_snd_1949_ = lean_ctor_get(v_b_1941_, 1);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_b_1941_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_b_1941_, 0);
lean_dec(v_unused_2531_);
v___x_1951_ = v_b_1941_;
v_isShared_1952_ = v_isSharedCheck_2530_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snd_1949_);
lean_dec(v_b_1941_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_2530_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_a_1954_; lean_object* v___x_1960_; lean_object* v_a_1962_; lean_object* v_a_1967_; 
v___x_1960_ = lean_box(0);
v_a_1967_ = lean_array_uget(v_as_1938_, v_i_1940_);
if (lean_obj_tag(v_a_1967_) == 0)
{
lean_del_object(v___x_1951_);
v_a_1962_ = v_snd_1949_;
goto v___jp_1961_;
}
else
{
lean_object* v_val_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2529_; 
v_val_1968_ = lean_ctor_get(v_a_1967_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_a_1967_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_1970_ = v_a_1967_;
v_isShared_1971_ = v_isSharedCheck_2529_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_val_1968_);
lean_dec(v_a_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2529_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___y_1975_; uint8_t v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___x_2000_; 
v___x_1972_ = lean_box(0);
v___x_1973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2000_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1968_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; uint8_t v___y_2003_; uint8_t v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; uint8_t v___y_2026_; lean_object* v___y_2027_; uint8_t v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v_a_2032_; uint8_t v___y_2038_; lean_object* v___y_2039_; uint8_t v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; uint8_t v___y_2082_; uint8_t v_isHEq_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; uint8_t v_isEq_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___x_2466_; 
v___x_2001_ = l_Lean_LocalDecl_type(v_val_1968_);
lean_inc_ref(v___x_2001_);
v___x_2466_ = l_Lean_Meta_matchNot_x3f(v___x_2001_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
if (lean_obj_tag(v_a_2467_) == 1)
{
lean_object* v_val_2468_; lean_object* v___x_2469_; 
v_val_2468_ = lean_ctor_get(v_a_2467_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v_a_2467_, 1);
v___x_2469_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2468_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
if (lean_obj_tag(v_a_2470_) == 1)
{
lean_object* v_val_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec_ref(v_config_1936_);
v_val_2471_ = lean_ctor_get(v_a_2470_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_a_2470_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2473_ = v_a_2470_;
v_isShared_2474_ = v_isSharedCheck_2512_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_val_2471_);
lean_dec(v_a_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2512_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; 
lean_inc(v_mvarId_1937_);
v___x_2475_ = l_Lean_MVarId_getType(v_mvarId_1937_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v___x_2477_ = l_Lean_LocalDecl_toExpr(v_val_1968_);
v___x_2478_ = l_Lean_mkFVar(v_val_2471_);
v___x_2479_ = l_Lean_Expr_app___override(v___x_2477_, v___x_2478_);
v___x_2480_ = l_Lean_Meta_mkFalseElim(v_a_2476_, v___x_2479_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2482_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
v___x_2482_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1937_, v_a_2481_, v___y_1943_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
lean_dec_ref_known(v___x_2482_, 1);
v___x_2483_ = lean_box(v___x_1947_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2483_);
v___x_2485_ = v___x_2473_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_1972_);
v_a_1954_ = v___x_2486_;
goto v___jp_1953_;
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_del_object(v___x_2473_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_2488_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2482_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2482_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_del_object(v___x_2473_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2496_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2480_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2480_);
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
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_del_object(v___x_2473_);
lean_dec(v_val_2471_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2504_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2475_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2475_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
else
{
lean_dec(v_a_2470_);
v___y_2332_ = v___y_1942_;
v___y_2333_ = v___y_1943_;
v___y_2334_ = v___y_1944_;
v___y_2335_ = v___y_1945_;
goto v___jp_2331_;
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2513_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2469_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2469_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_dec(v_a_2467_);
v___y_2332_ = v___y_1942_;
v___y_2333_ = v___y_1943_;
v___y_2334_ = v___y_1944_;
v___y_2335_ = v___y_1945_;
goto v___jp_2331_;
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2521_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2466_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2466_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
v___jp_2002_:
{
uint8_t v_genDiseq_2009_; 
v_genDiseq_2009_ = lean_ctor_get_uint8(v_config_1936_, sizeof(void*)*1 + 2);
if (v_genDiseq_2009_ == 0)
{
lean_dec_ref(v___x_2001_);
v___y_1975_ = v___y_2003_;
v___y_1976_ = v___y_2004_;
v___y_1977_ = v___y_2005_;
v___y_1978_ = v___y_2006_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_2008_;
goto v___jp_1974_;
}
else
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2001_);
lean_dec_ref(v___x_2001_);
if (v___x_2010_ == 0)
{
v___y_1975_ = v___y_2003_;
v___y_1976_ = v___y_2004_;
v___y_1977_ = v___y_2005_;
v___y_1978_ = v___y_2006_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_2008_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2011_; 
lean_inc(v_val_1968_);
lean_inc(v_mvarId_1937_);
v___x_2011_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1937_, v_val_1968_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; uint8_t v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = lean_unbox(v_a_2012_);
lean_dec(v_a_2012_);
if (v___x_2013_ == 0)
{
v___y_1975_ = v___y_2003_;
v___y_1976_ = v___y_2004_;
v___y_1977_ = v___y_2005_;
v___y_1978_ = v___y_2006_;
v___y_1979_ = v___y_2007_;
v___y_1980_ = v___y_2008_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v___x_2014_ = lean_box(v___x_1947_);
v___x_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set(v___x_2016_, 1, v___x_1972_);
v_a_1954_ = v___x_2016_;
goto v___jp_1953_;
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2017_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2011_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2011_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
}
v___jp_2025_:
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Lean_Exception_isInterrupt(v_a_2032_);
if (v___x_2033_ == 0)
{
uint8_t v___x_2034_; 
lean_inc_ref(v_a_2032_);
v___x_2034_ = l_Lean_Exception_isRuntime(v_a_2032_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v_a_2032_);
v___y_2003_ = v___y_2026_;
v___y_2004_ = v___y_2028_;
v___y_2005_ = v___y_2030_;
v___y_2006_ = v___y_2029_;
v___y_2007_ = v___y_2031_;
v___y_2008_ = v___y_2027_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2035_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_a_2032_);
return v___x_2035_;
}
}
else
{
lean_object* v___x_2036_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_a_2032_);
return v___x_2036_;
}
}
v___jp_2037_:
{
if (lean_obj_tag(v___y_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_a_2046_ = lean_ctor_get(v___y_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___y_2045_, 1);
v___x_2047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2048_ = l_Lean_Expr_isConstOf(v_a_2046_, v___x_2047_);
lean_dec(v_a_2046_);
if (v___x_2048_ == 0)
{
lean_dec_ref(v___y_2041_);
v___y_2003_ = v___y_2038_;
v___y_2004_ = v___y_2040_;
v___y_2005_ = v___y_2043_;
v___y_2006_ = v___y_2042_;
v___y_2007_ = v___y_2044_;
v___y_2008_ = v___y_2039_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2049_; 
lean_inc_ref(v___y_2041_);
v___x_2049_ = l_Lean_Meta_mkEqRefl(v___y_2041_, v___y_2043_, v___y_2042_, v___y_2044_, v___y_2039_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; lean_object* v_dummy_2052_; lean_object* v_nargs_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v___x_2051_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2053_ = l_Lean_Expr_getAppNumArgs(v___y_2041_);
lean_inc(v_nargs_2053_);
v___x_2054_ = lean_mk_array(v_nargs_2053_, v_dummy_2052_);
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_sub(v_nargs_2053_, v___x_2055_);
lean_dec(v_nargs_2053_);
v___x_2057_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2041_, v___x_2054_, v___x_2056_);
v___x_2058_ = lean_array_push(v___x_2057_, v_a_2050_);
v___x_2059_ = l_Lean_mkAppN(v___x_2051_, v___x_2058_);
lean_dec_ref(v___x_2058_);
lean_inc(v_mvarId_1937_);
v___x_2060_ = l_Lean_MVarId_getType(v_mvarId_1937_, v___y_2043_, v___y_2042_, v___y_2044_, v___y_2039_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
lean_inc(v_val_1968_);
v___x_2062_ = l_Lean_LocalDecl_toExpr(v_val_1968_);
v___x_2063_ = l_Lean_Meta_mkAbsurd(v_a_2061_, v___x_2062_, v___x_2059_, v___y_2043_, v___y_2042_, v___y_2044_, v___y_2039_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
lean_inc(v_mvarId_1937_);
v___x_2065_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1937_, v_a_2064_, v___y_2042_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2075_);
v___x_2067_ = v___x_2065_;
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v___x_2065_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = lean_box(v___x_1947_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set_tag(v___x_2067_, 1);
lean_ctor_set(v___x_2067_, 0, v___x_2069_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___x_1972_);
v_a_1954_ = v___x_2072_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2065_, 1);
v___y_2026_ = v___y_2038_;
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2040_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v_a_2032_ = v_a_2076_;
goto v___jp_2025_;
}
}
else
{
lean_object* v_a_2077_; 
v_a_2077_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2063_, 1);
v___y_2026_ = v___y_2038_;
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2040_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v_a_2032_ = v_a_2077_;
goto v___jp_2025_;
}
}
else
{
lean_object* v_a_2078_; 
lean_dec_ref(v___x_2059_);
v_a_2078_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2060_, 1);
v___y_2026_ = v___y_2038_;
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2040_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v_a_2032_ = v_a_2078_;
goto v___jp_2025_;
}
}
else
{
lean_object* v_a_2079_; 
lean_dec_ref(v___y_2041_);
v_a_2079_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2049_, 1);
v___y_2026_ = v___y_2038_;
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2040_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v_a_2032_ = v_a_2079_;
goto v___jp_2025_;
}
}
}
else
{
lean_object* v_a_2080_; 
lean_dec_ref(v___y_2041_);
v_a_2080_ = lean_ctor_get(v___y_2045_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___y_2045_, 1);
v___y_2026_ = v___y_2038_;
v___y_2027_ = v___y_2039_;
v___y_2028_ = v___y_2040_;
v___y_2029_ = v___y_2042_;
v___y_2030_ = v___y_2043_;
v___y_2031_ = v___y_2044_;
v_a_2032_ = v_a_2080_;
goto v___jp_2025_;
}
}
v___jp_2081_:
{
uint8_t v_useDecide_2088_; 
v_useDecide_2088_ = lean_ctor_get_uint8(v_config_1936_, sizeof(void*)*1);
if (v_useDecide_2088_ == 0)
{
v___y_2003_ = v___y_2082_;
v___y_2004_ = v_isHEq_2083_;
v___y_2005_ = v___y_2084_;
v___y_2006_ = v___y_2085_;
v___y_2007_ = v___y_2086_;
v___y_2008_ = v___y_2087_;
goto v___jp_2002_;
}
else
{
uint8_t v___x_2089_; 
v___x_2089_ = l_Lean_Expr_hasFVar(v___x_2001_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_inc_ref(v___x_2001_);
v___x_2090_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2001_, v___y_2085_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; uint8_t v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = l_Lean_Expr_hasMVar(v_a_2091_);
if (v___x_2092_ == 0)
{
uint8_t v___x_2093_; 
v___x_2093_ = l_Lean_Expr_hasFVar(v_a_2091_);
lean_dec(v_a_2091_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_inc_ref(v___x_2001_);
v___x_2094_ = l_Lean_Meta_mkDecide(v___x_2001_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; uint8_t v_transparency_2097_; uint8_t v___x_2098_; uint8_t v___x_2099_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = l_Lean_Meta_Context_config(v___y_2084_);
v_transparency_2097_ = lean_ctor_get_uint8(v___x_2096_, 9);
lean_dec_ref(v___x_2096_);
v___x_2098_ = 1;
v___x_2099_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v_keyedConfig_2100_; uint8_t v_trackZetaDelta_2101_; lean_object* v_zetaDeltaSet_2102_; lean_object* v_lctx_2103_; lean_object* v_localInstances_2104_; lean_object* v_defEqCtx_x3f_2105_; lean_object* v_synthPendingDepth_2106_; lean_object* v_customCanUnfoldPredicate_x3f_2107_; uint8_t v_univApprox_2108_; uint8_t v_inTypeClassResolution_2109_; uint8_t v_cacheInferType_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_keyedConfig_2100_ = lean_ctor_get(v___y_2084_, 0);
v_trackZetaDelta_2101_ = lean_ctor_get_uint8(v___y_2084_, sizeof(void*)*7);
v_zetaDeltaSet_2102_ = lean_ctor_get(v___y_2084_, 1);
v_lctx_2103_ = lean_ctor_get(v___y_2084_, 2);
v_localInstances_2104_ = lean_ctor_get(v___y_2084_, 3);
v_defEqCtx_x3f_2105_ = lean_ctor_get(v___y_2084_, 4);
v_synthPendingDepth_2106_ = lean_ctor_get(v___y_2084_, 5);
v_customCanUnfoldPredicate_x3f_2107_ = lean_ctor_get(v___y_2084_, 6);
v_univApprox_2108_ = lean_ctor_get_uint8(v___y_2084_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2109_ = lean_ctor_get_uint8(v___y_2084_, sizeof(void*)*7 + 2);
v_cacheInferType_2110_ = lean_ctor_get_uint8(v___y_2084_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2100_);
v___x_2111_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2098_, v_keyedConfig_2100_);
lean_inc(v_customCanUnfoldPredicate_x3f_2107_);
lean_inc(v_synthPendingDepth_2106_);
lean_inc(v_defEqCtx_x3f_2105_);
lean_inc_ref(v_localInstances_2104_);
lean_inc_ref(v_lctx_2103_);
lean_inc(v_zetaDeltaSet_2102_);
v___x_2112_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v_zetaDeltaSet_2102_);
lean_ctor_set(v___x_2112_, 2, v_lctx_2103_);
lean_ctor_set(v___x_2112_, 3, v_localInstances_2104_);
lean_ctor_set(v___x_2112_, 4, v_defEqCtx_x3f_2105_);
lean_ctor_set(v___x_2112_, 5, v_synthPendingDepth_2106_);
lean_ctor_set(v___x_2112_, 6, v_customCanUnfoldPredicate_x3f_2107_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*7, v_trackZetaDelta_2101_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*7 + 1, v_univApprox_2108_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2109_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*7 + 3, v_cacheInferType_2110_);
lean_inc(v___y_2087_);
lean_inc_ref(v___y_2086_);
lean_inc(v___y_2085_);
lean_inc(v_a_2095_);
v___x_2113_ = lean_whnf(v_a_2095_, v___x_2112_, v___y_2085_, v___y_2086_, v___y_2087_);
v___y_2038_ = v___y_2082_;
v___y_2039_ = v___y_2087_;
v___y_2040_ = v_isHEq_2083_;
v___y_2041_ = v_a_2095_;
v___y_2042_ = v___y_2085_;
v___y_2043_ = v___y_2084_;
v___y_2044_ = v___y_2086_;
v___y_2045_ = v___x_2113_;
goto v___jp_2037_;
}
else
{
lean_object* v___x_2114_; 
lean_inc(v___y_2087_);
lean_inc_ref(v___y_2086_);
lean_inc(v___y_2085_);
lean_inc_ref(v___y_2084_);
lean_inc(v_a_2095_);
v___x_2114_ = lean_whnf(v_a_2095_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
v___y_2038_ = v___y_2082_;
v___y_2039_ = v___y_2087_;
v___y_2040_ = v_isHEq_2083_;
v___y_2041_ = v_a_2095_;
v___y_2042_ = v___y_2085_;
v___y_2043_ = v___y_2084_;
v___y_2044_ = v___y_2086_;
v___y_2045_ = v___x_2114_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2115_; 
v_a_2115_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2094_, 1);
v___y_2026_ = v___y_2082_;
v___y_2027_ = v___y_2087_;
v___y_2028_ = v_isHEq_2083_;
v___y_2029_ = v___y_2085_;
v___y_2030_ = v___y_2084_;
v___y_2031_ = v___y_2086_;
v_a_2032_ = v_a_2115_;
goto v___jp_2025_;
}
}
else
{
v___y_2003_ = v___y_2082_;
v___y_2004_ = v_isHEq_2083_;
v___y_2005_ = v___y_2084_;
v___y_2006_ = v___y_2085_;
v___y_2007_ = v___y_2086_;
v___y_2008_ = v___y_2087_;
goto v___jp_2002_;
}
}
else
{
lean_dec(v_a_2091_);
v___y_2003_ = v___y_2082_;
v___y_2004_ = v_isHEq_2083_;
v___y_2005_ = v___y_2084_;
v___y_2006_ = v___y_2085_;
v___y_2007_ = v___y_2086_;
v___y_2008_ = v___y_2087_;
goto v___jp_2002_;
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2116_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2090_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2090_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
v___y_2003_ = v___y_2082_;
v___y_2004_ = v_isHEq_2083_;
v___y_2005_ = v___y_2084_;
v___y_2006_ = v___y_2085_;
v___y_2007_ = v___y_2086_;
v___y_2008_ = v___y_2087_;
goto v___jp_2002_;
}
}
}
v___jp_2124_:
{
lean_object* v___x_2130_; 
lean_inc_ref(v___x_2001_);
v___x_2130_ = l_Lean_Meta_matchHEq_x3f(v___x_2001_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
if (lean_obj_tag(v_a_2131_) == 1)
{
lean_object* v_val_2132_; lean_object* v_snd_2133_; lean_object* v_snd_2134_; lean_object* v_fst_2135_; lean_object* v_fst_2136_; lean_object* v_fst_2137_; lean_object* v_snd_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2231_; 
v_val_2132_ = lean_ctor_get(v_a_2131_, 0);
lean_inc(v_val_2132_);
lean_dec_ref_known(v_a_2131_, 1);
v_snd_2133_ = lean_ctor_get(v_val_2132_, 1);
lean_inc(v_snd_2133_);
v_snd_2134_ = lean_ctor_get(v_snd_2133_, 1);
lean_inc(v_snd_2134_);
v_fst_2135_ = lean_ctor_get(v_val_2132_, 0);
lean_inc(v_fst_2135_);
lean_dec(v_val_2132_);
v_fst_2136_ = lean_ctor_get(v_snd_2133_, 0);
lean_inc(v_fst_2136_);
lean_dec(v_snd_2133_);
v_fst_2137_ = lean_ctor_get(v_snd_2134_, 0);
v_snd_2138_ = lean_ctor_get(v_snd_2134_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_snd_2134_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2140_ = v_snd_2134_;
v_isShared_2141_ = v_isSharedCheck_2231_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_snd_2138_);
lean_inc(v_fst_2137_);
lean_dec(v_snd_2134_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2231_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2136_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
if (lean_obj_tag(v_a_2143_) == 1)
{
lean_object* v_val_2144_; lean_object* v___x_2145_; 
v_val_2144_ = lean_ctor_get(v_a_2143_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v_a_2143_, 1);
v___x_2145_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2138_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
if (lean_obj_tag(v_a_2146_) == 1)
{
lean_object* v_toConstantVal_2147_; lean_object* v_val_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2214_; 
v_toConstantVal_2147_ = lean_ctor_get(v_val_2144_, 0);
lean_inc_ref(v_toConstantVal_2147_);
lean_dec(v_val_2144_);
v_val_2148_ = lean_ctor_get(v_a_2146_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_a_2146_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2150_ = v_a_2146_;
v_isShared_2151_ = v_isSharedCheck_2214_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_val_2148_);
lean_dec(v_a_2146_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2214_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v_toConstantVal_2152_; lean_object* v_name_2153_; lean_object* v_name_2154_; uint8_t v___x_2155_; 
v_toConstantVal_2152_ = lean_ctor_get(v_val_2148_, 0);
lean_inc_ref(v_toConstantVal_2152_);
lean_dec(v_val_2148_);
v_name_2153_ = lean_ctor_get(v_toConstantVal_2147_, 0);
lean_inc(v_name_2153_);
lean_dec_ref(v_toConstantVal_2147_);
v_name_2154_ = lean_ctor_get(v_toConstantVal_2152_, 0);
lean_inc(v_name_2154_);
lean_dec_ref(v_toConstantVal_2152_);
v___x_2155_ = lean_name_eq(v_name_2153_, v_name_2154_);
lean_dec(v_name_2154_);
lean_dec(v_name_2153_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Meta_isExprDefEq(v_fst_2135_, v_fst_2137_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; uint8_t v___x_2158_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = lean_unbox(v_a_2157_);
lean_dec(v_a_2157_);
if (v___x_2158_ == 0)
{
lean_del_object(v___x_2150_);
lean_del_object(v___x_2140_);
v___y_2082_ = v_isEq_2125_;
v_isHEq_2083_ = v___x_1947_;
v___y_2084_ = v___y_2126_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2159_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec_ref(v_config_1936_);
lean_inc(v_mvarId_1937_);
v___x_2159_ = l_Lean_MVarId_getType(v_mvarId_1937_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = l_Lean_LocalDecl_toExpr(v_val_1968_);
v___x_2162_ = l_Lean_Meta_mkEqOfHEq(v___x_2161_, v___x_1947_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = l_Lean_Meta_mkNoConfusion(v_a_2160_, v_a_2163_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2166_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1937_, v_a_2165_, v___y_2127_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec_ref_known(v___x_2166_, 1);
v___x_2167_ = lean_box(v___x_1947_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2167_);
v___x_2169_ = v___x_2150_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2171_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 1, v___x_1972_);
lean_ctor_set(v___x_2140_, 0, v___x_2169_);
v___x_2171_ = v___x_2140_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v___x_1972_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
v_a_1954_ = v___x_2171_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_del_object(v___x_2150_);
lean_del_object(v___x_2140_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_2174_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2166_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2166_);
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
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_del_object(v___x_2150_);
lean_del_object(v___x_2140_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2182_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2164_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2164_);
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
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_a_2160_);
lean_del_object(v___x_2150_);
lean_del_object(v___x_2140_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2190_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2162_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2162_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_del_object(v___x_2150_);
lean_del_object(v___x_2140_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2198_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2159_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2159_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2150_);
lean_del_object(v___x_2140_);
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2206_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2156_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2156_);
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
lean_del_object(v___x_2150_);
lean_del_object(v___x_2140_);
lean_dec(v_fst_2137_);
lean_dec(v_fst_2135_);
v___y_2082_ = v_isEq_2125_;
v_isHEq_2083_ = v___x_1947_;
v___y_2084_ = v___y_2126_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
goto v___jp_2081_;
}
}
}
else
{
lean_dec(v_a_2146_);
lean_dec(v_val_2144_);
lean_del_object(v___x_2140_);
lean_dec(v_fst_2137_);
lean_dec(v_fst_2135_);
v___y_2082_ = v_isEq_2125_;
v_isHEq_2083_ = v___x_1947_;
v___y_2084_ = v___y_2126_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
goto v___jp_2081_;
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_val_2144_);
lean_del_object(v___x_2140_);
lean_dec(v_fst_2137_);
lean_dec(v_fst_2135_);
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2215_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2145_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2145_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_dec(v_a_2143_);
lean_del_object(v___x_2140_);
lean_dec(v_snd_2138_);
lean_dec(v_fst_2137_);
lean_dec(v_fst_2135_);
v___y_2082_ = v_isEq_2125_;
v_isHEq_2083_ = v___x_1947_;
v___y_2084_ = v___y_2126_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
goto v___jp_2081_;
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_del_object(v___x_2140_);
lean_dec(v_snd_2138_);
lean_dec(v_fst_2137_);
lean_dec(v_fst_2135_);
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2223_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2142_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2142_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
else
{
lean_dec(v_a_2131_);
v___y_2082_ = v_isEq_2125_;
v_isHEq_2083_ = v___x_2000_;
v___y_2084_ = v___y_2126_;
v___y_2085_ = v___y_2127_;
v___y_2086_ = v___y_2128_;
v___y_2087_ = v___y_2129_;
goto v___jp_2081_;
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2232_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2130_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2130_);
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
v___jp_2240_:
{
lean_object* v___x_2245_; 
lean_inc_ref(v___x_2001_);
v___x_2245_ = l_Lean_Meta_matchEq_x3f(v___x_2001_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___x_2245_, 1);
if (lean_obj_tag(v_a_2246_) == 1)
{
lean_object* v_val_2247_; lean_object* v_snd_2248_; lean_object* v_fst_2249_; lean_object* v_snd_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2322_; 
v_val_2247_ = lean_ctor_get(v_a_2246_, 0);
lean_inc(v_val_2247_);
lean_dec_ref_known(v_a_2246_, 1);
v_snd_2248_ = lean_ctor_get(v_val_2247_, 1);
lean_inc(v_snd_2248_);
lean_dec(v_val_2247_);
v_fst_2249_ = lean_ctor_get(v_snd_2248_, 0);
v_snd_2250_ = lean_ctor_get(v_snd_2248_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_snd_2248_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2252_ = v_snd_2248_;
v_isShared_2253_ = v_isSharedCheck_2322_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_snd_2250_);
lean_inc(v_fst_2249_);
lean_dec(v_snd_2248_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2322_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2249_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
if (lean_obj_tag(v_a_2255_) == 1)
{
lean_object* v_val_2256_; lean_object* v___x_2257_; 
v_val_2256_ = lean_ctor_get(v_a_2255_, 0);
lean_inc(v_val_2256_);
lean_dec_ref_known(v_a_2255_, 1);
v___x_2257_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2250_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
if (lean_obj_tag(v_a_2258_) == 1)
{
lean_object* v_toConstantVal_2259_; lean_object* v_val_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2305_; 
v_toConstantVal_2259_ = lean_ctor_get(v_val_2256_, 0);
lean_inc_ref(v_toConstantVal_2259_);
lean_dec(v_val_2256_);
v_val_2260_ = lean_ctor_get(v_a_2258_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_a_2258_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2262_ = v_a_2258_;
v_isShared_2263_ = v_isSharedCheck_2305_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_val_2260_);
lean_dec(v_a_2258_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2305_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v_toConstantVal_2264_; lean_object* v_name_2265_; lean_object* v_name_2266_; uint8_t v___x_2267_; 
v_toConstantVal_2264_ = lean_ctor_get(v_val_2260_, 0);
lean_inc_ref(v_toConstantVal_2264_);
lean_dec(v_val_2260_);
v_name_2265_ = lean_ctor_get(v_toConstantVal_2259_, 0);
lean_inc(v_name_2265_);
lean_dec_ref(v_toConstantVal_2259_);
v_name_2266_ = lean_ctor_get(v_toConstantVal_2264_, 0);
lean_inc(v_name_2266_);
lean_dec_ref(v_toConstantVal_2264_);
v___x_2267_ = lean_name_eq(v_name_2265_, v_name_2266_);
lean_dec(v_name_2266_);
lean_dec(v_name_2265_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec_ref(v_config_1936_);
lean_inc(v_mvarId_1937_);
v___x_2268_ = l_Lean_MVarId_getType(v_mvarId_1937_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v___x_2270_ = l_Lean_LocalDecl_toExpr(v_val_1968_);
v___x_2271_ = l_Lean_Meta_mkNoConfusion(v_a_2269_, v___x_2270_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2273_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1937_, v_a_2272_, v___y_2242_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
lean_dec_ref_known(v___x_2273_, 1);
v___x_2274_ = lean_box(v___x_1947_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2274_);
v___x_2276_ = v___x_2262_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 1, v___x_1972_);
lean_ctor_set(v___x_2252_, 0, v___x_2276_);
v___x_2278_ = v___x_2252_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v___x_1972_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
v_a_1954_ = v___x_2278_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_del_object(v___x_2262_);
lean_del_object(v___x_2252_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_2281_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2273_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2273_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_del_object(v___x_2262_);
lean_del_object(v___x_2252_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2289_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2271_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2271_);
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
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_del_object(v___x_2262_);
lean_del_object(v___x_2252_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2297_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2268_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2268_);
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
lean_del_object(v___x_2262_);
lean_del_object(v___x_2252_);
v_isEq_2125_ = v___x_1947_;
v___y_2126_ = v___y_2241_;
v___y_2127_ = v___y_2242_;
v___y_2128_ = v___y_2243_;
v___y_2129_ = v___y_2244_;
goto v___jp_2124_;
}
}
}
else
{
lean_dec(v_a_2258_);
lean_dec(v_val_2256_);
lean_del_object(v___x_2252_);
v_isEq_2125_ = v___x_1947_;
v___y_2126_ = v___y_2241_;
v___y_2127_ = v___y_2242_;
v___y_2128_ = v___y_2243_;
v___y_2129_ = v___y_2244_;
goto v___jp_2124_;
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec(v_val_2256_);
lean_del_object(v___x_2252_);
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2306_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2257_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2257_);
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
lean_dec(v_a_2255_);
lean_del_object(v___x_2252_);
lean_dec(v_snd_2250_);
v_isEq_2125_ = v___x_1947_;
v___y_2126_ = v___y_2241_;
v___y_2127_ = v___y_2242_;
v___y_2128_ = v___y_2243_;
v___y_2129_ = v___y_2244_;
goto v___jp_2124_;
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_del_object(v___x_2252_);
lean_dec(v_snd_2250_);
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2314_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2254_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2254_);
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
lean_dec(v_a_2246_);
v_isEq_2125_ = v___x_2000_;
v___y_2126_ = v___y_2241_;
v___y_2127_ = v___y_2242_;
v___y_2128_ = v___y_2243_;
v___y_2129_ = v___y_2244_;
goto v___jp_2124_;
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2323_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2245_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2245_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
v___jp_2331_:
{
lean_object* v___x_2336_; 
lean_inc_ref(v___x_2001_);
v___x_2336_ = l_Lean_refutableHasNotBit_x3f(v___x_2001_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
if (lean_obj_tag(v_a_2337_) == 1)
{
lean_object* v_val_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2377_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec_ref(v_config_1936_);
v_val_2338_ = lean_ctor_get(v_a_2337_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_a_2337_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2340_ = v_a_2337_;
v_isShared_2341_ = v_isSharedCheck_2377_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_val_2338_);
lean_dec(v_a_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2377_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; 
lean_inc(v_mvarId_1937_);
v___x_2342_ = l_Lean_MVarId_getType(v_mvarId_1937_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = l_Lean_LocalDecl_toExpr(v_val_1968_);
v___x_2345_ = l_Lean_Meta_mkAbsurd(v_a_2343_, v_val_2338_, v___x_2344_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2347_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2347_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1937_, v_a_2346_, v___y_2333_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_dec_ref_known(v___x_2347_, 1);
v___x_2348_ = lean_box(v___x_1947_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2348_);
v___x_2350_ = v___x_2340_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_ctor_set(v___x_2351_, 1, v___x_1972_);
v_a_1954_ = v___x_2351_;
goto v___jp_1953_;
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_del_object(v___x_2340_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_2353_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2347_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2347_);
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
lean_del_object(v___x_2340_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2361_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2345_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2345_);
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
lean_del_object(v___x_2340_);
lean_dec(v_val_2338_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2369_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2342_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2342_);
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
}
else
{
lean_object* v___x_2378_; 
lean_dec(v_a_2337_);
lean_inc_ref(v___x_2001_);
v___x_2378_ = l_Lean_Meta_matchNe_x3f(v___x_2001_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
if (lean_obj_tag(v_a_2379_) == 1)
{
lean_object* v_val_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2449_; 
v_val_2380_ = lean_ctor_get(v_a_2379_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_a_2379_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2382_ = v_a_2379_;
v_isShared_2383_ = v_isSharedCheck_2449_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_val_2380_);
lean_dec(v_a_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2449_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_snd_2384_; lean_object* v_fst_2385_; lean_object* v_snd_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2448_; 
v_snd_2384_ = lean_ctor_get(v_val_2380_, 1);
lean_inc(v_snd_2384_);
lean_dec(v_val_2380_);
v_fst_2385_ = lean_ctor_get(v_snd_2384_, 0);
v_snd_2386_ = lean_ctor_get(v_snd_2384_, 1);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_snd_2384_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2388_ = v_snd_2384_;
v_isShared_2389_ = v_isSharedCheck_2448_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_snd_2386_);
lean_inc(v_fst_2385_);
lean_dec(v_snd_2384_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2448_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; 
lean_inc(v_fst_2385_);
v___x_2390_ = l_Lean_Meta_isExprDefEq(v_fst_2385_, v_snd_2386_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; uint8_t v___x_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = lean_unbox(v_a_2391_);
lean_dec(v_a_2391_);
if (v___x_2392_ == 0)
{
lean_del_object(v___x_2388_);
lean_dec(v_fst_2385_);
lean_del_object(v___x_2382_);
v___y_2241_ = v___y_2332_;
v___y_2242_ = v___y_2333_;
v___y_2243_ = v___y_2334_;
v___y_2244_ = v___y_2335_;
goto v___jp_2240_;
}
else
{
lean_object* v___x_2393_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec_ref(v_config_1936_);
lean_inc(v_mvarId_1937_);
v___x_2393_ = l_Lean_MVarId_getType(v_mvarId_1937_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = l_Lean_Meta_mkEqRefl(v_fst_2385_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2397_ = l_Lean_LocalDecl_toExpr(v_val_1968_);
v___x_2398_ = l_Lean_Meta_mkAbsurd(v_a_2394_, v_a_2396_, v___x_2397_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___x_2400_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1937_, v_a_2399_, v___y_2333_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
lean_dec_ref_known(v___x_2400_, 1);
v___x_2401_ = lean_box(v___x_1947_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2401_);
v___x_2403_ = v___x_2382_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2405_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 1, v___x_1972_);
lean_ctor_set(v___x_2388_, 0, v___x_2403_);
v___x_2405_ = v___x_2388_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_1972_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
v_a_1954_ = v___x_2405_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_del_object(v___x_2388_);
lean_del_object(v___x_2382_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_2408_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2400_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2400_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_del_object(v___x_2388_);
lean_del_object(v___x_2382_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2416_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2398_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2398_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_a_2394_);
lean_del_object(v___x_2388_);
lean_del_object(v___x_2382_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2424_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2395_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2395_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_del_object(v___x_2388_);
lean_dec(v_fst_2385_);
lean_del_object(v___x_2382_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
v_a_2432_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2393_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2393_);
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
lean_del_object(v___x_2388_);
lean_dec(v_fst_2385_);
lean_del_object(v___x_2382_);
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2440_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2390_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2390_);
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
}
else
{
lean_dec(v_a_2379_);
v___y_2241_ = v___y_2332_;
v___y_2242_ = v___y_2333_;
v___y_2243_ = v___y_2334_;
v___y_2244_ = v___y_2335_;
goto v___jp_2240_;
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2450_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2378_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2378_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_2458_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2336_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2336_);
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
}
else
{
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_1962_ = v___x_1973_;
goto v___jp_1961_;
}
v___jp_1974_:
{
uint8_t v_emptyType_1981_; 
v_emptyType_1981_ = lean_ctor_get_uint8(v_config_1936_, sizeof(void*)*1 + 1);
if (v_emptyType_1981_ == 0)
{
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_1962_ = v___x_1973_;
goto v___jp_1961_;
}
else
{
if (v___y_1975_ == 0)
{
if (v___y_1976_ == 0)
{
lean_object* v_searchFuel_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_searchFuel_1982_ = lean_ctor_get(v_config_1936_, 0);
v___x_1983_ = l_Lean_LocalDecl_fvarId(v_val_1968_);
lean_dec(v_val_1968_);
lean_inc(v_searchFuel_1982_);
lean_inc(v_mvarId_1937_);
v___x_1984_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1937_, v___x_1983_, v_searchFuel_1982_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
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
lean_del_object(v___x_1970_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_1962_ = v___x_1973_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v___x_1987_ = lean_box(v___x_1947_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1987_);
v___x_1989_ = v___x_1970_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v___x_1972_);
v_a_1954_ = v___x_1990_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_del_object(v___x_1970_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_config_1936_);
v_a_1992_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1984_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1984_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_1962_ = v___x_1973_;
goto v___jp_1961_;
}
}
else
{
lean_del_object(v___x_1970_);
lean_dec(v_val_1968_);
lean_del_object(v___x_1951_);
lean_dec(v_snd_1949_);
v_a_1962_ = v___x_1973_;
goto v___jp_1961_;
}
}
}
}
}
v___jp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1955_, 0, v_a_1954_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1955_);
v___x_1957_ = v___x_1951_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_snd_1949_);
v___x_1957_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
v___jp_1961_:
{
lean_object* v___x_1963_; size_t v___x_1964_; size_t v___x_1965_; 
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1960_);
lean_ctor_set(v___x_1963_, 1, v_a_1962_);
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_add(v_i_1940_, v___x_1964_);
v_i_1940_ = v___x_1965_;
v_b_1941_ = v___x_1963_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2532_, lean_object* v_mvarId_2533_, lean_object* v_as_2534_, lean_object* v_sz_2535_, lean_object* v_i_2536_, lean_object* v_b_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
size_t v_sz_boxed_2543_; size_t v_i_boxed_2544_; lean_object* v_res_2545_; 
v_sz_boxed_2543_ = lean_unbox_usize(v_sz_2535_);
lean_dec(v_sz_2535_);
v_i_boxed_2544_ = lean_unbox_usize(v_i_2536_);
lean_dec(v_i_2536_);
v_res_2545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2532_, v_mvarId_2533_, v_as_2534_, v_sz_boxed_2543_, v_i_boxed_2544_, v_b_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v_as_2534_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2546_, lean_object* v_mvarId_2547_, lean_object* v_as_2548_, size_t v_sz_2549_, size_t v_i_2550_, lean_object* v_b_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
uint8_t v___x_2557_; 
v___x_2557_ = lean_usize_dec_lt(v_i_2550_, v_sz_2549_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v_b_2551_);
return v___x_2558_;
}
else
{
lean_object* v_snd_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_3140_; 
v_snd_2559_ = lean_ctor_get(v_b_2551_, 1);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_b_2551_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v_b_2551_, 0);
lean_dec(v_unused_3141_);
v___x_2561_ = v_b_2551_;
v_isShared_2562_ = v_isSharedCheck_3140_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_snd_2559_);
lean_dec(v_b_2551_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_3140_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_a_2564_; lean_object* v___x_2570_; lean_object* v_a_2572_; lean_object* v_a_2577_; 
v___x_2570_ = lean_box(0);
v_a_2577_ = lean_array_uget(v_as_2548_, v_i_2550_);
if (lean_obj_tag(v_a_2577_) == 0)
{
lean_del_object(v___x_2561_);
v_a_2572_ = v_snd_2559_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_3139_; 
v_val_2578_ = lean_ctor_get(v_a_2577_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_a_2577_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_2580_ = v_a_2577_;
v_isShared_2581_ = v_isSharedCheck_3139_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_val_2578_);
lean_dec(v_a_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_3139_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___y_2585_; uint8_t v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; uint8_t v___x_2610_; 
v___x_2582_ = lean_box(0);
v___x_2583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2610_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2578_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; uint8_t v___y_2613_; uint8_t v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v___y_2640_; uint8_t v___y_2641_; lean_object* v_a_2642_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2653_; uint8_t v___y_2654_; lean_object* v___y_2655_; uint8_t v___y_2692_; uint8_t v_isHEq_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; uint8_t v_isEq_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___x_3076_; 
v___x_2611_ = l_Lean_LocalDecl_type(v_val_2578_);
lean_inc_ref(v___x_2611_);
v___x_3076_ = l_Lean_Meta_matchNot_x3f(v___x_2611_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
if (lean_obj_tag(v_a_3077_) == 1)
{
lean_object* v_val_3078_; lean_object* v___x_3079_; 
v_val_3078_ = lean_ctor_get(v_a_3077_, 0);
lean_inc(v_val_3078_);
lean_dec_ref_known(v_a_3077_, 1);
v___x_3079_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3078_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
if (lean_obj_tag(v_a_3080_) == 1)
{
lean_object* v_val_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3122_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec_ref(v_config_2546_);
v_val_3081_ = lean_ctor_get(v_a_3080_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_a_3080_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3083_ = v_a_3080_;
v_isShared_3084_ = v_isSharedCheck_3122_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_val_3081_);
lean_dec(v_a_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3122_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; 
lean_inc(v_mvarId_2547_);
v___x_3085_ = l_Lean_MVarId_getType(v_mvarId_2547_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
v___x_3087_ = l_Lean_LocalDecl_toExpr(v_val_2578_);
v___x_3088_ = l_Lean_mkFVar(v_val_3081_);
v___x_3089_ = l_Lean_Expr_app___override(v___x_3087_, v___x_3088_);
v___x_3090_ = l_Lean_Meta_mkFalseElim(v_a_3086_, v___x_3089_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3092_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3090_, 1);
v___x_3092_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2547_, v_a_3091_, v___y_2553_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
lean_dec_ref_known(v___x_3092_, 1);
v___x_3093_ = lean_box(v___x_2557_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3093_);
v___x_3095_ = v___x_3083_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v___x_2582_);
v_a_2564_ = v___x_3096_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_del_object(v___x_3083_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_3098_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3092_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3092_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_del_object(v___x_3083_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_3106_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3090_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3090_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_del_object(v___x_3083_);
lean_dec(v_val_3081_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_3114_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3085_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3085_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
}
else
{
lean_dec(v_a_3080_);
v___y_2942_ = v___y_2552_;
v___y_2943_ = v___y_2553_;
v___y_2944_ = v___y_2554_;
v___y_2945_ = v___y_2555_;
goto v___jp_2941_;
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_3123_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3079_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3079_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_dec(v_a_3077_);
v___y_2942_ = v___y_2552_;
v___y_2943_ = v___y_2553_;
v___y_2944_ = v___y_2554_;
v___y_2945_ = v___y_2555_;
goto v___jp_2941_;
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_3131_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3076_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3076_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
v___jp_2612_:
{
uint8_t v_genDiseq_2619_; 
v_genDiseq_2619_ = lean_ctor_get_uint8(v_config_2546_, sizeof(void*)*1 + 2);
if (v_genDiseq_2619_ == 0)
{
lean_dec_ref(v___x_2611_);
v___y_2585_ = v___y_2613_;
v___y_2586_ = v___y_2614_;
v___y_2587_ = v___y_2615_;
v___y_2588_ = v___y_2616_;
v___y_2589_ = v___y_2617_;
v___y_2590_ = v___y_2618_;
goto v___jp_2584_;
}
else
{
uint8_t v___x_2620_; 
v___x_2620_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2611_);
lean_dec_ref(v___x_2611_);
if (v___x_2620_ == 0)
{
v___y_2585_ = v___y_2613_;
v___y_2586_ = v___y_2614_;
v___y_2587_ = v___y_2615_;
v___y_2588_ = v___y_2616_;
v___y_2589_ = v___y_2617_;
v___y_2590_ = v___y_2618_;
goto v___jp_2584_;
}
else
{
lean_object* v___x_2621_; 
lean_inc(v_val_2578_);
lean_inc(v_mvarId_2547_);
v___x_2621_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2547_, v_val_2578_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; uint8_t v___x_2623_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = lean_unbox(v_a_2622_);
lean_dec(v_a_2622_);
if (v___x_2623_ == 0)
{
v___y_2585_ = v___y_2613_;
v___y_2586_ = v___y_2614_;
v___y_2587_ = v___y_2615_;
v___y_2588_ = v___y_2616_;
v___y_2589_ = v___y_2617_;
v___y_2590_ = v___y_2618_;
goto v___jp_2584_;
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v___x_2624_ = lean_box(v___x_2557_);
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v___x_2582_);
v_a_2564_ = v___x_2626_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2627_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2621_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2621_);
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
}
v___jp_2635_:
{
uint8_t v___x_2643_; 
v___x_2643_ = l_Lean_Exception_isInterrupt(v_a_2642_);
if (v___x_2643_ == 0)
{
uint8_t v___x_2644_; 
lean_inc_ref(v_a_2642_);
v___x_2644_ = l_Lean_Exception_isRuntime(v_a_2642_);
if (v___x_2644_ == 0)
{
lean_dec_ref(v_a_2642_);
v___y_2613_ = v___y_2640_;
v___y_2614_ = v___y_2641_;
v___y_2615_ = v___y_2637_;
v___y_2616_ = v___y_2638_;
v___y_2617_ = v___y_2639_;
v___y_2618_ = v___y_2636_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2645_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v___x_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2645_, 0, v_a_2642_);
return v___x_2645_;
}
}
else
{
lean_object* v___x_2646_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v___x_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_a_2642_);
return v___x_2646_;
}
}
v___jp_2647_:
{
if (lean_obj_tag(v___y_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_a_2656_ = lean_ctor_get(v___y_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___y_2655_, 1);
v___x_2657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2658_ = l_Lean_Expr_isConstOf(v_a_2656_, v___x_2657_);
lean_dec(v_a_2656_);
if (v___x_2658_ == 0)
{
lean_dec_ref(v___y_2651_);
v___y_2613_ = v___y_2653_;
v___y_2614_ = v___y_2654_;
v___y_2615_ = v___y_2649_;
v___y_2616_ = v___y_2650_;
v___y_2617_ = v___y_2652_;
v___y_2618_ = v___y_2648_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2659_; 
lean_inc_ref(v___y_2651_);
v___x_2659_ = l_Lean_Meta_mkEqRefl(v___y_2651_, v___y_2649_, v___y_2650_, v___y_2652_, v___y_2648_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; lean_object* v_dummy_2662_; lean_object* v_nargs_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2663_ = l_Lean_Expr_getAppNumArgs(v___y_2651_);
lean_inc(v_nargs_2663_);
v___x_2664_ = lean_mk_array(v_nargs_2663_, v_dummy_2662_);
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_sub(v_nargs_2663_, v___x_2665_);
lean_dec(v_nargs_2663_);
v___x_2667_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2651_, v___x_2664_, v___x_2666_);
v___x_2668_ = lean_array_push(v___x_2667_, v_a_2660_);
v___x_2669_ = l_Lean_mkAppN(v___x_2661_, v___x_2668_);
lean_dec_ref(v___x_2668_);
lean_inc(v_mvarId_2547_);
v___x_2670_ = l_Lean_MVarId_getType(v_mvarId_2547_, v___y_2649_, v___y_2650_, v___y_2652_, v___y_2648_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
lean_inc(v_val_2578_);
v___x_2672_ = l_Lean_LocalDecl_toExpr(v_val_2578_);
v___x_2673_ = l_Lean_Meta_mkAbsurd(v_a_2671_, v___x_2672_, v___x_2669_, v___y_2649_, v___y_2650_, v___y_2652_, v___y_2648_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
lean_inc(v_mvarId_2547_);
v___x_2675_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2547_, v_a_2674_, v___y_2650_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2684_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; 
v_unused_2685_ = lean_ctor_get(v___x_2675_, 0);
lean_dec(v_unused_2685_);
v___x_2677_ = v___x_2675_;
v_isShared_2678_ = v_isSharedCheck_2684_;
goto v_resetjp_2676_;
}
else
{
lean_dec(v___x_2675_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2684_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2679_ = lean_box(v___x_2557_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 1);
lean_ctor_set(v___x_2677_, 0, v___x_2679_);
v___x_2681_ = v___x_2677_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
lean_ctor_set(v___x_2682_, 1, v___x_2582_);
v_a_2564_ = v___x_2682_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_a_2686_; 
v_a_2686_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2675_, 1);
v___y_2636_ = v___y_2648_;
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2652_;
v___y_2640_ = v___y_2653_;
v___y_2641_ = v___y_2654_;
v_a_2642_ = v_a_2686_;
goto v___jp_2635_;
}
}
else
{
lean_object* v_a_2687_; 
v_a_2687_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2673_, 1);
v___y_2636_ = v___y_2648_;
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2652_;
v___y_2640_ = v___y_2653_;
v___y_2641_ = v___y_2654_;
v_a_2642_ = v_a_2687_;
goto v___jp_2635_;
}
}
else
{
lean_object* v_a_2688_; 
lean_dec_ref(v___x_2669_);
v_a_2688_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2670_, 1);
v___y_2636_ = v___y_2648_;
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2652_;
v___y_2640_ = v___y_2653_;
v___y_2641_ = v___y_2654_;
v_a_2642_ = v_a_2688_;
goto v___jp_2635_;
}
}
else
{
lean_object* v_a_2689_; 
lean_dec_ref(v___y_2651_);
v_a_2689_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2659_, 1);
v___y_2636_ = v___y_2648_;
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2652_;
v___y_2640_ = v___y_2653_;
v___y_2641_ = v___y_2654_;
v_a_2642_ = v_a_2689_;
goto v___jp_2635_;
}
}
}
else
{
lean_object* v_a_2690_; 
lean_dec_ref(v___y_2651_);
v_a_2690_ = lean_ctor_get(v___y_2655_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___y_2655_, 1);
v___y_2636_ = v___y_2648_;
v___y_2637_ = v___y_2649_;
v___y_2638_ = v___y_2650_;
v___y_2639_ = v___y_2652_;
v___y_2640_ = v___y_2653_;
v___y_2641_ = v___y_2654_;
v_a_2642_ = v_a_2690_;
goto v___jp_2635_;
}
}
v___jp_2691_:
{
uint8_t v_useDecide_2698_; 
v_useDecide_2698_ = lean_ctor_get_uint8(v_config_2546_, sizeof(void*)*1);
if (v_useDecide_2698_ == 0)
{
v___y_2613_ = v___y_2692_;
v___y_2614_ = v_isHEq_2693_;
v___y_2615_ = v___y_2694_;
v___y_2616_ = v___y_2695_;
v___y_2617_ = v___y_2696_;
v___y_2618_ = v___y_2697_;
goto v___jp_2612_;
}
else
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_Expr_hasFVar(v___x_2611_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
lean_inc_ref(v___x_2611_);
v___x_2700_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2611_, v___y_2695_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; uint8_t v___x_2702_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
v___x_2702_ = l_Lean_Expr_hasMVar(v_a_2701_);
if (v___x_2702_ == 0)
{
uint8_t v___x_2703_; 
v___x_2703_ = l_Lean_Expr_hasFVar(v_a_2701_);
lean_dec(v_a_2701_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; 
lean_inc_ref(v___x_2611_);
v___x_2704_ = l_Lean_Meta_mkDecide(v___x_2611_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2706_; uint8_t v_transparency_2707_; uint8_t v___x_2708_; uint8_t v___x_2709_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v___x_2706_ = l_Lean_Meta_Context_config(v___y_2694_);
v_transparency_2707_ = lean_ctor_get_uint8(v___x_2706_, 9);
lean_dec_ref(v___x_2706_);
v___x_2708_ = 1;
v___x_2709_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v_keyedConfig_2710_; uint8_t v_trackZetaDelta_2711_; lean_object* v_zetaDeltaSet_2712_; lean_object* v_lctx_2713_; lean_object* v_localInstances_2714_; lean_object* v_defEqCtx_x3f_2715_; lean_object* v_synthPendingDepth_2716_; lean_object* v_customCanUnfoldPredicate_x3f_2717_; uint8_t v_univApprox_2718_; uint8_t v_inTypeClassResolution_2719_; uint8_t v_cacheInferType_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v_keyedConfig_2710_ = lean_ctor_get(v___y_2694_, 0);
v_trackZetaDelta_2711_ = lean_ctor_get_uint8(v___y_2694_, sizeof(void*)*7);
v_zetaDeltaSet_2712_ = lean_ctor_get(v___y_2694_, 1);
v_lctx_2713_ = lean_ctor_get(v___y_2694_, 2);
v_localInstances_2714_ = lean_ctor_get(v___y_2694_, 3);
v_defEqCtx_x3f_2715_ = lean_ctor_get(v___y_2694_, 4);
v_synthPendingDepth_2716_ = lean_ctor_get(v___y_2694_, 5);
v_customCanUnfoldPredicate_x3f_2717_ = lean_ctor_get(v___y_2694_, 6);
v_univApprox_2718_ = lean_ctor_get_uint8(v___y_2694_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2719_ = lean_ctor_get_uint8(v___y_2694_, sizeof(void*)*7 + 2);
v_cacheInferType_2720_ = lean_ctor_get_uint8(v___y_2694_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2710_);
v___x_2721_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2708_, v_keyedConfig_2710_);
lean_inc(v_customCanUnfoldPredicate_x3f_2717_);
lean_inc(v_synthPendingDepth_2716_);
lean_inc(v_defEqCtx_x3f_2715_);
lean_inc_ref(v_localInstances_2714_);
lean_inc_ref(v_lctx_2713_);
lean_inc(v_zetaDeltaSet_2712_);
v___x_2722_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_zetaDeltaSet_2712_);
lean_ctor_set(v___x_2722_, 2, v_lctx_2713_);
lean_ctor_set(v___x_2722_, 3, v_localInstances_2714_);
lean_ctor_set(v___x_2722_, 4, v_defEqCtx_x3f_2715_);
lean_ctor_set(v___x_2722_, 5, v_synthPendingDepth_2716_);
lean_ctor_set(v___x_2722_, 6, v_customCanUnfoldPredicate_x3f_2717_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7, v_trackZetaDelta_2711_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 1, v_univApprox_2718_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2719_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 3, v_cacheInferType_2720_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc(v_a_2705_);
v___x_2723_ = lean_whnf(v_a_2705_, v___x_2722_, v___y_2695_, v___y_2696_, v___y_2697_);
v___y_2648_ = v___y_2697_;
v___y_2649_ = v___y_2694_;
v___y_2650_ = v___y_2695_;
v___y_2651_ = v_a_2705_;
v___y_2652_ = v___y_2696_;
v___y_2653_ = v___y_2692_;
v___y_2654_ = v_isHEq_2693_;
v___y_2655_ = v___x_2723_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2724_; 
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v_a_2705_);
v___x_2724_ = lean_whnf(v_a_2705_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
v___y_2648_ = v___y_2697_;
v___y_2649_ = v___y_2694_;
v___y_2650_ = v___y_2695_;
v___y_2651_ = v_a_2705_;
v___y_2652_ = v___y_2696_;
v___y_2653_ = v___y_2692_;
v___y_2654_ = v_isHEq_2693_;
v___y_2655_ = v___x_2724_;
goto v___jp_2647_;
}
}
else
{
lean_object* v_a_2725_; 
v_a_2725_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2704_, 1);
v___y_2636_ = v___y_2697_;
v___y_2637_ = v___y_2694_;
v___y_2638_ = v___y_2695_;
v___y_2639_ = v___y_2696_;
v___y_2640_ = v___y_2692_;
v___y_2641_ = v_isHEq_2693_;
v_a_2642_ = v_a_2725_;
goto v___jp_2635_;
}
}
else
{
v___y_2613_ = v___y_2692_;
v___y_2614_ = v_isHEq_2693_;
v___y_2615_ = v___y_2694_;
v___y_2616_ = v___y_2695_;
v___y_2617_ = v___y_2696_;
v___y_2618_ = v___y_2697_;
goto v___jp_2612_;
}
}
else
{
lean_dec(v_a_2701_);
v___y_2613_ = v___y_2692_;
v___y_2614_ = v_isHEq_2693_;
v___y_2615_ = v___y_2694_;
v___y_2616_ = v___y_2695_;
v___y_2617_ = v___y_2696_;
v___y_2618_ = v___y_2697_;
goto v___jp_2612_;
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2726_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2700_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2700_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
v___y_2613_ = v___y_2692_;
v___y_2614_ = v_isHEq_2693_;
v___y_2615_ = v___y_2694_;
v___y_2616_ = v___y_2695_;
v___y_2617_ = v___y_2696_;
v___y_2618_ = v___y_2697_;
goto v___jp_2612_;
}
}
}
v___jp_2734_:
{
lean_object* v___x_2740_; 
lean_inc_ref(v___x_2611_);
v___x_2740_ = l_Lean_Meta_matchHEq_x3f(v___x_2611_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
if (lean_obj_tag(v_a_2741_) == 1)
{
lean_object* v_val_2742_; lean_object* v_snd_2743_; lean_object* v_snd_2744_; lean_object* v_fst_2745_; lean_object* v_fst_2746_; lean_object* v_fst_2747_; lean_object* v_snd_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2841_; 
v_val_2742_ = lean_ctor_get(v_a_2741_, 0);
lean_inc(v_val_2742_);
lean_dec_ref_known(v_a_2741_, 1);
v_snd_2743_ = lean_ctor_get(v_val_2742_, 1);
lean_inc(v_snd_2743_);
v_snd_2744_ = lean_ctor_get(v_snd_2743_, 1);
lean_inc(v_snd_2744_);
v_fst_2745_ = lean_ctor_get(v_val_2742_, 0);
lean_inc(v_fst_2745_);
lean_dec(v_val_2742_);
v_fst_2746_ = lean_ctor_get(v_snd_2743_, 0);
lean_inc(v_fst_2746_);
lean_dec(v_snd_2743_);
v_fst_2747_ = lean_ctor_get(v_snd_2744_, 0);
v_snd_2748_ = lean_ctor_get(v_snd_2744_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_snd_2744_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2750_ = v_snd_2744_;
v_isShared_2751_ = v_isSharedCheck_2841_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_snd_2748_);
lean_inc(v_fst_2747_);
lean_dec(v_snd_2744_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2841_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2746_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
if (lean_obj_tag(v_a_2753_) == 1)
{
lean_object* v_val_2754_; lean_object* v___x_2755_; 
v_val_2754_ = lean_ctor_get(v_a_2753_, 0);
lean_inc(v_val_2754_);
lean_dec_ref_known(v_a_2753_, 1);
v___x_2755_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2748_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
if (lean_obj_tag(v_a_2756_) == 1)
{
lean_object* v_toConstantVal_2757_; lean_object* v_val_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2824_; 
v_toConstantVal_2757_ = lean_ctor_get(v_val_2754_, 0);
lean_inc_ref(v_toConstantVal_2757_);
lean_dec(v_val_2754_);
v_val_2758_ = lean_ctor_get(v_a_2756_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_a_2756_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2760_ = v_a_2756_;
v_isShared_2761_ = v_isSharedCheck_2824_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_val_2758_);
lean_dec(v_a_2756_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2824_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v_toConstantVal_2762_; lean_object* v_name_2763_; lean_object* v_name_2764_; uint8_t v___x_2765_; 
v_toConstantVal_2762_ = lean_ctor_get(v_val_2758_, 0);
lean_inc_ref(v_toConstantVal_2762_);
lean_dec(v_val_2758_);
v_name_2763_ = lean_ctor_get(v_toConstantVal_2757_, 0);
lean_inc(v_name_2763_);
lean_dec_ref(v_toConstantVal_2757_);
v_name_2764_ = lean_ctor_get(v_toConstantVal_2762_, 0);
lean_inc(v_name_2764_);
lean_dec_ref(v_toConstantVal_2762_);
v___x_2765_ = lean_name_eq(v_name_2763_, v_name_2764_);
lean_dec(v_name_2764_);
lean_dec(v_name_2763_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_Meta_isExprDefEq(v_fst_2745_, v_fst_2747_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; uint8_t v___x_2768_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v___x_2768_ = lean_unbox(v_a_2767_);
lean_dec(v_a_2767_);
if (v___x_2768_ == 0)
{
lean_del_object(v___x_2760_);
lean_del_object(v___x_2750_);
v___y_2692_ = v_isEq_2735_;
v_isHEq_2693_ = v___x_2557_;
v___y_2694_ = v___y_2736_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
goto v___jp_2691_;
}
else
{
lean_object* v___x_2769_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec_ref(v_config_2546_);
lean_inc(v_mvarId_2547_);
v___x_2769_ = l_Lean_MVarId_getType(v_mvarId_2547_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v___x_2771_ = l_Lean_LocalDecl_toExpr(v_val_2578_);
v___x_2772_ = l_Lean_Meta_mkEqOfHEq(v___x_2771_, v___x_2557_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2774_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v___x_2774_ = l_Lean_Meta_mkNoConfusion(v_a_2770_, v_a_2773_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2776_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2776_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2547_, v_a_2775_, v___y_2737_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
lean_dec_ref_known(v___x_2776_, 1);
v___x_2777_ = lean_box(v___x_2557_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2777_);
v___x_2779_ = v___x_2760_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2781_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 1, v___x_2582_);
lean_ctor_set(v___x_2750_, 0, v___x_2779_);
v___x_2781_ = v___x_2750_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2582_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
v_a_2564_ = v___x_2781_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_del_object(v___x_2760_);
lean_del_object(v___x_2750_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_2784_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2776_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2776_);
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
lean_del_object(v___x_2760_);
lean_del_object(v___x_2750_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_2792_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2774_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2774_);
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
lean_dec(v_a_2770_);
lean_del_object(v___x_2760_);
lean_del_object(v___x_2750_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_2800_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2772_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2772_);
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
lean_del_object(v___x_2760_);
lean_del_object(v___x_2750_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_2808_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2769_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2769_);
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
lean_del_object(v___x_2760_);
lean_del_object(v___x_2750_);
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2816_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2766_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2766_);
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
else
{
lean_del_object(v___x_2760_);
lean_del_object(v___x_2750_);
lean_dec(v_fst_2747_);
lean_dec(v_fst_2745_);
v___y_2692_ = v_isEq_2735_;
v_isHEq_2693_ = v___x_2557_;
v___y_2694_ = v___y_2736_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
goto v___jp_2691_;
}
}
}
else
{
lean_dec(v_a_2756_);
lean_dec(v_val_2754_);
lean_del_object(v___x_2750_);
lean_dec(v_fst_2747_);
lean_dec(v_fst_2745_);
v___y_2692_ = v_isEq_2735_;
v_isHEq_2693_ = v___x_2557_;
v___y_2694_ = v___y_2736_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
goto v___jp_2691_;
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_val_2754_);
lean_del_object(v___x_2750_);
lean_dec(v_fst_2747_);
lean_dec(v_fst_2745_);
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2825_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2755_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2755_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
else
{
lean_dec(v_a_2753_);
lean_del_object(v___x_2750_);
lean_dec(v_snd_2748_);
lean_dec(v_fst_2747_);
lean_dec(v_fst_2745_);
v___y_2692_ = v_isEq_2735_;
v_isHEq_2693_ = v___x_2557_;
v___y_2694_ = v___y_2736_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
goto v___jp_2691_;
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_del_object(v___x_2750_);
lean_dec(v_snd_2748_);
lean_dec(v_fst_2747_);
lean_dec(v_fst_2745_);
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2833_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2752_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2752_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
else
{
lean_dec(v_a_2741_);
v___y_2692_ = v_isEq_2735_;
v_isHEq_2693_ = v___x_2610_;
v___y_2694_ = v___y_2736_;
v___y_2695_ = v___y_2737_;
v___y_2696_ = v___y_2738_;
v___y_2697_ = v___y_2739_;
goto v___jp_2691_;
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2842_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2740_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2740_);
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
v___jp_2850_:
{
lean_object* v___x_2855_; 
lean_inc_ref(v___x_2611_);
v___x_2855_ = l_Lean_Meta_matchEq_x3f(v___x_2611_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
if (lean_obj_tag(v_a_2856_) == 1)
{
lean_object* v_val_2857_; lean_object* v_snd_2858_; lean_object* v_fst_2859_; lean_object* v_snd_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2932_; 
v_val_2857_ = lean_ctor_get(v_a_2856_, 0);
lean_inc(v_val_2857_);
lean_dec_ref_known(v_a_2856_, 1);
v_snd_2858_ = lean_ctor_get(v_val_2857_, 1);
lean_inc(v_snd_2858_);
lean_dec(v_val_2857_);
v_fst_2859_ = lean_ctor_get(v_snd_2858_, 0);
v_snd_2860_ = lean_ctor_get(v_snd_2858_, 1);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_snd_2858_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2862_ = v_snd_2858_;
v_isShared_2863_ = v_isSharedCheck_2932_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_snd_2860_);
lean_inc(v_fst_2859_);
lean_dec(v_snd_2858_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2932_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2859_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
if (lean_obj_tag(v_a_2865_) == 1)
{
lean_object* v_val_2866_; lean_object* v___x_2867_; 
v_val_2866_ = lean_ctor_get(v_a_2865_, 0);
lean_inc(v_val_2866_);
lean_dec_ref_known(v_a_2865_, 1);
v___x_2867_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2860_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
if (lean_obj_tag(v_a_2868_) == 1)
{
lean_object* v_toConstantVal_2869_; lean_object* v_val_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2915_; 
v_toConstantVal_2869_ = lean_ctor_get(v_val_2866_, 0);
lean_inc_ref(v_toConstantVal_2869_);
lean_dec(v_val_2866_);
v_val_2870_ = lean_ctor_get(v_a_2868_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2872_ = v_a_2868_;
v_isShared_2873_ = v_isSharedCheck_2915_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_val_2870_);
lean_dec(v_a_2868_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2915_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_toConstantVal_2874_; lean_object* v_name_2875_; lean_object* v_name_2876_; uint8_t v___x_2877_; 
v_toConstantVal_2874_ = lean_ctor_get(v_val_2870_, 0);
lean_inc_ref(v_toConstantVal_2874_);
lean_dec(v_val_2870_);
v_name_2875_ = lean_ctor_get(v_toConstantVal_2869_, 0);
lean_inc(v_name_2875_);
lean_dec_ref(v_toConstantVal_2869_);
v_name_2876_ = lean_ctor_get(v_toConstantVal_2874_, 0);
lean_inc(v_name_2876_);
lean_dec_ref(v_toConstantVal_2874_);
v___x_2877_ = lean_name_eq(v_name_2875_, v_name_2876_);
lean_dec(v_name_2876_);
lean_dec(v_name_2875_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec_ref(v_config_2546_);
lean_inc(v_mvarId_2547_);
v___x_2878_ = l_Lean_MVarId_getType(v_mvarId_2547_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___x_2880_ = l_Lean_LocalDecl_toExpr(v_val_2578_);
v___x_2881_ = l_Lean_Meta_mkNoConfusion(v_a_2879_, v___x_2880_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2883_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2547_, v_a_2882_, v___y_2852_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
lean_dec_ref_known(v___x_2883_, 1);
v___x_2884_ = lean_box(v___x_2557_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2884_);
v___x_2886_ = v___x_2872_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v___x_2582_);
lean_ctor_set(v___x_2862_, 0, v___x_2886_);
v___x_2888_ = v___x_2862_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v___x_2582_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
v_a_2564_ = v___x_2888_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_del_object(v___x_2872_);
lean_del_object(v___x_2862_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_2891_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2883_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2883_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_del_object(v___x_2872_);
lean_del_object(v___x_2862_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_2899_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2881_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2881_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_del_object(v___x_2872_);
lean_del_object(v___x_2862_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_2907_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2878_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2878_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_del_object(v___x_2872_);
lean_del_object(v___x_2862_);
v_isEq_2735_ = v___x_2557_;
v___y_2736_ = v___y_2851_;
v___y_2737_ = v___y_2852_;
v___y_2738_ = v___y_2853_;
v___y_2739_ = v___y_2854_;
goto v___jp_2734_;
}
}
}
else
{
lean_dec(v_a_2868_);
lean_dec(v_val_2866_);
lean_del_object(v___x_2862_);
v_isEq_2735_ = v___x_2557_;
v___y_2736_ = v___y_2851_;
v___y_2737_ = v___y_2852_;
v___y_2738_ = v___y_2853_;
v___y_2739_ = v___y_2854_;
goto v___jp_2734_;
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_val_2866_);
lean_del_object(v___x_2862_);
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2916_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2867_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2867_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_dec(v_a_2865_);
lean_del_object(v___x_2862_);
lean_dec(v_snd_2860_);
v_isEq_2735_ = v___x_2557_;
v___y_2736_ = v___y_2851_;
v___y_2737_ = v___y_2852_;
v___y_2738_ = v___y_2853_;
v___y_2739_ = v___y_2854_;
goto v___jp_2734_;
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_del_object(v___x_2862_);
lean_dec(v_snd_2860_);
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2924_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2864_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2864_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
else
{
lean_dec(v_a_2856_);
v_isEq_2735_ = v___x_2610_;
v___y_2736_ = v___y_2851_;
v___y_2737_ = v___y_2852_;
v___y_2738_ = v___y_2853_;
v___y_2739_ = v___y_2854_;
goto v___jp_2734_;
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2933_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2855_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2855_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
v___jp_2941_:
{
lean_object* v___x_2946_; 
lean_inc_ref(v___x_2611_);
v___x_2946_ = l_Lean_refutableHasNotBit_x3f(v___x_2611_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
if (lean_obj_tag(v_a_2947_) == 1)
{
lean_object* v_val_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec_ref(v_config_2546_);
v_val_2948_ = lean_ctor_get(v_a_2947_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_a_2947_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2950_ = v_a_2947_;
v_isShared_2951_ = v_isSharedCheck_2987_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_val_2948_);
lean_dec(v_a_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2987_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; 
lean_inc(v_mvarId_2547_);
v___x_2952_ = l_Lean_MVarId_getType(v_mvarId_2547_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2954_ = l_Lean_LocalDecl_toExpr(v_val_2578_);
v___x_2955_ = l_Lean_Meta_mkAbsurd(v_a_2953_, v_val_2948_, v___x_2954_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2547_, v_a_2956_, v___y_2943_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
lean_dec_ref_known(v___x_2957_, 1);
v___x_2958_ = lean_box(v___x_2557_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2958_);
v___x_2960_ = v___x_2950_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v___x_2582_);
v_a_2564_ = v___x_2961_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_del_object(v___x_2950_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_2963_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2957_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2957_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_del_object(v___x_2950_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_2971_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2955_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2955_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_del_object(v___x_2950_);
lean_dec(v_val_2948_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_2979_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2952_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2952_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
else
{
lean_object* v___x_2988_; 
lean_dec(v_a_2947_);
lean_inc_ref(v___x_2611_);
v___x_2988_ = l_Lean_Meta_matchNe_x3f(v___x_2611_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
if (lean_obj_tag(v_a_2989_) == 1)
{
lean_object* v_val_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3059_; 
v_val_2990_ = lean_ctor_get(v_a_2989_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_a_2989_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_2992_ = v_a_2989_;
v_isShared_2993_ = v_isSharedCheck_3059_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_val_2990_);
lean_dec(v_a_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3059_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_snd_2994_; lean_object* v_fst_2995_; lean_object* v_snd_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3058_; 
v_snd_2994_ = lean_ctor_get(v_val_2990_, 1);
lean_inc(v_snd_2994_);
lean_dec(v_val_2990_);
v_fst_2995_ = lean_ctor_get(v_snd_2994_, 0);
v_snd_2996_ = lean_ctor_get(v_snd_2994_, 1);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_snd_2994_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_2998_ = v_snd_2994_;
v_isShared_2999_ = v_isSharedCheck_3058_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_snd_2996_);
lean_inc(v_fst_2995_);
lean_dec(v_snd_2994_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3058_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3000_; 
lean_inc(v_fst_2995_);
v___x_3000_ = l_Lean_Meta_isExprDefEq(v_fst_2995_, v_snd_2996_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; uint8_t v___x_3002_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = lean_unbox(v_a_3001_);
lean_dec(v_a_3001_);
if (v___x_3002_ == 0)
{
lean_del_object(v___x_2998_);
lean_dec(v_fst_2995_);
lean_del_object(v___x_2992_);
v___y_2851_ = v___y_2942_;
v___y_2852_ = v___y_2943_;
v___y_2853_ = v___y_2944_;
v___y_2854_ = v___y_2945_;
goto v___jp_2850_;
}
else
{
lean_object* v___x_3003_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec_ref(v_config_2546_);
lean_inc(v_mvarId_2547_);
v___x_3003_ = l_Lean_MVarId_getType(v_mvarId_2547_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = l_Lean_Meta_mkEqRefl(v_fst_2995_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = l_Lean_LocalDecl_toExpr(v_val_2578_);
v___x_3008_ = l_Lean_Meta_mkAbsurd(v_a_3004_, v_a_3006_, v___x_3007_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2547_, v_a_3009_, v___y_2943_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3013_; 
lean_dec_ref_known(v___x_3010_, 1);
v___x_3011_ = lean_box(v___x_2557_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_3011_);
v___x_3013_ = v___x_2992_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3015_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 1, v___x_2582_);
lean_ctor_set(v___x_2998_, 0, v___x_3013_);
v___x_3015_ = v___x_2998_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___x_2582_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
v_a_2564_ = v___x_3015_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_del_object(v___x_2998_);
lean_del_object(v___x_2992_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_3018_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3010_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3010_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_del_object(v___x_2998_);
lean_del_object(v___x_2992_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_3026_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3008_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3008_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_a_3004_);
lean_del_object(v___x_2998_);
lean_del_object(v___x_2992_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_3034_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3005_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3005_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_del_object(v___x_2998_);
lean_dec(v_fst_2995_);
lean_del_object(v___x_2992_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
v_a_3042_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3003_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3003_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_del_object(v___x_2998_);
lean_dec(v_fst_2995_);
lean_del_object(v___x_2992_);
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_3050_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3000_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3000_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2989_);
v___y_2851_ = v___y_2942_;
v___y_2852_ = v___y_2943_;
v___y_2853_ = v___y_2944_;
v___y_2854_ = v___y_2945_;
goto v___jp_2850_;
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_3060_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_2988_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_2988_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v___x_2611_);
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_3068_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_2946_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_2946_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
else
{
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_2572_ = v___x_2583_;
goto v___jp_2571_;
}
v___jp_2584_:
{
uint8_t v_emptyType_2591_; 
v_emptyType_2591_ = lean_ctor_get_uint8(v_config_2546_, sizeof(void*)*1 + 1);
if (v_emptyType_2591_ == 0)
{
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_2572_ = v___x_2583_;
goto v___jp_2571_;
}
else
{
if (v___y_2585_ == 0)
{
if (v___y_2586_ == 0)
{
lean_object* v_searchFuel_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_searchFuel_2592_ = lean_ctor_get(v_config_2546_, 0);
v___x_2593_ = l_Lean_LocalDecl_fvarId(v_val_2578_);
lean_dec(v_val_2578_);
lean_inc(v_searchFuel_2592_);
lean_inc(v_mvarId_2547_);
v___x_2594_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2547_, v___x_2593_, v_searchFuel_2592_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; uint8_t v___x_2596_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2596_ = lean_unbox(v_a_2595_);
lean_dec(v_a_2595_);
if (v___x_2596_ == 0)
{
lean_del_object(v___x_2580_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_2572_ = v___x_2583_;
goto v___jp_2571_;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v___x_2597_ = lean_box(v___x_2557_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2597_);
v___x_2599_ = v___x_2580_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2582_);
v_a_2564_ = v___x_2600_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_del_object(v___x_2580_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
lean_dec(v_mvarId_2547_);
lean_dec_ref(v_config_2546_);
v_a_2602_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2594_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2594_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_2572_ = v___x_2583_;
goto v___jp_2571_;
}
}
else
{
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_del_object(v___x_2561_);
lean_dec(v_snd_2559_);
v_a_2572_ = v___x_2583_;
goto v___jp_2571_;
}
}
}
}
}
v___jp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_a_2564_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2565_);
v___x_2567_ = v___x_2561_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_snd_2559_);
v___x_2567_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
return v___x_2568_;
}
}
v___jp_2571_:
{
lean_object* v___x_2573_; size_t v___x_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2570_);
lean_ctor_set(v___x_2573_, 1, v_a_2572_);
v___x_2574_ = ((size_t)1ULL);
v___x_2575_ = lean_usize_add(v_i_2550_, v___x_2574_);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2546_, v_mvarId_2547_, v_as_2548_, v_sz_2549_, v___x_2575_, v___x_2573_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3142_, lean_object* v_mvarId_3143_, lean_object* v_as_3144_, lean_object* v_sz_3145_, lean_object* v_i_3146_, lean_object* v_b_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
size_t v_sz_boxed_3153_; size_t v_i_boxed_3154_; lean_object* v_res_3155_; 
v_sz_boxed_3153_ = lean_unbox_usize(v_sz_3145_);
lean_dec(v_sz_3145_);
v_i_boxed_3154_ = lean_unbox_usize(v_i_3146_);
lean_dec(v_i_3146_);
v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3142_, v_mvarId_3143_, v_as_3144_, v_sz_boxed_3153_, v_i_boxed_3154_, v_b_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec_ref(v_as_3144_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3159_, lean_object* v_mvarId_3160_, lean_object* v_as_3161_, size_t v_sz_3162_, size_t v_i_3163_, lean_object* v_b_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
uint8_t v___x_3170_; 
v___x_3170_ = lean_usize_dec_lt(v_i_3163_, v_sz_3162_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; 
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v___x_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3171_, 0, v_b_3164_);
return v___x_3171_;
}
else
{
lean_object* v_snd_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3785_; 
v_snd_3172_ = lean_ctor_get(v_b_3164_, 1);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_b_3164_);
if (v_isSharedCheck_3785_ == 0)
{
lean_object* v_unused_3786_; 
v_unused_3786_ = lean_ctor_get(v_b_3164_, 0);
lean_dec(v_unused_3786_);
v___x_3174_ = v_b_3164_;
v_isShared_3175_ = v_isSharedCheck_3785_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_snd_3172_);
lean_dec(v_b_3164_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3785_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v_a_3177_; lean_object* v___x_3183_; lean_object* v_a_3185_; lean_object* v_a_3190_; 
v___x_3183_ = lean_box(0);
v_a_3190_ = lean_array_uget(v_as_3161_, v_i_3163_);
if (lean_obj_tag(v_a_3190_) == 0)
{
lean_del_object(v___x_3174_);
v_a_3185_ = v_snd_3172_;
goto v___jp_3184_;
}
else
{
lean_object* v_val_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3784_; 
v_val_3191_ = lean_ctor_get(v_a_3190_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v_a_3190_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3193_ = v_a_3190_;
v_isShared_3194_ = v_isSharedCheck_3784_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_val_3191_);
lean_dec(v_a_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3784_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; uint8_t v___y_3198_; uint8_t v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; uint8_t v___x_3224_; 
v___x_3195_ = lean_box(0);
v___x_3196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3224_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3191_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; uint8_t v___y_3227_; uint8_t v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; uint8_t v___y_3254_; uint8_t v___y_3255_; lean_object* v___y_3256_; lean_object* v_a_3257_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; uint8_t v___y_3266_; uint8_t v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3314_; uint8_t v_isHEq_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; uint8_t v_isEq_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___x_3714_; 
v___x_3225_ = l_Lean_LocalDecl_type(v_val_3191_);
lean_inc_ref(v___x_3225_);
v___x_3714_ = l_Lean_Meta_matchNot_x3f(v___x_3225_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_a_3715_);
lean_dec_ref_known(v___x_3714_, 1);
if (lean_obj_tag(v_a_3715_) == 1)
{
lean_object* v_val_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3775_; 
v_val_3716_ = lean_ctor_get(v_a_3715_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_a_3715_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3718_ = v_a_3715_;
v_isShared_3719_ = v_isSharedCheck_3775_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_val_3716_);
lean_dec(v_a_3715_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3775_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3716_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
if (lean_obj_tag(v_a_3721_) == 1)
{
lean_object* v_val_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3766_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec_ref(v_config_3159_);
v_val_3722_ = lean_ctor_get(v_a_3721_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v_a_3721_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3724_ = v_a_3721_;
v_isShared_3725_ = v_isSharedCheck_3766_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_val_3722_);
lean_dec(v_a_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3766_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; 
lean_inc(v_mvarId_3160_);
v___x_3726_ = l_Lean_MVarId_getType(v_mvarId_3160_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v___x_3728_ = l_Lean_LocalDecl_toExpr(v_val_3191_);
v___x_3729_ = l_Lean_mkFVar(v_val_3722_);
v___x_3730_ = l_Lean_Expr_app___override(v___x_3728_, v___x_3729_);
v___x_3731_ = l_Lean_Meta_mkFalseElim(v_a_3727_, v___x_3730_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
v___x_3733_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3160_, v_a_3732_, v___y_3166_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3736_; 
lean_dec_ref_known(v___x_3733_, 1);
v___x_3734_ = lean_box(v___x_3170_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3734_);
v___x_3736_ = v___x_3724_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3737_; lean_object* v___x_3739_; 
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3195_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set_tag(v___x_3718_, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3737_);
v___x_3739_ = v___x_3718_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
v_a_3177_ = v___x_3739_;
goto v___jp_3176_;
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_del_object(v___x_3724_);
lean_del_object(v___x_3718_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3742_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3733_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3733_);
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
lean_del_object(v___x_3724_);
lean_del_object(v___x_3718_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3750_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3731_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3731_);
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
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_del_object(v___x_3724_);
lean_dec(v_val_3722_);
lean_del_object(v___x_3718_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3758_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3726_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3726_);
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
else
{
lean_dec(v_a_3721_);
lean_del_object(v___x_3718_);
v___y_3578_ = v___y_3165_;
v___y_3579_ = v___y_3166_;
v___y_3580_ = v___y_3167_;
v___y_3581_ = v___y_3168_;
goto v___jp_3577_;
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_del_object(v___x_3718_);
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3767_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3720_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3720_);
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
}
else
{
lean_dec(v_a_3715_);
v___y_3578_ = v___y_3165_;
v___y_3579_ = v___y_3166_;
v___y_3580_ = v___y_3167_;
v___y_3581_ = v___y_3168_;
goto v___jp_3577_;
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3776_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3714_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3714_);
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
v___jp_3226_:
{
uint8_t v_genDiseq_3233_; 
v_genDiseq_3233_ = lean_ctor_get_uint8(v_config_3159_, sizeof(void*)*1 + 2);
if (v_genDiseq_3233_ == 0)
{
lean_dec_ref(v___x_3225_);
v___y_3198_ = v___y_3227_;
v___y_3199_ = v___y_3228_;
v___y_3200_ = v___y_3229_;
v___y_3201_ = v___y_3230_;
v___y_3202_ = v___y_3231_;
v___y_3203_ = v___y_3232_;
goto v___jp_3197_;
}
else
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3225_);
lean_dec_ref(v___x_3225_);
if (v___x_3234_ == 0)
{
v___y_3198_ = v___y_3227_;
v___y_3199_ = v___y_3228_;
v___y_3200_ = v___y_3229_;
v___y_3201_ = v___y_3230_;
v___y_3202_ = v___y_3231_;
v___y_3203_ = v___y_3232_;
goto v___jp_3197_;
}
else
{
lean_object* v___x_3235_; 
lean_inc(v_val_3191_);
lean_inc(v_mvarId_3160_);
v___x_3235_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3160_, v_val_3191_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; uint8_t v___x_3237_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v___x_3237_ = lean_unbox(v_a_3236_);
lean_dec(v_a_3236_);
if (v___x_3237_ == 0)
{
v___y_3198_ = v___y_3227_;
v___y_3199_ = v___y_3228_;
v___y_3200_ = v___y_3229_;
v___y_3201_ = v___y_3230_;
v___y_3202_ = v___y_3231_;
v___y_3203_ = v___y_3232_;
goto v___jp_3197_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v___x_3238_ = lean_box(v___x_3170_);
v___x_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
lean_ctor_set(v___x_3240_, 1, v___x_3195_);
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
v_a_3177_ = v___x_3241_;
goto v___jp_3176_;
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3242_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3235_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3235_);
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
}
}
v___jp_3250_:
{
uint8_t v___x_3258_; 
v___x_3258_ = l_Lean_Exception_isInterrupt(v_a_3257_);
if (v___x_3258_ == 0)
{
uint8_t v___x_3259_; 
lean_inc_ref(v_a_3257_);
v___x_3259_ = l_Lean_Exception_isRuntime(v_a_3257_);
if (v___x_3259_ == 0)
{
lean_dec_ref(v_a_3257_);
v___y_3227_ = v___y_3254_;
v___y_3228_ = v___y_3255_;
v___y_3229_ = v___y_3251_;
v___y_3230_ = v___y_3256_;
v___y_3231_ = v___y_3253_;
v___y_3232_ = v___y_3252_;
goto v___jp_3226_;
}
else
{
lean_object* v___x_3260_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v___x_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3260_, 0, v_a_3257_);
return v___x_3260_;
}
}
else
{
lean_object* v___x_3261_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v___x_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_a_3257_);
return v___x_3261_;
}
}
v___jp_3262_:
{
if (lean_obj_tag(v___y_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v_a_3271_ = lean_ctor_get(v___y_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___y_3270_, 1);
v___x_3272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3273_ = l_Lean_Expr_isConstOf(v_a_3271_, v___x_3272_);
lean_dec(v_a_3271_);
if (v___x_3273_ == 0)
{
lean_dec_ref(v___y_3268_);
v___y_3227_ = v___y_3266_;
v___y_3228_ = v___y_3267_;
v___y_3229_ = v___y_3263_;
v___y_3230_ = v___y_3269_;
v___y_3231_ = v___y_3265_;
v___y_3232_ = v___y_3264_;
goto v___jp_3226_;
}
else
{
lean_object* v___x_3274_; 
lean_inc_ref(v___y_3268_);
v___x_3274_ = l_Lean_Meta_mkEqRefl(v___y_3268_, v___y_3263_, v___y_3269_, v___y_3265_, v___y_3264_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v_dummy_3277_; lean_object* v_nargs_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3277_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3278_ = l_Lean_Expr_getAppNumArgs(v___y_3268_);
lean_inc(v_nargs_3278_);
v___x_3279_ = lean_mk_array(v_nargs_3278_, v_dummy_3277_);
v___x_3280_ = lean_unsigned_to_nat(1u);
v___x_3281_ = lean_nat_sub(v_nargs_3278_, v___x_3280_);
lean_dec(v_nargs_3278_);
v___x_3282_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3268_, v___x_3279_, v___x_3281_);
v___x_3283_ = lean_array_push(v___x_3282_, v_a_3275_);
v___x_3284_ = l_Lean_mkAppN(v___x_3276_, v___x_3283_);
lean_dec_ref(v___x_3283_);
lean_inc(v_mvarId_3160_);
v___x_3285_ = l_Lean_MVarId_getType(v_mvarId_3160_, v___y_3263_, v___y_3269_, v___y_3265_, v___y_3264_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref_known(v___x_3285_, 1);
lean_inc(v_val_3191_);
v___x_3287_ = l_Lean_LocalDecl_toExpr(v_val_3191_);
v___x_3288_ = l_Lean_Meta_mkAbsurd(v_a_3286_, v___x_3287_, v___x_3284_, v___y_3263_, v___y_3269_, v___y_3265_, v___y_3264_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3308_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3308_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3308_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; 
lean_inc(v_mvarId_3160_);
v___x_3293_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3160_, v_a_3289_, v___y_3269_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3305_ == 0)
{
lean_object* v_unused_3306_; 
v_unused_3306_ = lean_ctor_get(v___x_3293_, 0);
lean_dec(v_unused_3306_);
v___x_3295_ = v___x_3293_;
v_isShared_3296_ = v_isSharedCheck_3305_;
goto v_resetjp_3294_;
}
else
{
lean_dec(v___x_3293_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3305_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3297_ = lean_box(v___x_3170_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set_tag(v___x_3295_, 1);
lean_ctor_set(v___x_3295_, 0, v___x_3297_);
v___x_3299_ = v___x_3295_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v___x_3195_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3300_);
v___x_3302_ = v___x_3291_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
v_a_3177_ = v___x_3302_;
goto v___jp_3176_;
}
}
}
}
else
{
lean_object* v_a_3307_; 
lean_del_object(v___x_3291_);
v_a_3307_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3293_, 1);
v___y_3251_ = v___y_3263_;
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3267_;
v___y_3256_ = v___y_3269_;
v_a_3257_ = v_a_3307_;
goto v___jp_3250_;
}
}
}
else
{
lean_object* v_a_3309_; 
v_a_3309_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3288_, 1);
v___y_3251_ = v___y_3263_;
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3267_;
v___y_3256_ = v___y_3269_;
v_a_3257_ = v_a_3309_;
goto v___jp_3250_;
}
}
else
{
lean_object* v_a_3310_; 
lean_dec_ref(v___x_3284_);
v_a_3310_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3285_, 1);
v___y_3251_ = v___y_3263_;
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3267_;
v___y_3256_ = v___y_3269_;
v_a_3257_ = v_a_3310_;
goto v___jp_3250_;
}
}
else
{
lean_object* v_a_3311_; 
lean_dec_ref(v___y_3268_);
v_a_3311_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3274_, 1);
v___y_3251_ = v___y_3263_;
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3267_;
v___y_3256_ = v___y_3269_;
v_a_3257_ = v_a_3311_;
goto v___jp_3250_;
}
}
}
else
{
lean_object* v_a_3312_; 
lean_dec_ref(v___y_3268_);
v_a_3312_ = lean_ctor_get(v___y_3270_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___y_3270_, 1);
v___y_3251_ = v___y_3263_;
v___y_3252_ = v___y_3264_;
v___y_3253_ = v___y_3265_;
v___y_3254_ = v___y_3266_;
v___y_3255_ = v___y_3267_;
v___y_3256_ = v___y_3269_;
v_a_3257_ = v_a_3312_;
goto v___jp_3250_;
}
}
v___jp_3313_:
{
uint8_t v_useDecide_3320_; 
v_useDecide_3320_ = lean_ctor_get_uint8(v_config_3159_, sizeof(void*)*1);
if (v_useDecide_3320_ == 0)
{
v___y_3227_ = v___y_3314_;
v___y_3228_ = v_isHEq_3315_;
v___y_3229_ = v___y_3316_;
v___y_3230_ = v___y_3317_;
v___y_3231_ = v___y_3318_;
v___y_3232_ = v___y_3319_;
goto v___jp_3226_;
}
else
{
uint8_t v___x_3321_; 
v___x_3321_ = l_Lean_Expr_hasFVar(v___x_3225_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; 
lean_inc_ref(v___x_3225_);
v___x_3322_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3225_, v___y_3317_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; uint8_t v___x_3324_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3322_, 1);
v___x_3324_ = l_Lean_Expr_hasMVar(v_a_3323_);
if (v___x_3324_ == 0)
{
uint8_t v___x_3325_; 
v___x_3325_ = l_Lean_Expr_hasFVar(v_a_3323_);
lean_dec(v_a_3323_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_inc_ref(v___x_3225_);
v___x_3326_ = l_Lean_Meta_mkDecide(v___x_3225_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; uint8_t v_transparency_3329_; uint8_t v___x_3330_; uint8_t v___x_3331_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = l_Lean_Meta_Context_config(v___y_3316_);
v_transparency_3329_ = lean_ctor_get_uint8(v___x_3328_, 9);
lean_dec_ref(v___x_3328_);
v___x_3330_ = 1;
v___x_3331_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3329_, v___x_3330_);
if (v___x_3331_ == 0)
{
lean_object* v_keyedConfig_3332_; uint8_t v_trackZetaDelta_3333_; lean_object* v_zetaDeltaSet_3334_; lean_object* v_lctx_3335_; lean_object* v_localInstances_3336_; lean_object* v_defEqCtx_x3f_3337_; lean_object* v_synthPendingDepth_3338_; lean_object* v_customCanUnfoldPredicate_x3f_3339_; uint8_t v_univApprox_3340_; uint8_t v_inTypeClassResolution_3341_; uint8_t v_cacheInferType_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v_keyedConfig_3332_ = lean_ctor_get(v___y_3316_, 0);
v_trackZetaDelta_3333_ = lean_ctor_get_uint8(v___y_3316_, sizeof(void*)*7);
v_zetaDeltaSet_3334_ = lean_ctor_get(v___y_3316_, 1);
v_lctx_3335_ = lean_ctor_get(v___y_3316_, 2);
v_localInstances_3336_ = lean_ctor_get(v___y_3316_, 3);
v_defEqCtx_x3f_3337_ = lean_ctor_get(v___y_3316_, 4);
v_synthPendingDepth_3338_ = lean_ctor_get(v___y_3316_, 5);
v_customCanUnfoldPredicate_x3f_3339_ = lean_ctor_get(v___y_3316_, 6);
v_univApprox_3340_ = lean_ctor_get_uint8(v___y_3316_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3341_ = lean_ctor_get_uint8(v___y_3316_, sizeof(void*)*7 + 2);
v_cacheInferType_3342_ = lean_ctor_get_uint8(v___y_3316_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3332_);
v___x_3343_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3330_, v_keyedConfig_3332_);
lean_inc(v_customCanUnfoldPredicate_x3f_3339_);
lean_inc(v_synthPendingDepth_3338_);
lean_inc(v_defEqCtx_x3f_3337_);
lean_inc_ref(v_localInstances_3336_);
lean_inc_ref(v_lctx_3335_);
lean_inc(v_zetaDeltaSet_3334_);
v___x_3344_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
lean_ctor_set(v___x_3344_, 1, v_zetaDeltaSet_3334_);
lean_ctor_set(v___x_3344_, 2, v_lctx_3335_);
lean_ctor_set(v___x_3344_, 3, v_localInstances_3336_);
lean_ctor_set(v___x_3344_, 4, v_defEqCtx_x3f_3337_);
lean_ctor_set(v___x_3344_, 5, v_synthPendingDepth_3338_);
lean_ctor_set(v___x_3344_, 6, v_customCanUnfoldPredicate_x3f_3339_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7, v_trackZetaDelta_3333_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 1, v_univApprox_3340_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3341_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 3, v_cacheInferType_3342_);
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3318_);
lean_inc(v___y_3317_);
lean_inc(v_a_3327_);
v___x_3345_ = lean_whnf(v_a_3327_, v___x_3344_, v___y_3317_, v___y_3318_, v___y_3319_);
v___y_3263_ = v___y_3316_;
v___y_3264_ = v___y_3319_;
v___y_3265_ = v___y_3318_;
v___y_3266_ = v___y_3314_;
v___y_3267_ = v_isHEq_3315_;
v___y_3268_ = v_a_3327_;
v___y_3269_ = v___y_3317_;
v___y_3270_ = v___x_3345_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3346_; 
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3318_);
lean_inc(v___y_3317_);
lean_inc_ref(v___y_3316_);
lean_inc(v_a_3327_);
v___x_3346_ = lean_whnf(v_a_3327_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
v___y_3263_ = v___y_3316_;
v___y_3264_ = v___y_3319_;
v___y_3265_ = v___y_3318_;
v___y_3266_ = v___y_3314_;
v___y_3267_ = v_isHEq_3315_;
v___y_3268_ = v_a_3327_;
v___y_3269_ = v___y_3317_;
v___y_3270_ = v___x_3346_;
goto v___jp_3262_;
}
}
else
{
lean_object* v_a_3347_; 
v_a_3347_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3326_, 1);
v___y_3251_ = v___y_3316_;
v___y_3252_ = v___y_3319_;
v___y_3253_ = v___y_3318_;
v___y_3254_ = v___y_3314_;
v___y_3255_ = v_isHEq_3315_;
v___y_3256_ = v___y_3317_;
v_a_3257_ = v_a_3347_;
goto v___jp_3250_;
}
}
else
{
v___y_3227_ = v___y_3314_;
v___y_3228_ = v_isHEq_3315_;
v___y_3229_ = v___y_3316_;
v___y_3230_ = v___y_3317_;
v___y_3231_ = v___y_3318_;
v___y_3232_ = v___y_3319_;
goto v___jp_3226_;
}
}
else
{
lean_dec(v_a_3323_);
v___y_3227_ = v___y_3314_;
v___y_3228_ = v_isHEq_3315_;
v___y_3229_ = v___y_3316_;
v___y_3230_ = v___y_3317_;
v___y_3231_ = v___y_3318_;
v___y_3232_ = v___y_3319_;
goto v___jp_3226_;
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3348_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3322_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3322_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
v___y_3227_ = v___y_3314_;
v___y_3228_ = v_isHEq_3315_;
v___y_3229_ = v___y_3316_;
v___y_3230_ = v___y_3317_;
v___y_3231_ = v___y_3318_;
v___y_3232_ = v___y_3319_;
goto v___jp_3226_;
}
}
}
v___jp_3356_:
{
lean_object* v___x_3362_; 
lean_inc_ref(v___x_3225_);
v___x_3362_ = l_Lean_Meta_matchHEq_x3f(v___x_3225_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
if (lean_obj_tag(v_a_3363_) == 1)
{
lean_object* v_val_3364_; lean_object* v_snd_3365_; lean_object* v_snd_3366_; lean_object* v_fst_3367_; lean_object* v_fst_3368_; lean_object* v_fst_3369_; lean_object* v_snd_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3470_; 
v_val_3364_ = lean_ctor_get(v_a_3363_, 0);
lean_inc(v_val_3364_);
lean_dec_ref_known(v_a_3363_, 1);
v_snd_3365_ = lean_ctor_get(v_val_3364_, 1);
lean_inc(v_snd_3365_);
v_snd_3366_ = lean_ctor_get(v_snd_3365_, 1);
lean_inc(v_snd_3366_);
v_fst_3367_ = lean_ctor_get(v_val_3364_, 0);
lean_inc(v_fst_3367_);
lean_dec(v_val_3364_);
v_fst_3368_ = lean_ctor_get(v_snd_3365_, 0);
lean_inc(v_fst_3368_);
lean_dec(v_snd_3365_);
v_fst_3369_ = lean_ctor_get(v_snd_3366_, 0);
v_snd_3370_ = lean_ctor_get(v_snd_3366_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_snd_3366_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3372_ = v_snd_3366_;
v_isShared_3373_ = v_isSharedCheck_3470_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_snd_3370_);
lean_inc(v_fst_3369_);
lean_dec(v_snd_3366_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3470_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3368_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
if (lean_obj_tag(v_a_3375_) == 1)
{
lean_object* v_val_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3461_; 
v_val_3376_ = lean_ctor_get(v_a_3375_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v_a_3375_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3378_ = v_a_3375_;
v_isShared_3379_ = v_isSharedCheck_3461_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_val_3376_);
lean_dec(v_a_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3461_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3370_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3380_, 1);
if (lean_obj_tag(v_a_3381_) == 1)
{
lean_object* v_toConstantVal_3382_; lean_object* v_val_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3452_; 
v_toConstantVal_3382_ = lean_ctor_get(v_val_3376_, 0);
lean_inc_ref(v_toConstantVal_3382_);
lean_dec(v_val_3376_);
v_val_3383_ = lean_ctor_get(v_a_3381_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_a_3381_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3385_ = v_a_3381_;
v_isShared_3386_ = v_isSharedCheck_3452_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_val_3383_);
lean_dec(v_a_3381_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3452_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v_toConstantVal_3387_; lean_object* v_name_3388_; lean_object* v_name_3389_; uint8_t v___x_3390_; 
v_toConstantVal_3387_ = lean_ctor_get(v_val_3383_, 0);
lean_inc_ref(v_toConstantVal_3387_);
lean_dec(v_val_3383_);
v_name_3388_ = lean_ctor_get(v_toConstantVal_3382_, 0);
lean_inc(v_name_3388_);
lean_dec_ref(v_toConstantVal_3382_);
v_name_3389_ = lean_ctor_get(v_toConstantVal_3387_, 0);
lean_inc(v_name_3389_);
lean_dec_ref(v_toConstantVal_3387_);
v___x_3390_ = lean_name_eq(v_name_3388_, v_name_3389_);
lean_dec(v_name_3389_);
lean_dec(v_name_3388_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Meta_isExprDefEq(v_fst_3367_, v_fst_3369_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; uint8_t v___x_3393_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3393_ = lean_unbox(v_a_3392_);
lean_dec(v_a_3392_);
if (v___x_3393_ == 0)
{
lean_del_object(v___x_3385_);
lean_del_object(v___x_3378_);
lean_del_object(v___x_3372_);
v___y_3314_ = v_isEq_3357_;
v_isHEq_3315_ = v___x_3170_;
v___y_3316_ = v___y_3358_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
goto v___jp_3313_;
}
else
{
lean_object* v___x_3394_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec_ref(v_config_3159_);
lean_inc(v_mvarId_3160_);
v___x_3394_ = l_Lean_MVarId_getType(v_mvarId_3160_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v___x_3396_ = l_Lean_LocalDecl_toExpr(v_val_3191_);
v___x_3397_ = l_Lean_Meta_mkEqOfHEq(v___x_3396_, v___x_3170_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3399_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3397_, 1);
v___x_3399_ = l_Lean_Meta_mkNoConfusion(v_a_3395_, v_a_3398_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3401_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v___x_3401_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3160_, v_a_3400_, v___y_3359_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
lean_dec_ref_known(v___x_3401_, 1);
v___x_3402_ = lean_box(v___x_3170_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3402_);
v___x_3404_ = v___x_3385_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3406_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 1, v___x_3195_);
lean_ctor_set(v___x_3372_, 0, v___x_3404_);
v___x_3406_ = v___x_3372_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v___x_3195_);
v___x_3406_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3408_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3406_);
v___x_3408_ = v___x_3378_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
v_a_3177_ = v___x_3408_;
goto v___jp_3176_;
}
}
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_del_object(v___x_3385_);
lean_del_object(v___x_3378_);
lean_del_object(v___x_3372_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3412_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3401_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3401_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_del_object(v___x_3385_);
lean_del_object(v___x_3378_);
lean_del_object(v___x_3372_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3420_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3399_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3399_);
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
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v_a_3395_);
lean_del_object(v___x_3385_);
lean_del_object(v___x_3378_);
lean_del_object(v___x_3372_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3428_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3397_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3397_);
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
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_del_object(v___x_3385_);
lean_del_object(v___x_3378_);
lean_del_object(v___x_3372_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3436_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3394_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3394_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_del_object(v___x_3385_);
lean_del_object(v___x_3378_);
lean_del_object(v___x_3372_);
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3444_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3391_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3391_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
lean_del_object(v___x_3385_);
lean_del_object(v___x_3378_);
lean_del_object(v___x_3372_);
lean_dec(v_fst_3369_);
lean_dec(v_fst_3367_);
v___y_3314_ = v_isEq_3357_;
v_isHEq_3315_ = v___x_3170_;
v___y_3316_ = v___y_3358_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
goto v___jp_3313_;
}
}
}
else
{
lean_dec(v_a_3381_);
lean_del_object(v___x_3378_);
lean_dec(v_val_3376_);
lean_del_object(v___x_3372_);
lean_dec(v_fst_3369_);
lean_dec(v_fst_3367_);
v___y_3314_ = v_isEq_3357_;
v_isHEq_3315_ = v___x_3170_;
v___y_3316_ = v___y_3358_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
goto v___jp_3313_;
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_del_object(v___x_3378_);
lean_dec(v_val_3376_);
lean_del_object(v___x_3372_);
lean_dec(v_fst_3369_);
lean_dec(v_fst_3367_);
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3453_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3380_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3380_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
else
{
lean_dec(v_a_3375_);
lean_del_object(v___x_3372_);
lean_dec(v_snd_3370_);
lean_dec(v_fst_3369_);
lean_dec(v_fst_3367_);
v___y_3314_ = v_isEq_3357_;
v_isHEq_3315_ = v___x_3170_;
v___y_3316_ = v___y_3358_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
goto v___jp_3313_;
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_del_object(v___x_3372_);
lean_dec(v_snd_3370_);
lean_dec(v_fst_3369_);
lean_dec(v_fst_3367_);
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3462_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3374_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3374_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
else
{
lean_dec(v_a_3363_);
v___y_3314_ = v_isEq_3357_;
v_isHEq_3315_ = v___x_3224_;
v___y_3316_ = v___y_3358_;
v___y_3317_ = v___y_3359_;
v___y_3318_ = v___y_3360_;
v___y_3319_ = v___y_3361_;
goto v___jp_3313_;
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3471_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3362_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3362_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
v___jp_3479_:
{
lean_object* v___x_3484_; 
lean_inc_ref(v___x_3225_);
v___x_3484_ = l_Lean_Meta_matchEq_x3f(v___x_3225_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v___x_3484_, 1);
if (lean_obj_tag(v_a_3485_) == 1)
{
lean_object* v_val_3486_; lean_object* v_snd_3487_; lean_object* v_fst_3488_; lean_object* v_snd_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3568_; 
v_val_3486_ = lean_ctor_get(v_a_3485_, 0);
lean_inc(v_val_3486_);
lean_dec_ref_known(v_a_3485_, 1);
v_snd_3487_ = lean_ctor_get(v_val_3486_, 1);
lean_inc(v_snd_3487_);
lean_dec(v_val_3486_);
v_fst_3488_ = lean_ctor_get(v_snd_3487_, 0);
v_snd_3489_ = lean_ctor_get(v_snd_3487_, 1);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_snd_3487_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3491_ = v_snd_3487_;
v_isShared_3492_ = v_isSharedCheck_3568_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_snd_3489_);
lean_inc(v_fst_3488_);
lean_dec(v_snd_3487_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3568_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3488_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
if (lean_obj_tag(v_a_3494_) == 1)
{
lean_object* v_val_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3559_; 
v_val_3495_ = lean_ctor_get(v_a_3494_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_a_3494_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3497_ = v_a_3494_;
v_isShared_3498_ = v_isSharedCheck_3559_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_val_3495_);
lean_dec(v_a_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3559_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3489_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
if (lean_obj_tag(v_a_3500_) == 1)
{
lean_object* v_toConstantVal_3501_; lean_object* v_val_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3550_; 
v_toConstantVal_3501_ = lean_ctor_get(v_val_3495_, 0);
lean_inc_ref(v_toConstantVal_3501_);
lean_dec(v_val_3495_);
v_val_3502_ = lean_ctor_get(v_a_3500_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_a_3500_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3504_ = v_a_3500_;
v_isShared_3505_ = v_isSharedCheck_3550_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_val_3502_);
lean_dec(v_a_3500_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3550_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v_toConstantVal_3506_; lean_object* v_name_3507_; lean_object* v_name_3508_; uint8_t v___x_3509_; 
v_toConstantVal_3506_ = lean_ctor_get(v_val_3502_, 0);
lean_inc_ref(v_toConstantVal_3506_);
lean_dec(v_val_3502_);
v_name_3507_ = lean_ctor_get(v_toConstantVal_3501_, 0);
lean_inc(v_name_3507_);
lean_dec_ref(v_toConstantVal_3501_);
v_name_3508_ = lean_ctor_get(v_toConstantVal_3506_, 0);
lean_inc(v_name_3508_);
lean_dec_ref(v_toConstantVal_3506_);
v___x_3509_ = lean_name_eq(v_name_3507_, v_name_3508_);
lean_dec(v_name_3508_);
lean_dec(v_name_3507_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec_ref(v_config_3159_);
lean_inc(v_mvarId_3160_);
v___x_3510_ = l_Lean_MVarId_getType(v_mvarId_3160_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
v___x_3512_ = l_Lean_LocalDecl_toExpr(v_val_3191_);
v___x_3513_ = l_Lean_Meta_mkNoConfusion(v_a_3511_, v___x_3512_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3160_, v_a_3514_, v___y_3481_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
lean_dec_ref_known(v___x_3515_, 1);
v___x_3516_ = lean_box(v___x_3170_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3516_);
v___x_3518_ = v___x_3504_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3520_; 
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v___x_3195_);
lean_ctor_set(v___x_3491_, 0, v___x_3518_);
v___x_3520_ = v___x_3491_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v___x_3195_);
v___x_3520_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set_tag(v___x_3497_, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3520_);
v___x_3522_ = v___x_3497_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
v_a_3177_ = v___x_3522_;
goto v___jp_3176_;
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_del_object(v___x_3504_);
lean_del_object(v___x_3497_);
lean_del_object(v___x_3491_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3526_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3515_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3515_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_del_object(v___x_3504_);
lean_del_object(v___x_3497_);
lean_del_object(v___x_3491_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3534_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3513_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3513_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_del_object(v___x_3504_);
lean_del_object(v___x_3497_);
lean_del_object(v___x_3491_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3542_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3510_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3510_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
lean_del_object(v___x_3504_);
lean_del_object(v___x_3497_);
lean_del_object(v___x_3491_);
v_isEq_3357_ = v___x_3170_;
v___y_3358_ = v___y_3480_;
v___y_3359_ = v___y_3481_;
v___y_3360_ = v___y_3482_;
v___y_3361_ = v___y_3483_;
goto v___jp_3356_;
}
}
}
else
{
lean_dec(v_a_3500_);
lean_del_object(v___x_3497_);
lean_dec(v_val_3495_);
lean_del_object(v___x_3491_);
v_isEq_3357_ = v___x_3170_;
v___y_3358_ = v___y_3480_;
v___y_3359_ = v___y_3481_;
v___y_3360_ = v___y_3482_;
v___y_3361_ = v___y_3483_;
goto v___jp_3356_;
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_del_object(v___x_3497_);
lean_dec(v_val_3495_);
lean_del_object(v___x_3491_);
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3551_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3499_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3499_);
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
}
else
{
lean_dec(v_a_3494_);
lean_del_object(v___x_3491_);
lean_dec(v_snd_3489_);
v_isEq_3357_ = v___x_3170_;
v___y_3358_ = v___y_3480_;
v___y_3359_ = v___y_3481_;
v___y_3360_ = v___y_3482_;
v___y_3361_ = v___y_3483_;
goto v___jp_3356_;
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_del_object(v___x_3491_);
lean_dec(v_snd_3489_);
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3560_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3493_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3493_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
}
else
{
lean_dec(v_a_3485_);
v_isEq_3357_ = v___x_3224_;
v___y_3358_ = v___y_3480_;
v___y_3359_ = v___y_3481_;
v___y_3360_ = v___y_3482_;
v___y_3361_ = v___y_3483_;
goto v___jp_3356_;
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3569_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3484_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3484_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
v___jp_3577_:
{
lean_object* v___x_3582_; 
lean_inc_ref(v___x_3225_);
v___x_3582_ = l_Lean_refutableHasNotBit_x3f(v___x_3225_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
if (lean_obj_tag(v_a_3583_) == 1)
{
lean_object* v_val_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3624_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec_ref(v_config_3159_);
v_val_3584_ = lean_ctor_get(v_a_3583_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_a_3583_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3586_ = v_a_3583_;
v_isShared_3587_ = v_isSharedCheck_3624_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_val_3584_);
lean_dec(v_a_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3624_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; 
lean_inc(v_mvarId_3160_);
v___x_3588_ = l_Lean_MVarId_getType(v_mvarId_3160_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = l_Lean_LocalDecl_toExpr(v_val_3191_);
v___x_3591_ = l_Lean_Meta_mkAbsurd(v_a_3589_, v_val_3584_, v___x_3590_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v___x_3591_, 1);
v___x_3593_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3160_, v_a_3592_, v___y_3579_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
lean_dec_ref_known(v___x_3593_, 1);
v___x_3594_ = lean_box(v___x_3170_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3594_);
v___x_3596_ = v___x_3586_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
lean_ctor_set(v___x_3597_, 1, v___x_3195_);
v___x_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
v_a_3177_ = v___x_3598_;
goto v___jp_3176_;
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_del_object(v___x_3586_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3600_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3593_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3593_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_del_object(v___x_3586_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3608_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3591_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3591_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_del_object(v___x_3586_);
lean_dec(v_val_3584_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3616_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3588_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3588_);
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
else
{
lean_object* v___x_3625_; 
lean_dec(v_a_3583_);
lean_inc_ref(v___x_3225_);
v___x_3625_ = l_Lean_Meta_matchNe_x3f(v___x_3225_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3625_, 1);
if (lean_obj_tag(v_a_3626_) == 1)
{
lean_object* v_val_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3697_; 
v_val_3627_ = lean_ctor_get(v_a_3626_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_a_3626_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3629_ = v_a_3626_;
v_isShared_3630_ = v_isSharedCheck_3697_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_val_3627_);
lean_dec(v_a_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3697_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v_snd_3631_; lean_object* v_fst_3632_; lean_object* v_snd_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3696_; 
v_snd_3631_ = lean_ctor_get(v_val_3627_, 1);
lean_inc(v_snd_3631_);
lean_dec(v_val_3627_);
v_fst_3632_ = lean_ctor_get(v_snd_3631_, 0);
v_snd_3633_ = lean_ctor_get(v_snd_3631_, 1);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_snd_3631_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3635_ = v_snd_3631_;
v_isShared_3636_ = v_isSharedCheck_3696_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_snd_3633_);
lean_inc(v_fst_3632_);
lean_dec(v_snd_3631_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3696_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; 
lean_inc(v_fst_3632_);
v___x_3637_ = l_Lean_Meta_isExprDefEq(v_fst_3632_, v_snd_3633_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; uint8_t v___x_3639_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v___x_3639_ = lean_unbox(v_a_3638_);
lean_dec(v_a_3638_);
if (v___x_3639_ == 0)
{
lean_del_object(v___x_3635_);
lean_dec(v_fst_3632_);
lean_del_object(v___x_3629_);
v___y_3480_ = v___y_3578_;
v___y_3481_ = v___y_3579_;
v___y_3482_ = v___y_3580_;
v___y_3483_ = v___y_3581_;
goto v___jp_3479_;
}
else
{
lean_object* v___x_3640_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec_ref(v_config_3159_);
lean_inc(v_mvarId_3160_);
v___x_3640_ = l_Lean_MVarId_getType(v_mvarId_3160_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v___x_3642_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref_known(v___x_3640_, 1);
v___x_3642_ = l_Lean_Meta_mkEqRefl(v_fst_3632_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___x_3642_, 1);
v___x_3644_ = l_Lean_LocalDecl_toExpr(v_val_3191_);
v___x_3645_ = l_Lean_Meta_mkAbsurd(v_a_3641_, v_a_3643_, v___x_3644_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3647_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3645_, 1);
v___x_3647_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3160_, v_a_3646_, v___y_3579_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v___x_3648_; lean_object* v___x_3650_; 
lean_dec_ref_known(v___x_3647_, 1);
v___x_3648_ = lean_box(v___x_3170_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3648_);
v___x_3650_ = v___x_3629_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3652_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 1, v___x_3195_);
lean_ctor_set(v___x_3635_, 0, v___x_3650_);
v___x_3652_ = v___x_3635_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___x_3195_);
v___x_3652_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; 
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
v_a_3177_ = v___x_3653_;
goto v___jp_3176_;
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_del_object(v___x_3635_);
lean_del_object(v___x_3629_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3656_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3647_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3647_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_del_object(v___x_3635_);
lean_del_object(v___x_3629_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3664_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3645_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3645_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v_a_3641_);
lean_del_object(v___x_3635_);
lean_del_object(v___x_3629_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3672_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3642_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3642_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_del_object(v___x_3635_);
lean_dec(v_fst_3632_);
lean_del_object(v___x_3629_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
v_a_3680_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3640_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3640_);
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
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_del_object(v___x_3635_);
lean_dec(v_fst_3632_);
lean_del_object(v___x_3629_);
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3688_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3637_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3637_);
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
}
}
else
{
lean_dec(v_a_3626_);
v___y_3480_ = v___y_3578_;
v___y_3481_ = v___y_3579_;
v___y_3482_ = v___y_3580_;
v___y_3483_ = v___y_3581_;
goto v___jp_3479_;
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3698_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3625_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3625_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3706_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3582_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3582_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
else
{
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3185_ = v___x_3196_;
goto v___jp_3184_;
}
v___jp_3197_:
{
uint8_t v_emptyType_3204_; 
v_emptyType_3204_ = lean_ctor_get_uint8(v_config_3159_, sizeof(void*)*1 + 1);
if (v_emptyType_3204_ == 0)
{
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3185_ = v___x_3196_;
goto v___jp_3184_;
}
else
{
if (v___y_3198_ == 0)
{
if (v___y_3199_ == 0)
{
lean_object* v_searchFuel_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_searchFuel_3205_ = lean_ctor_get(v_config_3159_, 0);
v___x_3206_ = l_Lean_LocalDecl_fvarId(v_val_3191_);
lean_dec(v_val_3191_);
lean_inc(v_searchFuel_3205_);
lean_inc(v_mvarId_3160_);
v___x_3207_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3160_, v___x_3206_, v_searchFuel_3205_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; uint8_t v___x_3209_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v___x_3209_ = lean_unbox(v_a_3208_);
lean_dec(v_a_3208_);
if (v___x_3209_ == 0)
{
lean_del_object(v___x_3193_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3185_ = v___x_3196_;
goto v___jp_3184_;
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v___x_3210_ = lean_box(v___x_3170_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3210_);
v___x_3212_ = v___x_3193_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v___x_3195_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
v_a_3177_ = v___x_3214_;
goto v___jp_3176_;
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_del_object(v___x_3193_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
lean_dec(v_mvarId_3160_);
lean_dec_ref(v_config_3159_);
v_a_3216_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3207_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3207_);
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
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3185_ = v___x_3196_;
goto v___jp_3184_;
}
}
else
{
lean_del_object(v___x_3193_);
lean_dec(v_val_3191_);
lean_del_object(v___x_3174_);
lean_dec(v_snd_3172_);
v_a_3185_ = v___x_3196_;
goto v___jp_3184_;
}
}
}
}
}
v___jp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v_a_3177_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3178_);
v___x_3180_ = v___x_3174_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_snd_3172_);
v___x_3180_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
}
v___jp_3184_:
{
lean_object* v___x_3186_; size_t v___x_3187_; size_t v___x_3188_; 
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3183_);
lean_ctor_set(v___x_3186_, 1, v_a_3185_);
v___x_3187_ = ((size_t)1ULL);
v___x_3188_ = lean_usize_add(v_i_3163_, v___x_3187_);
v_i_3163_ = v___x_3188_;
v_b_3164_ = v___x_3186_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3787_, lean_object* v_mvarId_3788_, lean_object* v_as_3789_, lean_object* v_sz_3790_, lean_object* v_i_3791_, lean_object* v_b_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
size_t v_sz_boxed_3798_; size_t v_i_boxed_3799_; lean_object* v_res_3800_; 
v_sz_boxed_3798_ = lean_unbox_usize(v_sz_3790_);
lean_dec(v_sz_3790_);
v_i_boxed_3799_ = lean_unbox_usize(v_i_3791_);
lean_dec(v_i_3791_);
v_res_3800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3787_, v_mvarId_3788_, v_as_3789_, v_sz_boxed_3798_, v_i_boxed_3799_, v_b_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec_ref(v_as_3789_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3801_, lean_object* v_mvarId_3802_, lean_object* v_as_3803_, size_t v_sz_3804_, size_t v_i_3805_, lean_object* v_b_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
uint8_t v___x_3812_; 
v___x_3812_ = lean_usize_dec_lt(v_i_3805_, v_sz_3804_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; 
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v___x_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3813_, 0, v_b_3806_);
return v___x_3813_;
}
else
{
lean_object* v_snd_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_4427_; 
v_snd_3814_ = lean_ctor_get(v_b_3806_, 1);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_b_3806_);
if (v_isSharedCheck_4427_ == 0)
{
lean_object* v_unused_4428_; 
v_unused_4428_ = lean_ctor_get(v_b_3806_, 0);
lean_dec(v_unused_4428_);
v___x_3816_ = v_b_3806_;
v_isShared_3817_ = v_isSharedCheck_4427_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_snd_3814_);
lean_dec(v_b_3806_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_4427_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v_a_3819_; lean_object* v___x_3825_; lean_object* v_a_3827_; lean_object* v_a_3832_; 
v___x_3825_ = lean_box(0);
v_a_3832_ = lean_array_uget(v_as_3803_, v_i_3805_);
if (lean_obj_tag(v_a_3832_) == 0)
{
lean_del_object(v___x_3816_);
v_a_3827_ = v_snd_3814_;
goto v___jp_3826_;
}
else
{
lean_object* v_val_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_4426_; 
v_val_3833_ = lean_ctor_get(v_a_3832_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_a_3832_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_3835_ = v_a_3832_;
v_isShared_3836_ = v_isSharedCheck_4426_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_val_3833_);
lean_dec(v_a_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_4426_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___y_3840_; uint8_t v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; uint8_t v___x_3866_; 
v___x_3837_ = lean_box(0);
v___x_3838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3866_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3833_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; uint8_t v___y_3869_; uint8_t v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3893_; uint8_t v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; uint8_t v___y_3898_; lean_object* v_a_3899_; lean_object* v___y_3905_; uint8_t v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; uint8_t v___y_3911_; lean_object* v___y_3912_; uint8_t v___y_3956_; uint8_t v_isHEq_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; uint8_t v_isEq_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___x_4356_; 
v___x_3867_ = l_Lean_LocalDecl_type(v_val_3833_);
lean_inc_ref(v___x_3867_);
v___x_4356_ = l_Lean_Meta_matchNot_x3f(v___x_3867_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
if (lean_obj_tag(v_a_4357_) == 1)
{
lean_object* v_val_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4417_; 
v_val_4358_ = lean_ctor_get(v_a_4357_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_a_4357_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4360_ = v_a_4357_;
v_isShared_4361_ = v_isSharedCheck_4417_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_val_4358_);
lean_dec(v_a_4357_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4417_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4358_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
if (lean_obj_tag(v_a_4363_) == 1)
{
lean_object* v_val_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4408_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec_ref(v_config_3801_);
v_val_4364_ = lean_ctor_get(v_a_4363_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_a_4363_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4366_ = v_a_4363_;
v_isShared_4367_ = v_isSharedCheck_4408_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_val_4364_);
lean_dec(v_a_4363_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4408_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4368_; 
lean_inc(v_mvarId_3802_);
v___x_4368_ = l_Lean_MVarId_getType(v_mvarId_3802_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4368_, 1);
v___x_4370_ = l_Lean_LocalDecl_toExpr(v_val_3833_);
v___x_4371_ = l_Lean_mkFVar(v_val_4364_);
v___x_4372_ = l_Lean_Expr_app___override(v___x_4370_, v___x_4371_);
v___x_4373_ = l_Lean_Meta_mkFalseElim(v_a_4369_, v___x_4372_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; lean_object* v___x_4375_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_a_4374_);
lean_dec_ref_known(v___x_4373_, 1);
v___x_4375_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3802_, v_a_4374_, v___y_3808_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v___x_4376_; lean_object* v___x_4378_; 
lean_dec_ref_known(v___x_4375_, 1);
v___x_4376_ = lean_box(v___x_3812_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 0, v___x_4376_);
v___x_4378_ = v___x_4366_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4376_);
v___x_4378_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
lean_ctor_set(v___x_4379_, 1, v___x_3837_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set_tag(v___x_4360_, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4379_);
v___x_4381_ = v___x_4360_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
v_a_3819_ = v___x_4381_;
goto v___jp_3818_;
}
}
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
lean_del_object(v___x_4366_);
lean_del_object(v___x_4360_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_4384_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4375_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4375_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
lean_del_object(v___x_4366_);
lean_del_object(v___x_4360_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4392_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4373_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4373_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4360_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4400_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4368_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4368_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
else
{
lean_dec(v_a_4363_);
lean_del_object(v___x_4360_);
v___y_4220_ = v___y_3807_;
v___y_4221_ = v___y_3808_;
v___y_4222_ = v___y_3809_;
v___y_4223_ = v___y_3810_;
goto v___jp_4219_;
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_del_object(v___x_4360_);
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4409_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4362_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4362_);
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
lean_dec(v_a_4357_);
v___y_4220_ = v___y_3807_;
v___y_4221_ = v___y_3808_;
v___y_4222_ = v___y_3809_;
v___y_4223_ = v___y_3810_;
goto v___jp_4219_;
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4418_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4356_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4356_);
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
v___jp_3868_:
{
uint8_t v_genDiseq_3875_; 
v_genDiseq_3875_ = lean_ctor_get_uint8(v_config_3801_, sizeof(void*)*1 + 2);
if (v_genDiseq_3875_ == 0)
{
lean_dec_ref(v___x_3867_);
v___y_3840_ = v___y_3869_;
v___y_3841_ = v___y_3870_;
v___y_3842_ = v___y_3871_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
goto v___jp_3839_;
}
else
{
uint8_t v___x_3876_; 
v___x_3876_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3867_);
lean_dec_ref(v___x_3867_);
if (v___x_3876_ == 0)
{
v___y_3840_ = v___y_3869_;
v___y_3841_ = v___y_3870_;
v___y_3842_ = v___y_3871_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
goto v___jp_3839_;
}
else
{
lean_object* v___x_3877_; 
lean_inc(v_val_3833_);
lean_inc(v_mvarId_3802_);
v___x_3877_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3802_, v_val_3833_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; uint8_t v___x_3879_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v___x_3879_ = lean_unbox(v_a_3878_);
lean_dec(v_a_3878_);
if (v___x_3879_ == 0)
{
v___y_3840_ = v___y_3869_;
v___y_3841_ = v___y_3870_;
v___y_3842_ = v___y_3871_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
goto v___jp_3839_;
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v___x_3880_ = lean_box(v___x_3812_);
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v___x_3837_);
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
v_a_3819_ = v___x_3883_;
goto v___jp_3818_;
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_3884_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3877_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3877_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
}
v___jp_3892_:
{
uint8_t v___x_3900_; 
v___x_3900_ = l_Lean_Exception_isInterrupt(v_a_3899_);
if (v___x_3900_ == 0)
{
uint8_t v___x_3901_; 
lean_inc_ref(v_a_3899_);
v___x_3901_ = l_Lean_Exception_isRuntime(v_a_3899_);
if (v___x_3901_ == 0)
{
lean_dec_ref(v_a_3899_);
v___y_3869_ = v___y_3894_;
v___y_3870_ = v___y_3898_;
v___y_3871_ = v___y_3897_;
v___y_3872_ = v___y_3893_;
v___y_3873_ = v___y_3895_;
v___y_3874_ = v___y_3896_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3902_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v___x_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3902_, 0, v_a_3899_);
return v___x_3902_;
}
}
else
{
lean_object* v___x_3903_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v___x_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_a_3899_);
return v___x_3903_;
}
}
v___jp_3904_:
{
if (lean_obj_tag(v___y_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v_a_3913_ = lean_ctor_get(v___y_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___y_3912_, 1);
v___x_3914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3915_ = l_Lean_Expr_isConstOf(v_a_3913_, v___x_3914_);
lean_dec(v_a_3913_);
if (v___x_3915_ == 0)
{
lean_dec_ref(v___y_3907_);
v___y_3869_ = v___y_3906_;
v___y_3870_ = v___y_3911_;
v___y_3871_ = v___y_3910_;
v___y_3872_ = v___y_3905_;
v___y_3873_ = v___y_3908_;
v___y_3874_ = v___y_3909_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3916_; 
lean_inc_ref(v___y_3907_);
v___x_3916_ = l_Lean_Meta_mkEqRefl(v___y_3907_, v___y_3910_, v___y_3905_, v___y_3908_, v___y_3909_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v_dummy_3919_; lean_object* v_nargs_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3920_ = l_Lean_Expr_getAppNumArgs(v___y_3907_);
lean_inc(v_nargs_3920_);
v___x_3921_ = lean_mk_array(v_nargs_3920_, v_dummy_3919_);
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = lean_nat_sub(v_nargs_3920_, v___x_3922_);
lean_dec(v_nargs_3920_);
v___x_3924_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3907_, v___x_3921_, v___x_3923_);
v___x_3925_ = lean_array_push(v___x_3924_, v_a_3917_);
v___x_3926_ = l_Lean_mkAppN(v___x_3918_, v___x_3925_);
lean_dec_ref(v___x_3925_);
lean_inc(v_mvarId_3802_);
v___x_3927_ = l_Lean_MVarId_getType(v_mvarId_3802_, v___y_3910_, v___y_3905_, v___y_3908_, v___y_3909_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___x_3927_, 1);
lean_inc(v_val_3833_);
v___x_3929_ = l_Lean_LocalDecl_toExpr(v_val_3833_);
v___x_3930_ = l_Lean_Meta_mkAbsurd(v_a_3928_, v___x_3929_, v___x_3926_, v___y_3910_, v___y_3905_, v___y_3908_, v___y_3909_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3950_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3933_ = v___x_3930_;
v_isShared_3934_ = v_isSharedCheck_3950_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3950_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; 
lean_inc(v_mvarId_3802_);
v___x_3935_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3802_, v_a_3931_, v___y_3905_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3947_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; 
v_unused_3948_ = lean_ctor_get(v___x_3935_, 0);
lean_dec(v_unused_3948_);
v___x_3937_ = v___x_3935_;
v_isShared_3938_ = v_isSharedCheck_3947_;
goto v_resetjp_3936_;
}
else
{
lean_dec(v___x_3935_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3947_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3939_ = lean_box(v___x_3812_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set_tag(v___x_3937_, 1);
lean_ctor_set(v___x_3937_, 0, v___x_3939_);
v___x_3941_ = v___x_3937_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
lean_ctor_set(v___x_3942_, 1, v___x_3837_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3942_);
v___x_3944_ = v___x_3933_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
v_a_3819_ = v___x_3944_;
goto v___jp_3818_;
}
}
}
}
else
{
lean_object* v_a_3949_; 
lean_del_object(v___x_3933_);
v_a_3949_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3949_);
lean_dec_ref_known(v___x_3935_, 1);
v___y_3893_ = v___y_3905_;
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3908_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v_a_3899_ = v_a_3949_;
goto v___jp_3892_;
}
}
}
else
{
lean_object* v_a_3951_; 
v_a_3951_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3930_, 1);
v___y_3893_ = v___y_3905_;
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3908_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v_a_3899_ = v_a_3951_;
goto v___jp_3892_;
}
}
else
{
lean_object* v_a_3952_; 
lean_dec_ref(v___x_3926_);
v_a_3952_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3927_, 1);
v___y_3893_ = v___y_3905_;
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3908_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v_a_3899_ = v_a_3952_;
goto v___jp_3892_;
}
}
else
{
lean_object* v_a_3953_; 
lean_dec_ref(v___y_3907_);
v_a_3953_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3916_, 1);
v___y_3893_ = v___y_3905_;
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3908_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v_a_3899_ = v_a_3953_;
goto v___jp_3892_;
}
}
}
else
{
lean_object* v_a_3954_; 
lean_dec_ref(v___y_3907_);
v_a_3954_ = lean_ctor_get(v___y_3912_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___y_3912_, 1);
v___y_3893_ = v___y_3905_;
v___y_3894_ = v___y_3906_;
v___y_3895_ = v___y_3908_;
v___y_3896_ = v___y_3909_;
v___y_3897_ = v___y_3910_;
v___y_3898_ = v___y_3911_;
v_a_3899_ = v_a_3954_;
goto v___jp_3892_;
}
}
v___jp_3955_:
{
uint8_t v_useDecide_3962_; 
v_useDecide_3962_ = lean_ctor_get_uint8(v_config_3801_, sizeof(void*)*1);
if (v_useDecide_3962_ == 0)
{
v___y_3869_ = v___y_3956_;
v___y_3870_ = v_isHEq_3957_;
v___y_3871_ = v___y_3958_;
v___y_3872_ = v___y_3959_;
v___y_3873_ = v___y_3960_;
v___y_3874_ = v___y_3961_;
goto v___jp_3868_;
}
else
{
uint8_t v___x_3963_; 
v___x_3963_ = l_Lean_Expr_hasFVar(v___x_3867_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; 
lean_inc_ref(v___x_3867_);
v___x_3964_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3867_, v___y_3959_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; uint8_t v___x_3966_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
v___x_3966_ = l_Lean_Expr_hasMVar(v_a_3965_);
if (v___x_3966_ == 0)
{
uint8_t v___x_3967_; 
v___x_3967_ = l_Lean_Expr_hasFVar(v_a_3965_);
lean_dec(v_a_3965_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
lean_inc_ref(v___x_3867_);
v___x_3968_ = l_Lean_Meta_mkDecide(v___x_3867_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3970_; uint8_t v_transparency_3971_; uint8_t v___x_3972_; uint8_t v___x_3973_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref_known(v___x_3968_, 1);
v___x_3970_ = l_Lean_Meta_Context_config(v___y_3958_);
v_transparency_3971_ = lean_ctor_get_uint8(v___x_3970_, 9);
lean_dec_ref(v___x_3970_);
v___x_3972_ = 1;
v___x_3973_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3971_, v___x_3972_);
if (v___x_3973_ == 0)
{
lean_object* v_keyedConfig_3974_; uint8_t v_trackZetaDelta_3975_; lean_object* v_zetaDeltaSet_3976_; lean_object* v_lctx_3977_; lean_object* v_localInstances_3978_; lean_object* v_defEqCtx_x3f_3979_; lean_object* v_synthPendingDepth_3980_; lean_object* v_customCanUnfoldPredicate_x3f_3981_; uint8_t v_univApprox_3982_; uint8_t v_inTypeClassResolution_3983_; uint8_t v_cacheInferType_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_keyedConfig_3974_ = lean_ctor_get(v___y_3958_, 0);
v_trackZetaDelta_3975_ = lean_ctor_get_uint8(v___y_3958_, sizeof(void*)*7);
v_zetaDeltaSet_3976_ = lean_ctor_get(v___y_3958_, 1);
v_lctx_3977_ = lean_ctor_get(v___y_3958_, 2);
v_localInstances_3978_ = lean_ctor_get(v___y_3958_, 3);
v_defEqCtx_x3f_3979_ = lean_ctor_get(v___y_3958_, 4);
v_synthPendingDepth_3980_ = lean_ctor_get(v___y_3958_, 5);
v_customCanUnfoldPredicate_x3f_3981_ = lean_ctor_get(v___y_3958_, 6);
v_univApprox_3982_ = lean_ctor_get_uint8(v___y_3958_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3983_ = lean_ctor_get_uint8(v___y_3958_, sizeof(void*)*7 + 2);
v_cacheInferType_3984_ = lean_ctor_get_uint8(v___y_3958_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3974_);
v___x_3985_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3972_, v_keyedConfig_3974_);
lean_inc(v_customCanUnfoldPredicate_x3f_3981_);
lean_inc(v_synthPendingDepth_3980_);
lean_inc(v_defEqCtx_x3f_3979_);
lean_inc_ref(v_localInstances_3978_);
lean_inc_ref(v_lctx_3977_);
lean_inc(v_zetaDeltaSet_3976_);
v___x_3986_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
lean_ctor_set(v___x_3986_, 1, v_zetaDeltaSet_3976_);
lean_ctor_set(v___x_3986_, 2, v_lctx_3977_);
lean_ctor_set(v___x_3986_, 3, v_localInstances_3978_);
lean_ctor_set(v___x_3986_, 4, v_defEqCtx_x3f_3979_);
lean_ctor_set(v___x_3986_, 5, v_synthPendingDepth_3980_);
lean_ctor_set(v___x_3986_, 6, v_customCanUnfoldPredicate_x3f_3981_);
lean_ctor_set_uint8(v___x_3986_, sizeof(void*)*7, v_trackZetaDelta_3975_);
lean_ctor_set_uint8(v___x_3986_, sizeof(void*)*7 + 1, v_univApprox_3982_);
lean_ctor_set_uint8(v___x_3986_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3983_);
lean_ctor_set_uint8(v___x_3986_, sizeof(void*)*7 + 3, v_cacheInferType_3984_);
lean_inc(v___y_3961_);
lean_inc_ref(v___y_3960_);
lean_inc(v___y_3959_);
lean_inc(v_a_3969_);
v___x_3987_ = lean_whnf(v_a_3969_, v___x_3986_, v___y_3959_, v___y_3960_, v___y_3961_);
v___y_3905_ = v___y_3959_;
v___y_3906_ = v___y_3956_;
v___y_3907_ = v_a_3969_;
v___y_3908_ = v___y_3960_;
v___y_3909_ = v___y_3961_;
v___y_3910_ = v___y_3958_;
v___y_3911_ = v_isHEq_3957_;
v___y_3912_ = v___x_3987_;
goto v___jp_3904_;
}
else
{
lean_object* v___x_3988_; 
lean_inc(v___y_3961_);
lean_inc_ref(v___y_3960_);
lean_inc(v___y_3959_);
lean_inc_ref(v___y_3958_);
lean_inc(v_a_3969_);
v___x_3988_ = lean_whnf(v_a_3969_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
v___y_3905_ = v___y_3959_;
v___y_3906_ = v___y_3956_;
v___y_3907_ = v_a_3969_;
v___y_3908_ = v___y_3960_;
v___y_3909_ = v___y_3961_;
v___y_3910_ = v___y_3958_;
v___y_3911_ = v_isHEq_3957_;
v___y_3912_ = v___x_3988_;
goto v___jp_3904_;
}
}
else
{
lean_object* v_a_3989_; 
v_a_3989_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3968_, 1);
v___y_3893_ = v___y_3959_;
v___y_3894_ = v___y_3956_;
v___y_3895_ = v___y_3960_;
v___y_3896_ = v___y_3961_;
v___y_3897_ = v___y_3958_;
v___y_3898_ = v_isHEq_3957_;
v_a_3899_ = v_a_3989_;
goto v___jp_3892_;
}
}
else
{
v___y_3869_ = v___y_3956_;
v___y_3870_ = v_isHEq_3957_;
v___y_3871_ = v___y_3958_;
v___y_3872_ = v___y_3959_;
v___y_3873_ = v___y_3960_;
v___y_3874_ = v___y_3961_;
goto v___jp_3868_;
}
}
else
{
lean_dec(v_a_3965_);
v___y_3869_ = v___y_3956_;
v___y_3870_ = v_isHEq_3957_;
v___y_3871_ = v___y_3958_;
v___y_3872_ = v___y_3959_;
v___y_3873_ = v___y_3960_;
v___y_3874_ = v___y_3961_;
goto v___jp_3868_;
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_3990_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3964_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3964_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
v___y_3869_ = v___y_3956_;
v___y_3870_ = v_isHEq_3957_;
v___y_3871_ = v___y_3958_;
v___y_3872_ = v___y_3959_;
v___y_3873_ = v___y_3960_;
v___y_3874_ = v___y_3961_;
goto v___jp_3868_;
}
}
}
v___jp_3998_:
{
lean_object* v___x_4004_; 
lean_inc_ref(v___x_3867_);
v___x_4004_ = l_Lean_Meta_matchHEq_x3f(v___x_3867_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
if (lean_obj_tag(v_a_4005_) == 1)
{
lean_object* v_val_4006_; lean_object* v_snd_4007_; lean_object* v_snd_4008_; lean_object* v_fst_4009_; lean_object* v_fst_4010_; lean_object* v_fst_4011_; lean_object* v_snd_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4112_; 
v_val_4006_ = lean_ctor_get(v_a_4005_, 0);
lean_inc(v_val_4006_);
lean_dec_ref_known(v_a_4005_, 1);
v_snd_4007_ = lean_ctor_get(v_val_4006_, 1);
lean_inc(v_snd_4007_);
v_snd_4008_ = lean_ctor_get(v_snd_4007_, 1);
lean_inc(v_snd_4008_);
v_fst_4009_ = lean_ctor_get(v_val_4006_, 0);
lean_inc(v_fst_4009_);
lean_dec(v_val_4006_);
v_fst_4010_ = lean_ctor_get(v_snd_4007_, 0);
lean_inc(v_fst_4010_);
lean_dec(v_snd_4007_);
v_fst_4011_ = lean_ctor_get(v_snd_4008_, 0);
v_snd_4012_ = lean_ctor_get(v_snd_4008_, 1);
v_isSharedCheck_4112_ = !lean_is_exclusive(v_snd_4008_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4014_ = v_snd_4008_;
v_isShared_4015_ = v_isSharedCheck_4112_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_snd_4012_);
lean_inc(v_fst_4011_);
lean_dec(v_snd_4008_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4112_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4010_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4016_, 1);
if (lean_obj_tag(v_a_4017_) == 1)
{
lean_object* v_val_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4103_; 
v_val_4018_ = lean_ctor_get(v_a_4017_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v_a_4017_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4020_ = v_a_4017_;
v_isShared_4021_ = v_isSharedCheck_4103_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_val_4018_);
lean_dec(v_a_4017_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4103_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4012_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___x_4022_, 1);
if (lean_obj_tag(v_a_4023_) == 1)
{
lean_object* v_toConstantVal_4024_; lean_object* v_val_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4094_; 
v_toConstantVal_4024_ = lean_ctor_get(v_val_4018_, 0);
lean_inc_ref(v_toConstantVal_4024_);
lean_dec(v_val_4018_);
v_val_4025_ = lean_ctor_get(v_a_4023_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_a_4023_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4027_ = v_a_4023_;
v_isShared_4028_ = v_isSharedCheck_4094_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_val_4025_);
lean_dec(v_a_4023_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4094_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v_toConstantVal_4029_; lean_object* v_name_4030_; lean_object* v_name_4031_; uint8_t v___x_4032_; 
v_toConstantVal_4029_ = lean_ctor_get(v_val_4025_, 0);
lean_inc_ref(v_toConstantVal_4029_);
lean_dec(v_val_4025_);
v_name_4030_ = lean_ctor_get(v_toConstantVal_4024_, 0);
lean_inc(v_name_4030_);
lean_dec_ref(v_toConstantVal_4024_);
v_name_4031_ = lean_ctor_get(v_toConstantVal_4029_, 0);
lean_inc(v_name_4031_);
lean_dec_ref(v_toConstantVal_4029_);
v___x_4032_ = lean_name_eq(v_name_4030_, v_name_4031_);
lean_dec(v_name_4031_);
lean_dec(v_name_4030_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_Meta_isExprDefEq(v_fst_4009_, v_fst_4011_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; uint8_t v___x_4035_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
v___x_4035_ = lean_unbox(v_a_4034_);
lean_dec(v_a_4034_);
if (v___x_4035_ == 0)
{
lean_del_object(v___x_4027_);
lean_del_object(v___x_4020_);
lean_del_object(v___x_4014_);
v___y_3956_ = v_isEq_3999_;
v_isHEq_3957_ = v___x_3812_;
v___y_3958_ = v___y_4000_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
goto v___jp_3955_;
}
else
{
lean_object* v___x_4036_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec_ref(v_config_3801_);
lean_inc(v_mvarId_3802_);
v___x_4036_ = l_Lean_MVarId_getType(v_mvarId_3802_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v___x_4038_ = l_Lean_LocalDecl_toExpr(v_val_3833_);
v___x_4039_ = l_Lean_Meta_mkEqOfHEq(v___x_4038_, v___x_3812_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4041_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4039_, 1);
v___x_4041_ = l_Lean_Meta_mkNoConfusion(v_a_4037_, v_a_4040_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4043_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___x_4041_, 1);
v___x_4043_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3802_, v_a_4042_, v___y_4001_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4046_; 
lean_dec_ref_known(v___x_4043_, 1);
v___x_4044_ = lean_box(v___x_3812_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v___x_4044_);
v___x_4046_ = v___x_4027_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4044_);
v___x_4046_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4048_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 1, v___x_3837_);
lean_ctor_set(v___x_4014_, 0, v___x_4046_);
v___x_4048_ = v___x_4014_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v___x_3837_);
v___x_4048_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4050_; 
if (v_isShared_4021_ == 0)
{
lean_ctor_set_tag(v___x_4020_, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4048_);
v___x_4050_ = v___x_4020_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
v_a_3819_ = v___x_4050_;
goto v___jp_3818_;
}
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_del_object(v___x_4027_);
lean_del_object(v___x_4020_);
lean_del_object(v___x_4014_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_4054_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4043_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4043_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_del_object(v___x_4027_);
lean_del_object(v___x_4020_);
lean_del_object(v___x_4014_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4062_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4041_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4041_);
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
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec(v_a_4037_);
lean_del_object(v___x_4027_);
lean_del_object(v___x_4020_);
lean_del_object(v___x_4014_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4070_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4039_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4039_);
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
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_del_object(v___x_4027_);
lean_del_object(v___x_4020_);
lean_del_object(v___x_4014_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4078_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4036_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4036_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_del_object(v___x_4027_);
lean_del_object(v___x_4020_);
lean_del_object(v___x_4014_);
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4086_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4033_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4033_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
else
{
lean_del_object(v___x_4027_);
lean_del_object(v___x_4020_);
lean_del_object(v___x_4014_);
lean_dec(v_fst_4011_);
lean_dec(v_fst_4009_);
v___y_3956_ = v_isEq_3999_;
v_isHEq_3957_ = v___x_3812_;
v___y_3958_ = v___y_4000_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
goto v___jp_3955_;
}
}
}
else
{
lean_dec(v_a_4023_);
lean_del_object(v___x_4020_);
lean_dec(v_val_4018_);
lean_del_object(v___x_4014_);
lean_dec(v_fst_4011_);
lean_dec(v_fst_4009_);
v___y_3956_ = v_isEq_3999_;
v_isHEq_3957_ = v___x_3812_;
v___y_3958_ = v___y_4000_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
goto v___jp_3955_;
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_del_object(v___x_4020_);
lean_dec(v_val_4018_);
lean_del_object(v___x_4014_);
lean_dec(v_fst_4011_);
lean_dec(v_fst_4009_);
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4095_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4022_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4022_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
}
else
{
lean_dec(v_a_4017_);
lean_del_object(v___x_4014_);
lean_dec(v_snd_4012_);
lean_dec(v_fst_4011_);
lean_dec(v_fst_4009_);
v___y_3956_ = v_isEq_3999_;
v_isHEq_3957_ = v___x_3812_;
v___y_3958_ = v___y_4000_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
goto v___jp_3955_;
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_del_object(v___x_4014_);
lean_dec(v_snd_4012_);
lean_dec(v_fst_4011_);
lean_dec(v_fst_4009_);
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4104_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4016_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4016_);
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
}
else
{
lean_dec(v_a_4005_);
v___y_3956_ = v_isEq_3999_;
v_isHEq_3957_ = v___x_3866_;
v___y_3958_ = v___y_4000_;
v___y_3959_ = v___y_4001_;
v___y_3960_ = v___y_4002_;
v___y_3961_ = v___y_4003_;
goto v___jp_3955_;
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4113_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4004_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4004_);
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
v___jp_4121_:
{
lean_object* v___x_4126_; 
lean_inc_ref(v___x_3867_);
v___x_4126_ = l_Lean_Meta_matchEq_x3f(v___x_3867_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4126_, 1);
if (lean_obj_tag(v_a_4127_) == 1)
{
lean_object* v_val_4128_; lean_object* v_snd_4129_; lean_object* v_fst_4130_; lean_object* v_snd_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4210_; 
v_val_4128_ = lean_ctor_get(v_a_4127_, 0);
lean_inc(v_val_4128_);
lean_dec_ref_known(v_a_4127_, 1);
v_snd_4129_ = lean_ctor_get(v_val_4128_, 1);
lean_inc(v_snd_4129_);
lean_dec(v_val_4128_);
v_fst_4130_ = lean_ctor_get(v_snd_4129_, 0);
v_snd_4131_ = lean_ctor_get(v_snd_4129_, 1);
v_isSharedCheck_4210_ = !lean_is_exclusive(v_snd_4129_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4133_ = v_snd_4129_;
v_isShared_4134_ = v_isSharedCheck_4210_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_snd_4131_);
lean_inc(v_fst_4130_);
lean_dec(v_snd_4129_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4210_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4130_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
if (lean_obj_tag(v_a_4136_) == 1)
{
lean_object* v_val_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4201_; 
v_val_4137_ = lean_ctor_get(v_a_4136_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v_a_4136_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4139_ = v_a_4136_;
v_isShared_4140_ = v_isSharedCheck_4201_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_val_4137_);
lean_dec(v_a_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4201_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4131_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
if (lean_obj_tag(v_a_4142_) == 1)
{
lean_object* v_toConstantVal_4143_; lean_object* v_val_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4192_; 
v_toConstantVal_4143_ = lean_ctor_get(v_val_4137_, 0);
lean_inc_ref(v_toConstantVal_4143_);
lean_dec(v_val_4137_);
v_val_4144_ = lean_ctor_get(v_a_4142_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v_a_4142_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4146_ = v_a_4142_;
v_isShared_4147_ = v_isSharedCheck_4192_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_val_4144_);
lean_dec(v_a_4142_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4192_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v_toConstantVal_4148_; lean_object* v_name_4149_; lean_object* v_name_4150_; uint8_t v___x_4151_; 
v_toConstantVal_4148_ = lean_ctor_get(v_val_4144_, 0);
lean_inc_ref(v_toConstantVal_4148_);
lean_dec(v_val_4144_);
v_name_4149_ = lean_ctor_get(v_toConstantVal_4143_, 0);
lean_inc(v_name_4149_);
lean_dec_ref(v_toConstantVal_4143_);
v_name_4150_ = lean_ctor_get(v_toConstantVal_4148_, 0);
lean_inc(v_name_4150_);
lean_dec_ref(v_toConstantVal_4148_);
v___x_4151_ = lean_name_eq(v_name_4149_, v_name_4150_);
lean_dec(v_name_4150_);
lean_dec(v_name_4149_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec_ref(v_config_3801_);
lean_inc(v_mvarId_3802_);
v___x_4152_ = l_Lean_MVarId_getType(v_mvarId_3802_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
v___x_4154_ = l_Lean_LocalDecl_toExpr(v_val_3833_);
v___x_4155_ = l_Lean_Meta_mkNoConfusion(v_a_4153_, v___x_4154_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4157_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
v___x_4157_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3802_, v_a_4156_, v___y_4123_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4160_; 
lean_dec_ref_known(v___x_4157_, 1);
v___x_4158_ = lean_box(v___x_3812_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4158_);
v___x_4160_ = v___x_4146_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
lean_object* v___x_4162_; 
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 1, v___x_3837_);
lean_ctor_set(v___x_4133_, 0, v___x_4160_);
v___x_4162_ = v___x_4133_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v___x_3837_);
v___x_4162_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
lean_object* v___x_4164_; 
if (v_isShared_4140_ == 0)
{
lean_ctor_set_tag(v___x_4139_, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4162_);
v___x_4164_ = v___x_4139_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
v_a_3819_ = v___x_4164_;
goto v___jp_3818_;
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_del_object(v___x_4146_);
lean_del_object(v___x_4139_);
lean_del_object(v___x_4133_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_4168_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4157_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4157_);
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
lean_del_object(v___x_4146_);
lean_del_object(v___x_4139_);
lean_del_object(v___x_4133_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4176_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4155_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4155_);
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
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_del_object(v___x_4146_);
lean_del_object(v___x_4139_);
lean_del_object(v___x_4133_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4184_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4152_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4152_);
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
else
{
lean_del_object(v___x_4146_);
lean_del_object(v___x_4139_);
lean_del_object(v___x_4133_);
v_isEq_3999_ = v___x_3812_;
v___y_4000_ = v___y_4122_;
v___y_4001_ = v___y_4123_;
v___y_4002_ = v___y_4124_;
v___y_4003_ = v___y_4125_;
goto v___jp_3998_;
}
}
}
else
{
lean_dec(v_a_4142_);
lean_del_object(v___x_4139_);
lean_dec(v_val_4137_);
lean_del_object(v___x_4133_);
v_isEq_3999_ = v___x_3812_;
v___y_4000_ = v___y_4122_;
v___y_4001_ = v___y_4123_;
v___y_4002_ = v___y_4124_;
v___y_4003_ = v___y_4125_;
goto v___jp_3998_;
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
lean_del_object(v___x_4139_);
lean_dec(v_val_4137_);
lean_del_object(v___x_4133_);
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4193_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4141_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4141_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
}
else
{
lean_dec(v_a_4136_);
lean_del_object(v___x_4133_);
lean_dec(v_snd_4131_);
v_isEq_3999_ = v___x_3812_;
v___y_4000_ = v___y_4122_;
v___y_4001_ = v___y_4123_;
v___y_4002_ = v___y_4124_;
v___y_4003_ = v___y_4125_;
goto v___jp_3998_;
}
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_del_object(v___x_4133_);
lean_dec(v_snd_4131_);
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4202_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4135_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4135_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
}
else
{
lean_dec(v_a_4127_);
v_isEq_3999_ = v___x_3866_;
v___y_4000_ = v___y_4122_;
v___y_4001_ = v___y_4123_;
v___y_4002_ = v___y_4124_;
v___y_4003_ = v___y_4125_;
goto v___jp_3998_;
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4211_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4126_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4126_);
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
v___jp_4219_:
{
lean_object* v___x_4224_; 
lean_inc_ref(v___x_3867_);
v___x_4224_ = l_Lean_refutableHasNotBit_x3f(v___x_3867_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref_known(v___x_4224_, 1);
if (lean_obj_tag(v_a_4225_) == 1)
{
lean_object* v_val_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4266_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec_ref(v_config_3801_);
v_val_4226_ = lean_ctor_get(v_a_4225_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_a_4225_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4228_ = v_a_4225_;
v_isShared_4229_ = v_isSharedCheck_4266_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_val_4226_);
lean_dec(v_a_4225_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4266_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4230_; 
lean_inc(v_mvarId_3802_);
v___x_4230_ = l_Lean_MVarId_getType(v_mvarId_3802_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
lean_inc(v_a_4231_);
lean_dec_ref_known(v___x_4230_, 1);
v___x_4232_ = l_Lean_LocalDecl_toExpr(v_val_3833_);
v___x_4233_ = l_Lean_Meta_mkAbsurd(v_a_4231_, v_val_4226_, v___x_4232_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4233_, 1);
v___x_4235_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3802_, v_a_4234_, v___y_4221_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v___x_4236_; lean_object* v___x_4238_; 
lean_dec_ref_known(v___x_4235_, 1);
v___x_4236_ = lean_box(v___x_3812_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4236_);
v___x_4238_ = v___x_4228_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4236_);
v___x_4238_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
lean_ctor_set(v___x_4239_, 1, v___x_3837_);
v___x_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
v_a_3819_ = v___x_4240_;
goto v___jp_3818_;
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_del_object(v___x_4228_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_4242_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4235_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4235_);
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
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_del_object(v___x_4228_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4250_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4233_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4233_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
lean_del_object(v___x_4228_);
lean_dec(v_val_4226_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4258_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4230_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4230_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
}
else
{
lean_object* v___x_4267_; 
lean_dec(v_a_4225_);
lean_inc_ref(v___x_3867_);
v___x_4267_ = l_Lean_Meta_matchNe_x3f(v___x_3867_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4268_);
lean_dec_ref_known(v___x_4267_, 1);
if (lean_obj_tag(v_a_4268_) == 1)
{
lean_object* v_val_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4339_; 
v_val_4269_ = lean_ctor_get(v_a_4268_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_a_4268_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4271_ = v_a_4268_;
v_isShared_4272_ = v_isSharedCheck_4339_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_val_4269_);
lean_dec(v_a_4268_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4339_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v_snd_4273_; lean_object* v_fst_4274_; lean_object* v_snd_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4338_; 
v_snd_4273_ = lean_ctor_get(v_val_4269_, 1);
lean_inc(v_snd_4273_);
lean_dec(v_val_4269_);
v_fst_4274_ = lean_ctor_get(v_snd_4273_, 0);
v_snd_4275_ = lean_ctor_get(v_snd_4273_, 1);
v_isSharedCheck_4338_ = !lean_is_exclusive(v_snd_4273_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4277_ = v_snd_4273_;
v_isShared_4278_ = v_isSharedCheck_4338_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_snd_4275_);
lean_inc(v_fst_4274_);
lean_dec(v_snd_4273_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4338_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4279_; 
lean_inc(v_fst_4274_);
v___x_4279_ = l_Lean_Meta_isExprDefEq(v_fst_4274_, v_snd_4275_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; uint8_t v___x_4281_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v___x_4281_ = lean_unbox(v_a_4280_);
lean_dec(v_a_4280_);
if (v___x_4281_ == 0)
{
lean_del_object(v___x_4277_);
lean_dec(v_fst_4274_);
lean_del_object(v___x_4271_);
v___y_4122_ = v___y_4220_;
v___y_4123_ = v___y_4221_;
v___y_4124_ = v___y_4222_;
v___y_4125_ = v___y_4223_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4282_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec_ref(v_config_3801_);
lean_inc(v_mvarId_3802_);
v___x_4282_ = l_Lean_MVarId_getType(v_mvarId_3802_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4284_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___x_4284_ = l_Lean_Meta_mkEqRefl(v_fst_4274_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___x_4284_, 1);
v___x_4286_ = l_Lean_LocalDecl_toExpr(v_val_3833_);
v___x_4287_ = l_Lean_Meta_mkAbsurd(v_a_4283_, v_a_4285_, v___x_4286_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4287_, 1);
v___x_4289_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3802_, v_a_4288_, v___y_4221_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4292_; 
lean_dec_ref_known(v___x_4289_, 1);
v___x_4290_ = lean_box(v___x_3812_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4290_);
v___x_4292_ = v___x_4271_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4290_);
v___x_4292_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
lean_object* v___x_4294_; 
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 1, v___x_3837_);
lean_ctor_set(v___x_4277_, 0, v___x_4292_);
v___x_4294_ = v___x_4277_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4292_);
lean_ctor_set(v_reuseFailAlloc_4296_, 1, v___x_3837_);
v___x_4294_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
lean_object* v___x_4295_; 
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
v_a_3819_ = v___x_4295_;
goto v___jp_3818_;
}
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_del_object(v___x_4277_);
lean_del_object(v___x_4271_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_4298_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4289_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4289_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_del_object(v___x_4277_);
lean_del_object(v___x_4271_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4306_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4287_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4287_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec(v_a_4283_);
lean_del_object(v___x_4277_);
lean_del_object(v___x_4271_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4314_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4284_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4284_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_del_object(v___x_4277_);
lean_dec(v_fst_4274_);
lean_del_object(v___x_4271_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
v_a_4322_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4282_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4282_);
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
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
lean_del_object(v___x_4277_);
lean_dec(v_fst_4274_);
lean_del_object(v___x_4271_);
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4330_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4332_ = v___x_4279_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4279_);
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
}
}
else
{
lean_dec(v_a_4268_);
v___y_4122_ = v___y_4220_;
v___y_4123_ = v___y_4221_;
v___y_4124_ = v___y_4222_;
v___y_4125_ = v___y_4223_;
goto v___jp_4121_;
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4340_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4267_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4267_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_4348_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4224_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4224_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
else
{
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_3827_ = v___x_3838_;
goto v___jp_3826_;
}
v___jp_3839_:
{
uint8_t v_emptyType_3846_; 
v_emptyType_3846_ = lean_ctor_get_uint8(v_config_3801_, sizeof(void*)*1 + 1);
if (v_emptyType_3846_ == 0)
{
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_3827_ = v___x_3838_;
goto v___jp_3826_;
}
else
{
if (v___y_3840_ == 0)
{
if (v___y_3841_ == 0)
{
lean_object* v_searchFuel_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_searchFuel_3847_ = lean_ctor_get(v_config_3801_, 0);
v___x_3848_ = l_Lean_LocalDecl_fvarId(v_val_3833_);
lean_dec(v_val_3833_);
lean_inc(v_searchFuel_3847_);
lean_inc(v_mvarId_3802_);
v___x_3849_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3802_, v___x_3848_, v_searchFuel_3847_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; uint8_t v___x_3851_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v___x_3851_ = lean_unbox(v_a_3850_);
lean_dec(v_a_3850_);
if (v___x_3851_ == 0)
{
lean_del_object(v___x_3835_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_3827_ = v___x_3838_;
goto v___jp_3826_;
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v___x_3852_ = lean_box(v___x_3812_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3852_);
v___x_3854_ = v___x_3835_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
lean_ctor_set(v___x_3855_, 1, v___x_3837_);
v___x_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
v_a_3819_ = v___x_3856_;
goto v___jp_3818_;
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_del_object(v___x_3835_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
lean_dec(v_mvarId_3802_);
lean_dec_ref(v_config_3801_);
v_a_3858_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3849_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3849_);
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
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_3827_ = v___x_3838_;
goto v___jp_3826_;
}
}
else
{
lean_del_object(v___x_3835_);
lean_dec(v_val_3833_);
lean_del_object(v___x_3816_);
lean_dec(v_snd_3814_);
v_a_3827_ = v___x_3838_;
goto v___jp_3826_;
}
}
}
}
}
v___jp_3818_:
{
lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3820_, 0, v_a_3819_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v___x_3820_);
v___x_3822_ = v___x_3816_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_snd_3814_);
v___x_3822_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3823_; 
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
return v___x_3823_;
}
}
v___jp_3826_:
{
lean_object* v___x_3828_; size_t v___x_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3825_);
lean_ctor_set(v___x_3828_, 1, v_a_3827_);
v___x_3829_ = ((size_t)1ULL);
v___x_3830_ = lean_usize_add(v_i_3805_, v___x_3829_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3801_, v_mvarId_3802_, v_as_3803_, v_sz_3804_, v___x_3830_, v___x_3828_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
return v___x_3831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4429_, lean_object* v_mvarId_4430_, lean_object* v_as_4431_, lean_object* v_sz_4432_, lean_object* v_i_4433_, lean_object* v_b_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
size_t v_sz_boxed_4440_; size_t v_i_boxed_4441_; lean_object* v_res_4442_; 
v_sz_boxed_4440_ = lean_unbox_usize(v_sz_4432_);
lean_dec(v_sz_4432_);
v_i_boxed_4441_ = lean_unbox_usize(v_i_4433_);
lean_dec(v_i_4433_);
v_res_4442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4429_, v_mvarId_4430_, v_as_4431_, v_sz_boxed_4440_, v_i_boxed_4441_, v_b_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec_ref(v_as_4431_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4443_, lean_object* v_config_4444_, lean_object* v_mvarId_4445_, lean_object* v_n_4446_, lean_object* v_b_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
if (lean_obj_tag(v_n_4446_) == 0)
{
lean_object* v_cs_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; size_t v_sz_4456_; size_t v___x_4457_; lean_object* v___x_4458_; 
v_cs_4453_ = lean_ctor_get(v_n_4446_, 0);
v___x_4454_ = lean_box(0);
v___x_4455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4454_);
lean_ctor_set(v___x_4455_, 1, v_b_4447_);
v_sz_4456_ = lean_array_size(v_cs_4453_);
v___x_4457_ = ((size_t)0ULL);
v___x_4458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4443_, v_config_4444_, v_mvarId_4445_, v_cs_4453_, v_sz_4456_, v___x_4457_, v___x_4455_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4473_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4461_ = v___x_4458_;
v_isShared_4462_ = v_isSharedCheck_4473_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4458_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4473_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v_fst_4463_; 
v_fst_4463_ = lean_ctor_get(v_a_4459_, 0);
if (lean_obj_tag(v_fst_4463_) == 0)
{
lean_object* v_snd_4464_; lean_object* v___x_4465_; lean_object* v___x_4467_; 
v_snd_4464_ = lean_ctor_get(v_a_4459_, 1);
lean_inc(v_snd_4464_);
lean_dec(v_a_4459_);
v___x_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4465_, 0, v_snd_4464_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v___x_4465_);
v___x_4467_ = v___x_4461_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
else
{
lean_object* v_val_4469_; lean_object* v___x_4471_; 
lean_inc_ref(v_fst_4463_);
lean_dec(v_a_4459_);
v_val_4469_ = lean_ctor_get(v_fst_4463_, 0);
lean_inc(v_val_4469_);
lean_dec_ref_known(v_fst_4463_, 1);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v_val_4469_);
v___x_4471_ = v___x_4461_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_val_4469_);
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
v_a_4474_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4458_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4458_);
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
lean_object* v_vs_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; size_t v_sz_4485_; size_t v___x_4486_; lean_object* v___x_4487_; 
v_vs_4482_ = lean_ctor_get(v_n_4446_, 0);
v___x_4483_ = lean_box(0);
v___x_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
lean_ctor_set(v___x_4484_, 1, v_b_4447_);
v_sz_4485_ = lean_array_size(v_vs_4482_);
v___x_4486_ = ((size_t)0ULL);
v___x_4487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4444_, v_mvarId_4445_, v_vs_4482_, v_sz_4485_, v___x_4486_, v___x_4484_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4502_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4490_ = v___x_4487_;
v_isShared_4491_ = v_isSharedCheck_4502_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4502_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v_fst_4492_; 
v_fst_4492_ = lean_ctor_get(v_a_4488_, 0);
if (lean_obj_tag(v_fst_4492_) == 0)
{
lean_object* v_snd_4493_; lean_object* v___x_4494_; lean_object* v___x_4496_; 
v_snd_4493_ = lean_ctor_get(v_a_4488_, 1);
lean_inc(v_snd_4493_);
lean_dec(v_a_4488_);
v___x_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4494_, 0, v_snd_4493_);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v___x_4494_);
v___x_4496_ = v___x_4490_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4494_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
else
{
lean_object* v_val_4498_; lean_object* v___x_4500_; 
lean_inc_ref(v_fst_4492_);
lean_dec(v_a_4488_);
v_val_4498_ = lean_ctor_get(v_fst_4492_, 0);
lean_inc(v_val_4498_);
lean_dec_ref_known(v_fst_4492_, 1);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v_val_4498_);
v___x_4500_ = v___x_4490_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_val_4498_);
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
else
{
lean_object* v_a_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4510_; 
v_a_4503_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4505_ = v___x_4487_;
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_a_4503_);
lean_dec(v___x_4487_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
if (v_isShared_4506_ == 0)
{
v___x_4508_ = v___x_4505_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4511_, lean_object* v_config_4512_, lean_object* v_mvarId_4513_, lean_object* v_as_4514_, size_t v_sz_4515_, size_t v_i_4516_, lean_object* v_b_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
uint8_t v___x_4523_; 
v___x_4523_ = lean_usize_dec_lt(v_i_4516_, v_sz_4515_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; 
lean_dec(v_mvarId_4513_);
lean_dec_ref(v_config_4512_);
v___x_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4524_, 0, v_b_4517_);
return v___x_4524_;
}
else
{
lean_object* v_snd_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4559_; 
v_snd_4525_ = lean_ctor_get(v_b_4517_, 1);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_b_4517_);
if (v_isSharedCheck_4559_ == 0)
{
lean_object* v_unused_4560_; 
v_unused_4560_ = lean_ctor_get(v_b_4517_, 0);
lean_dec(v_unused_4560_);
v___x_4527_ = v_b_4517_;
v_isShared_4528_ = v_isSharedCheck_4559_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_snd_4525_);
lean_dec(v_b_4517_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4559_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4529_; lean_object* v_a_4530_; lean_object* v___x_4531_; 
v___x_4529_ = lean_box(0);
v_a_4530_ = lean_array_uget_borrowed(v_as_4514_, v_i_4516_);
lean_inc(v_snd_4525_);
lean_inc(v_mvarId_4513_);
lean_inc_ref(v_config_4512_);
v___x_4531_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4511_, v_config_4512_, v_mvarId_4513_, v_a_4530_, v_snd_4525_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4550_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4534_ = v___x_4531_;
v_isShared_4535_ = v_isSharedCheck_4550_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4531_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4550_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
if (lean_obj_tag(v_a_4532_) == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4538_; 
lean_dec(v_mvarId_4513_);
lean_dec_ref(v_config_4512_);
v___x_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4536_, 0, v_a_4532_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v___x_4536_);
v___x_4538_ = v___x_4527_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4536_);
lean_ctor_set(v_reuseFailAlloc_4542_, 1, v_snd_4525_);
v___x_4538_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4540_; 
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v___x_4538_);
v___x_4540_ = v___x_4534_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4538_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; 
lean_del_object(v___x_4534_);
lean_dec(v_snd_4525_);
v_a_4543_ = lean_ctor_get(v_a_4532_, 0);
lean_inc(v_a_4543_);
lean_dec_ref_known(v_a_4532_, 1);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 1, v_a_4543_);
lean_ctor_set(v___x_4527_, 0, v___x_4529_);
v___x_4545_ = v___x_4527_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4529_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v_a_4543_);
v___x_4545_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
size_t v___x_4546_; size_t v___x_4547_; 
v___x_4546_ = ((size_t)1ULL);
v___x_4547_ = lean_usize_add(v_i_4516_, v___x_4546_);
v_i_4516_ = v___x_4547_;
v_b_4517_ = v___x_4545_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_del_object(v___x_4527_);
lean_dec(v_snd_4525_);
lean_dec(v_mvarId_4513_);
lean_dec_ref(v_config_4512_);
v_a_4551_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4531_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4531_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4561_, lean_object* v_config_4562_, lean_object* v_mvarId_4563_, lean_object* v_as_4564_, lean_object* v_sz_4565_, lean_object* v_i_4566_, lean_object* v_b_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
size_t v_sz_boxed_4573_; size_t v_i_boxed_4574_; lean_object* v_res_4575_; 
v_sz_boxed_4573_ = lean_unbox_usize(v_sz_4565_);
lean_dec(v_sz_4565_);
v_i_boxed_4574_ = lean_unbox_usize(v_i_4566_);
lean_dec(v_i_4566_);
v_res_4575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4561_, v_config_4562_, v_mvarId_4563_, v_as_4564_, v_sz_boxed_4573_, v_i_boxed_4574_, v_b_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec_ref(v_as_4564_);
lean_dec_ref(v_init_4561_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4576_, lean_object* v_config_4577_, lean_object* v_mvarId_4578_, lean_object* v_n_4579_, lean_object* v_b_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4576_, v_config_4577_, v_mvarId_4578_, v_n_4579_, v_b_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec_ref(v_n_4579_);
lean_dec_ref(v_init_4576_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4587_, lean_object* v_mvarId_4588_, lean_object* v_t_4589_, lean_object* v_init_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v_root_4596_; lean_object* v_tail_4597_; lean_object* v___x_4598_; 
v_root_4596_ = lean_ctor_get(v_t_4589_, 0);
v_tail_4597_ = lean_ctor_get(v_t_4589_, 1);
lean_inc(v_mvarId_4588_);
lean_inc_ref(v_config_4587_);
lean_inc_ref(v_init_4590_);
v___x_4598_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4590_, v_config_4587_, v_mvarId_4588_, v_root_4596_, v_init_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
lean_dec_ref(v_init_4590_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4635_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4635_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4635_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
if (lean_obj_tag(v_a_4599_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; 
lean_dec(v_mvarId_4588_);
lean_dec_ref(v_config_4587_);
v_a_4603_ = lean_ctor_get(v_a_4599_, 0);
lean_inc(v_a_4603_);
lean_dec_ref_known(v_a_4599_, 1);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v_a_4603_);
v___x_4605_ = v___x_4601_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4603_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; size_t v_sz_4610_; size_t v___x_4611_; lean_object* v___x_4612_; 
lean_del_object(v___x_4601_);
v_a_4607_ = lean_ctor_get(v_a_4599_, 0);
lean_inc(v_a_4607_);
lean_dec_ref_known(v_a_4599_, 1);
v___x_4608_ = lean_box(0);
v___x_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
lean_ctor_set(v___x_4609_, 1, v_a_4607_);
v_sz_4610_ = lean_array_size(v_tail_4597_);
v___x_4611_ = ((size_t)0ULL);
v___x_4612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4587_, v_mvarId_4588_, v_tail_4597_, v_sz_4610_, v___x_4611_, v___x_4609_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4626_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4626_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4626_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v_fst_4617_; 
v_fst_4617_ = lean_ctor_get(v_a_4613_, 0);
if (lean_obj_tag(v_fst_4617_) == 0)
{
lean_object* v_snd_4618_; lean_object* v___x_4620_; 
v_snd_4618_ = lean_ctor_get(v_a_4613_, 1);
lean_inc(v_snd_4618_);
lean_dec(v_a_4613_);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v_snd_4618_);
v___x_4620_ = v___x_4615_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_snd_4618_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
else
{
lean_object* v_val_4622_; lean_object* v___x_4624_; 
lean_inc_ref(v_fst_4617_);
lean_dec(v_a_4613_);
v_val_4622_ = lean_ctor_get(v_fst_4617_, 0);
lean_inc(v_val_4622_);
lean_dec_ref_known(v_fst_4617_, 1);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v_val_4622_);
v___x_4624_ = v___x_4615_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_val_4622_);
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
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
v_a_4627_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4612_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4612_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_mvarId_4588_);
lean_dec_ref(v_config_4587_);
v_a_4636_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4598_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4598_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4644_, lean_object* v_mvarId_4645_, lean_object* v_t_4646_, lean_object* v_init_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4644_, v_mvarId_4645_, v_t_4646_, v_init_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec_ref(v_t_4646_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4654_, lean_object* v___x_4655_, lean_object* v_config_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v___x_4662_; 
lean_inc(v_mvarId_4654_);
v___x_4662_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4654_, v___x_4655_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v___x_4663_; 
lean_dec_ref_known(v___x_4662_, 1);
lean_inc(v_mvarId_4654_);
v___x_4663_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4654_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4697_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4697_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4697_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
uint8_t v___x_4668_; 
v___x_4668_ = lean_unbox(v_a_4664_);
if (v___x_4668_ == 0)
{
lean_object* v_lctx_4669_; lean_object* v_decls_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
lean_del_object(v___x_4666_);
v_lctx_4669_ = lean_ctor_get(v___y_4657_, 2);
v_decls_4670_ = lean_ctor_get(v_lctx_4669_, 1);
v___x_4671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4672_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4656_, v_mvarId_4654_, v_decls_4670_, v___x_4671_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4685_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4675_ = v___x_4672_;
v_isShared_4676_ = v_isSharedCheck_4685_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4672_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4685_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v_fst_4677_; 
v_fst_4677_ = lean_ctor_get(v_a_4673_, 0);
lean_inc(v_fst_4677_);
lean_dec(v_a_4673_);
if (lean_obj_tag(v_fst_4677_) == 0)
{
lean_object* v___x_4679_; 
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v_a_4664_);
v___x_4679_ = v___x_4675_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4664_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
else
{
lean_object* v_val_4681_; lean_object* v___x_4683_; 
lean_dec(v_a_4664_);
v_val_4681_ = lean_ctor_get(v_fst_4677_, 0);
lean_inc(v_val_4681_);
lean_dec_ref_known(v_fst_4677_, 1);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v_val_4681_);
v___x_4683_ = v___x_4675_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_val_4681_);
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
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec(v_a_4664_);
v_a_4686_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4672_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4672_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
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
lean_object* v___x_4695_; 
lean_dec_ref(v_config_4656_);
lean_dec(v_mvarId_4654_);
if (v_isShared_4667_ == 0)
{
v___x_4695_ = v___x_4666_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4664_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
else
{
lean_dec_ref(v_config_4656_);
lean_dec(v_mvarId_4654_);
return v___x_4663_;
}
}
else
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
lean_dec_ref(v_config_4656_);
lean_dec(v_mvarId_4654_);
v_a_4698_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4662_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4662_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4706_, lean_object* v___x_4707_, lean_object* v_config_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4706_, v___x_4707_, v_config_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4717_, lean_object* v_config_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
lean_object* v___x_4724_; lean_object* v___f_4725_; lean_object* v___x_4726_; 
v___x_4724_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4717_);
v___f_4725_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4725_, 0, v_mvarId_4717_);
lean_closure_set(v___f_4725_, 1, v___x_4724_);
lean_closure_set(v___f_4725_, 2, v_config_4718_);
v___x_4726_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4717_, v___f_4725_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4727_, lean_object* v_config_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Lean_MVarId_contradictionCore(v_mvarId_4727_, v_config_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4735_, lean_object* v_config_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
lean_object* v___x_4742_; 
lean_inc(v_mvarId_4735_);
v___x_4742_ = l_Lean_MVarId_contradictionCore(v_mvarId_4735_, v_config_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_);
if (lean_obj_tag(v___x_4742_) == 0)
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4755_; 
v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4745_ = v___x_4742_;
v_isShared_4746_ = v_isSharedCheck_4755_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4742_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4755_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
uint8_t v___x_4747_; 
v___x_4747_ = lean_unbox(v_a_4743_);
lean_dec(v_a_4743_);
if (v___x_4747_ == 0)
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
lean_del_object(v___x_4745_);
v___x_4748_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4749_ = lean_box(0);
v___x_4750_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4748_, v_mvarId_4735_, v___x_4749_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_);
return v___x_4750_;
}
else
{
lean_object* v___x_4751_; lean_object* v___x_4753_; 
lean_dec(v_mvarId_4735_);
v___x_4751_ = lean_box(0);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 0, v___x_4751_);
v___x_4753_ = v___x_4745_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4751_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec(v_mvarId_4735_);
v_a_4756_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4742_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4742_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4764_, lean_object* v_config_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_Lean_MVarId_contradiction(v_mvarId_4764_, v_config_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4834_; uint8_t v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4834_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4835_ = 0;
v___x_4836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4837_ = l_Lean_registerTraceClass(v___x_4834_, v___x_4835_, v___x_4836_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4839_;
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
