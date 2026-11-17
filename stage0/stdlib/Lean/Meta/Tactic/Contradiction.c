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
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_mkGenDiseqMask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkGenDiseqMask___closed__0 = (const lean_object*)&l_Lean_Meta_mkGenDiseqMask___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.Tactic.Contradiction"};
static const lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.mkGenDiseqFalseProof\?"};
static const lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "assertion violation: isGenDiseq type\n  "};
static const lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_processGenDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_processGenDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_sz_boxed_673_; size_t v___x_15997__boxed_674_; uint8_t v___x_15999__boxed_675_; lean_object* v_res_676_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_663_);
lean_dec(v_sz_663_);
v___x_15997__boxed_674_ = lean_unbox_usize(v___x_664_);
lean_dec(v___x_664_);
v___x_15999__boxed_675_ = lean_unbox(v___x_666_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_660_, v_mvarId_661_, v_fields_662_, v_sz_boxed_673_, v___x_15997__boxed_674_, v___x_665_, v___x_15999__boxed_675_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
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
uint8_t v___x_16119__boxed_879_; uint8_t v___x_16122__boxed_880_; lean_object* v_res_881_; 
v___x_16119__boxed_879_ = lean_unbox(v___x_869_);
v___x_16122__boxed_880_ = lean_unbox(v___x_872_);
v_res_881_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_866_, v_fvarId_867_, v___x_868_, v___x_16119__boxed_879_, v___x_870_, v_val_871_, v___x_16122__boxed_880_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
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
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
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
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0(v_x_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1168_, v_x_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1176_, lean_object* v_mvarId_1177_, lean_object* v_x_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1177_, v_x_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_mvarId_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1185_, v_mvarId_1186_, v_x_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1194_, lean_object* v_fuel_1195_, lean_object* v_fvarId_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1223_, lean_object* v_fuel_1224_, lean_object* v_fvarId_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1223_, v_fuel_1224_, v_fvarId_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1232_, lean_object* v___f_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
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
v___x_1242_ = l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0(v___f_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1243_, lean_object* v___f_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1243_, v___f_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1251_, lean_object* v_fvarId_1252_, lean_object* v_fuel_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; 
lean_inc(v_fvarId_1252_);
lean_inc(v_mvarId_1251_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1259_, 0, v_mvarId_1251_);
lean_closure_set(v___f_1259_, 1, v_fuel_1253_);
lean_closure_set(v___f_1259_, 2, v_fvarId_1252_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1260_, 0, v_fvarId_1252_);
lean_closure_set(v___f_1260_, 1, v___f_1259_);
v___x_1261_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1251_, v___f_1260_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1262_, lean_object* v_fvarId_1263_, lean_object* v_fuel_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_1262_, v_fvarId_1263_, v_fuel_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0(lean_object* v_msg_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___f_1307_; lean_object* v___x_3742__overap_1308_; lean_object* v___x_1309_; 
v___f_1307_ = ((lean_object*)(l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0___closed__0));
v___x_3742__overap_1308_ = lean_panic_fn_borrowed(v___f_1307_, v_msg_1301_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
v___x_1309_ = lean_apply_5(v___x_3742__overap_1308_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, lean_box(0));
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0___boxed(lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0(v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(lean_object* v_e_1317_, lean_object* v___y_1318_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg___boxed(lean_object* v_e_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v_e_1342_, v___y_1343_);
lean_dec(v___y_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2(lean_object* v_e_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v_e_1346_, v___y_1348_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___boxed(lean_object* v_e_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2(v_e_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg(lean_object* v_k_1360_, uint8_t v_allowLevelAssignments_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg___boxed(lean_object* v_k_1384_, lean_object* v_allowLevelAssignments_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1391_; lean_object* v_res_1392_; 
v_allowLevelAssignments_boxed_1391_ = lean_unbox(v_allowLevelAssignments_1385_);
v_res_1392_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg(v_k_1384_, v_allowLevelAssignments_boxed_1391_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3(lean_object* v_00_u03b1_1393_, lean_object* v_k_1394_, uint8_t v_allowLevelAssignments_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg(v_k_1394_, v_allowLevelAssignments_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_k_1403_, lean_object* v_allowLevelAssignments_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1410_; lean_object* v_res_1411_; 
v_allowLevelAssignments_boxed_1410_ = lean_unbox(v_allowLevelAssignments_1404_);
v_res_1411_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3(v_00_u03b1_1402_, v_k_1403_, v_allowLevelAssignments_boxed_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1(lean_object* v_as_1414_, size_t v_sz_1415_, size_t v_i_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
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
v___x_1545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___closed__0));
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
v___x_1479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___closed__0));
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___boxed(lean_object* v_as_1594_, lean_object* v_sz_1595_, lean_object* v_i_1596_, lean_object* v_b_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
size_t v_sz_boxed_1603_; size_t v_i_boxed_1604_; lean_object* v_res_1605_; 
v_sz_boxed_1603_ = lean_unbox_usize(v_sz_1595_);
lean_dec(v_sz_1595_);
v_i_boxed_1604_ = lean_unbox_usize(v_i_1596_);
lean_dec(v_i_1596_);
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1(v_as_1594_, v_sz_boxed_1603_, v_i_boxed_1604_, v_b_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v_as_1594_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0(lean_object* v_type_1606_, uint8_t v___x_1607_, lean_object* v_h_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
lean_inc_ref(v_type_1606_);
v___x_1614_ = l_Lean_Meta_forallMetaTelescope(v_type_1606_, v___x_1607_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v_fst_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1680_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v_fst_1616_ = lean_ctor_get(v_a_1615_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_a_1615_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; 
v_unused_1681_ = lean_ctor_get(v_a_1615_, 1);
lean_dec(v_unused_1681_);
v___x_1618_ = v_a_1615_;
v_isShared_1619_ = v_isSharedCheck_1680_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_fst_1616_);
lean_dec(v_a_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1680_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1620_ = l_Lean_Meta_mkGenDiseqMask(v_type_1606_);
lean_dec_ref(v_type_1606_);
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
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1623_);
v___x_1626_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
size_t v_sz_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v_sz_1627_ = lean_array_size(v_fst_1616_);
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1(v_fst_1616_, v_sz_1627_, v___x_1628_, v___x_1626_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1670_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1670_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1670_;
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
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1665_; 
lean_del_object(v___x_1632_);
v___x_1635_ = l_Lean_mkAppN(v_h_1608_, v_fst_1616_);
lean_dec(v_fst_1616_);
v___x_1636_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_1635_, v___y_1610_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1665_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1665_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; 
lean_inc(v_a_1637_);
v___x_1641_ = l_Lean_Meta_hasAssignableMVar(v_a_1637_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1656_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1656_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1656_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_unbox(v_a_1642_);
lean_dec(v_a_1642_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1648_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set_tag(v___x_1639_, 1);
v___x_1648_ = v___x_1639_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1637_);
v___x_1648_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1648_);
v___x_1650_ = v___x_1644_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
else
{
lean_object* v___x_1654_; 
lean_del_object(v___x_1639_);
lean_dec(v_a_1637_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1624_);
v___x_1654_ = v___x_1644_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1624_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1639_);
lean_dec(v_a_1637_);
v_a_1657_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1641_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1641_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
else
{
lean_object* v_val_1666_; lean_object* v___x_1668_; 
lean_dec(v_fst_1616_);
lean_dec_ref(v_h_1608_);
v_val_1666_ = lean_ctor_get(v_fst_1634_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v_fst_1634_, 1);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v_val_1666_);
v___x_1668_ = v___x_1632_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_val_1666_);
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
lean_dec(v_fst_1616_);
lean_dec_ref(v_h_1608_);
v_a_1671_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1629_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1629_);
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
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v_h_1608_);
lean_dec_ref(v_type_1606_);
v_a_1682_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1614_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1614_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0___boxed(lean_object* v_type_1690_, lean_object* v___x_1691_, lean_object* v_h_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v___x_5460__boxed_1698_; lean_object* v_res_1699_; 
v___x_5460__boxed_1698_ = lean_unbox(v___x_1691_);
v_res_1699_ = l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0(v_type_1690_, v___x_5460__boxed_1698_, v_h_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
return v_res_1699_;
}
}
static lean_object* _init_l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1703_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__2));
v___x_1704_ = lean_unsigned_to_nat(2u);
v___x_1705_ = lean_unsigned_to_nat(122u);
v___x_1706_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__1));
v___x_1707_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__0));
v___x_1708_ = l_mkPanicMessageWithDecl(v___x_1707_, v___x_1706_, v___x_1705_, v___x_1704_, v___x_1703_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f(lean_object* v_h_1709_, lean_object* v_type_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_type_1710_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec_ref(v_type_1710_);
lean_dec_ref(v_h_1709_);
v___x_1717_ = lean_obj_once(&l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3, &l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3_once, _init_l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3);
v___x_1718_ = l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0(v___x_1717_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
return v___x_1718_;
}
else
{
uint8_t v___x_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1719_ = 0;
v___x_1720_ = lean_box(v___x_1719_);
v___f_1721_ = lean_alloc_closure((void*)(l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1721_, 0, v_type_1710_);
lean_closure_set(v___f_1721_, 1, v___x_1720_);
lean_closure_set(v___f_1721_, 2, v_h_1709_);
v___x_1722_ = 0;
v___x_1723_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg(v___f_1721_, v___x_1722_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___boxed(lean_object* v_h_1724_, lean_object* v_type_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_Meta_mkGenDiseqFalseProof_x3f(v_h_1724_, v_type_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_processGenDiseq(lean_object* v_mvarId_1732_, lean_object* v_localDecl_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_inc_ref(v_localDecl_1733_);
v___x_1739_ = l_Lean_LocalDecl_toExpr(v_localDecl_1733_);
v___x_1740_ = l_Lean_LocalDecl_type(v_localDecl_1733_);
lean_dec_ref(v_localDecl_1733_);
v___x_1741_ = l_Lean_Meta_mkGenDiseqFalseProof_x3f(v___x_1739_, v___x_1740_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1783_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1783_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1783_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
if (lean_obj_tag(v_a_1742_) == 1)
{
lean_object* v_val_1746_; lean_object* v___x_1747_; 
lean_del_object(v___x_1744_);
v_val_1746_ = lean_ctor_get(v_a_1742_, 0);
lean_inc(v_val_1746_);
lean_dec_ref_known(v_a_1742_, 1);
lean_inc(v_mvarId_1732_);
v___x_1747_ = l_Lean_MVarId_getType(v_mvarId_1732_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = l_Lean_Meta_mkFalseElim(v_a_1748_, v_val_1746_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1760_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1732_, v_a_1750_, v_a_1735_);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v___x_1751_, 0);
lean_dec(v_unused_1761_);
v___x_1753_ = v___x_1751_;
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
else
{
lean_dec(v___x_1751_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1755_ = 1;
v___x_1756_ = lean_box(v___x_1755_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1756_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_mvarId_1732_);
v_a_1762_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1749_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1749_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_val_1746_);
lean_dec(v_mvarId_1732_);
v_a_1770_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1747_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1747_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
uint8_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
lean_dec(v_a_1742_);
lean_dec(v_mvarId_1732_);
v___x_1778_ = 0;
v___x_1779_ = lean_box(v___x_1778_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1779_);
v___x_1781_ = v___x_1744_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec(v_mvarId_1732_);
v_a_1784_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1741_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1741_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1792_, lean_object* v_localDecl_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Meta_processGenDiseq(v_mvarId_1792_, v_localDecl_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1799_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(lean_object* v_x_1800_, lean_object* v_x_1801_){
_start:
{
if (lean_obj_tag(v_x_1800_) == 0)
{
if (lean_obj_tag(v_x_1801_) == 0)
{
uint8_t v___x_1802_; 
v___x_1802_ = 1;
return v___x_1802_;
}
else
{
uint8_t v___x_1803_; 
v___x_1803_ = 0;
return v___x_1803_;
}
}
else
{
if (lean_obj_tag(v_x_1801_) == 0)
{
uint8_t v___x_1804_; 
v___x_1804_ = 0;
return v___x_1804_;
}
else
{
lean_object* v_val_1805_; uint8_t v___x_1806_; 
v_val_1805_ = lean_ctor_get(v_x_1801_, 0);
v___x_1806_ = lean_unbox(v_val_1805_);
if (v___x_1806_ == 0)
{
lean_object* v_val_1807_; uint8_t v___x_1808_; 
v_val_1807_ = lean_ctor_get(v_x_1800_, 0);
v___x_1808_ = lean_unbox(v_val_1807_);
if (v___x_1808_ == 0)
{
uint8_t v___x_1809_; 
v___x_1809_ = 1;
return v___x_1809_;
}
else
{
uint8_t v___x_1810_; 
v___x_1810_ = lean_unbox(v_val_1805_);
return v___x_1810_;
}
}
else
{
lean_object* v_val_1811_; uint8_t v___x_1812_; 
v_val_1811_ = lean_ctor_get(v_x_1800_, 0);
v___x_1812_ = lean_unbox(v_val_1811_);
return v___x_1812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0___boxed(lean_object* v_x_1813_, lean_object* v_x_1814_){
_start:
{
uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(v_x_1813_, v_x_1814_);
lean_dec(v_x_1814_);
lean_dec(v_x_1813_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0(lean_object* v_lhs_1820_, lean_object* v_rhs_1821_, lean_object* v_mvarId_1822_, lean_object* v_h_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
lean_inc_ref(v_rhs_1821_);
lean_inc_ref(v_lhs_1820_);
v___x_1829_ = l_Lean_Meta_floatLitValuesEq_x3f(v_lhs_1820_, v_rhs_1821_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1892_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1892_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1892_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
uint8_t v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1834_ = 0;
v___x_1835_ = ((lean_object*)(l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___closed__0));
v___x_1836_ = l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(v_a_1830_, v___x_1835_);
lean_dec(v_a_1830_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec_ref(v_h_1823_);
lean_dec(v_mvarId_1822_);
lean_dec_ref(v_rhs_1821_);
lean_dec_ref(v_lhs_1820_);
v___x_1837_ = lean_box(v___x_1834_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1837_);
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
lean_object* v___x_1841_; 
lean_del_object(v___x_1832_);
v___x_1841_ = l_Lean_Meta_mkEq(v_lhs_1820_, v_rhs_1821_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = l_Lean_mkNot(v_a_1842_);
v___x_1844_ = l_Lean_Meta_mkDecideProof(v___x_1843_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
lean_inc(v_mvarId_1822_);
v___x_1846_ = l_Lean_MVarId_getType(v_mvarId_1822_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = l_Lean_Meta_mkAbsurd(v_a_1847_, v_h_1823_, v_a_1845_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1858_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1822_, v_a_1849_, v___y_1825_);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v___x_1850_, 0);
lean_dec(v_unused_1859_);
v___x_1852_ = v___x_1850_;
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1850_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_box(v___x_1836_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_mvarId_1822_);
v_a_1860_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1848_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1848_);
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
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v_a_1845_);
lean_dec_ref(v_h_1823_);
lean_dec(v_mvarId_1822_);
v_a_1868_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1846_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1846_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_h_1823_);
lean_dec(v_mvarId_1822_);
v_a_1876_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1844_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1844_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v_h_1823_);
lean_dec(v_mvarId_1822_);
v_a_1884_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1841_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1841_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v_h_1823_);
lean_dec(v_mvarId_1822_);
lean_dec_ref(v_rhs_1821_);
lean_dec_ref(v_lhs_1820_);
v_a_1893_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1829_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1829_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___boxed(lean_object* v_lhs_1901_, lean_object* v_rhs_1902_, lean_object* v_mvarId_1903_, lean_object* v_h_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_MVarId_closeIfDistinctFloatLits___lam__0(v_lhs_1901_, v_rhs_1902_, v_mvarId_1903_, v_h_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits(lean_object* v_mvarId_1911_, lean_object* v_h_1912_, lean_object* v_lhs_1913_, lean_object* v_rhs_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___f_1920_; lean_object* v___x_1921_; 
lean_inc(v_mvarId_1911_);
v___f_1920_ = lean_alloc_closure((void*)(l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1920_, 0, v_lhs_1913_);
lean_closure_set(v___f_1920_, 1, v_rhs_1914_);
lean_closure_set(v___f_1920_, 2, v_mvarId_1911_);
lean_closure_set(v___f_1920_, 3, v_h_1912_);
v___x_1921_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1911_, v___f_1920_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___boxed(lean_object* v_mvarId_1922_, lean_object* v_h_1923_, lean_object* v_lhs_1924_, lean_object* v_rhs_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_MVarId_closeIfDistinctFloatLits(v_mvarId_1922_, v_h_1923_, v_lhs_1924_, v_rhs_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
return v_res_1931_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_box(0);
v___x_1944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1945_ = l_Lean_mkConst(v___x_1944_, v___x_1943_);
return v___x_1945_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1946_; lean_object* v_dummy_1947_; 
v___x_1946_ = lean_box(0);
v_dummy_1947_ = l_Lean_Expr_sort___override(v___x_1946_);
return v_dummy_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1948_, lean_object* v_mvarId_1949_, lean_object* v_as_1950_, size_t v_sz_1951_, size_t v_i_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
uint8_t v___x_1959_; 
v___x_1959_ = lean_usize_dec_lt(v_i_1952_, v_sz_1951_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v_b_1953_);
return v___x_1960_;
}
else
{
lean_object* v_snd_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2542_; 
v_snd_1961_ = lean_ctor_get(v_b_1953_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_b_1953_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v_b_1953_, 0);
lean_dec(v_unused_2543_);
v___x_1963_ = v_b_1953_;
v_isShared_1964_ = v_isSharedCheck_2542_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_snd_1961_);
lean_dec(v_b_1953_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2542_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_a_1966_; lean_object* v___x_1972_; lean_object* v_a_1974_; lean_object* v_a_1979_; 
v___x_1972_ = lean_box(0);
v_a_1979_ = lean_array_uget(v_as_1950_, v_i_1952_);
if (lean_obj_tag(v_a_1979_) == 0)
{
lean_del_object(v___x_1963_);
v_a_1974_ = v_snd_1961_;
goto v___jp_1973_;
}
else
{
lean_object* v_val_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2541_; 
v_val_1980_ = lean_ctor_get(v_a_1979_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_1982_ = v_a_1979_;
v_isShared_1983_ = v_isSharedCheck_2541_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_val_1980_);
lean_dec(v_a_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2541_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___y_1987_; uint8_t v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; uint8_t v___x_2012_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2012_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1980_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; uint8_t v___y_2015_; uint8_t v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; uint8_t v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; uint8_t v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v_a_2044_; uint8_t v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; uint8_t v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; uint8_t v___y_2094_; uint8_t v_isHEq_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; uint8_t v_isEq_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___x_2478_; 
v___x_2013_ = l_Lean_LocalDecl_type(v_val_1980_);
lean_inc_ref(v___x_2013_);
v___x_2478_ = l_Lean_Meta_matchNot_x3f(v___x_2013_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
if (lean_obj_tag(v_a_2479_) == 1)
{
lean_object* v_val_2480_; lean_object* v___x_2481_; 
v_val_2480_ = lean_ctor_get(v_a_2479_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v_a_2479_, 1);
v___x_2481_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2480_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
if (lean_obj_tag(v_a_2482_) == 1)
{
lean_object* v_val_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_config_1948_);
v_val_2483_ = lean_ctor_get(v_a_2482_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_a_2482_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2485_ = v_a_2482_;
v_isShared_2486_ = v_isSharedCheck_2524_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_val_2483_);
lean_dec(v_a_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2524_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; 
lean_inc(v_mvarId_1949_);
v___x_2487_ = l_Lean_MVarId_getType(v_mvarId_1949_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2489_ = l_Lean_LocalDecl_toExpr(v_val_1980_);
v___x_2490_ = l_Lean_mkFVar(v_val_2483_);
v___x_2491_ = l_Lean_Expr_app___override(v___x_2489_, v___x_2490_);
v___x_2492_ = l_Lean_Meta_mkFalseElim(v_a_2488_, v___x_2491_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v___x_2494_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1949_, v_a_2493_, v___y_1955_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
lean_dec_ref_known(v___x_2494_, 1);
v___x_2495_ = lean_box(v___x_1959_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2495_);
v___x_2497_ = v___x_2485_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
lean_ctor_set(v___x_2498_, 1, v___x_1984_);
v_a_1966_ = v___x_2498_;
goto v___jp_1965_;
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_del_object(v___x_2485_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
v_a_2500_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2494_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2494_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_del_object(v___x_2485_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2508_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2492_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2492_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_del_object(v___x_2485_);
lean_dec(v_val_2483_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2516_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2487_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2487_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
else
{
lean_dec(v_a_2482_);
v___y_2344_ = v___y_1954_;
v___y_2345_ = v___y_1955_;
v___y_2346_ = v___y_1956_;
v___y_2347_ = v___y_1957_;
goto v___jp_2343_;
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2525_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2481_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2481_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_dec(v_a_2479_);
v___y_2344_ = v___y_1954_;
v___y_2345_ = v___y_1955_;
v___y_2346_ = v___y_1956_;
v___y_2347_ = v___y_1957_;
goto v___jp_2343_;
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2533_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2478_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2478_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
v___jp_2014_:
{
uint8_t v_genDiseq_2021_; 
v_genDiseq_2021_ = lean_ctor_get_uint8(v_config_1948_, sizeof(void*)*1 + 2);
if (v_genDiseq_2021_ == 0)
{
lean_dec_ref(v___x_2013_);
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2020_;
goto v___jp_1986_;
}
else
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2013_);
lean_dec_ref(v___x_2013_);
if (v___x_2022_ == 0)
{
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2020_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2023_; 
lean_inc(v_val_1980_);
lean_inc(v_mvarId_1949_);
v___x_2023_ = l_Lean_Meta_processGenDiseq(v_mvarId_1949_, v_val_1980_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; uint8_t v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = lean_unbox(v_a_2024_);
lean_dec(v_a_2024_);
if (v___x_2025_ == 0)
{
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
v___y_1992_ = v___y_2020_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v___x_2026_ = lean_box(v___x_1959_);
v___x_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_1984_);
v_a_1966_ = v___x_2028_;
goto v___jp_1965_;
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2029_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2023_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2023_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
v___jp_2037_:
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_Exception_isInterrupt(v_a_2044_);
if (v___x_2045_ == 0)
{
uint8_t v___x_2046_; 
lean_inc_ref(v_a_2044_);
v___x_2046_ = l_Lean_Exception_isRuntime(v_a_2044_);
if (v___x_2046_ == 0)
{
lean_dec_ref(v_a_2044_);
v___y_2015_ = v___y_2038_;
v___y_2016_ = v___y_2041_;
v___y_2017_ = v___y_2040_;
v___y_2018_ = v___y_2042_;
v___y_2019_ = v___y_2039_;
v___y_2020_ = v___y_2043_;
goto v___jp_2014_;
}
else
{
lean_object* v___x_2047_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_a_2044_);
return v___x_2047_;
}
}
else
{
lean_object* v___x_2048_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_a_2044_);
return v___x_2048_;
}
}
v___jp_2049_:
{
if (lean_obj_tag(v___y_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_a_2058_ = lean_ctor_get(v___y_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___y_2057_, 1);
v___x_2059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2060_ = l_Lean_Expr_isConstOf(v_a_2058_, v___x_2059_);
lean_dec(v_a_2058_);
if (v___x_2060_ == 0)
{
lean_dec_ref(v___y_2055_);
v___y_2015_ = v___y_2050_;
v___y_2016_ = v___y_2053_;
v___y_2017_ = v___y_2052_;
v___y_2018_ = v___y_2054_;
v___y_2019_ = v___y_2051_;
v___y_2020_ = v___y_2056_;
goto v___jp_2014_;
}
else
{
lean_object* v___x_2061_; 
lean_inc_ref(v___y_2055_);
v___x_2061_ = l_Lean_Meta_mkEqRefl(v___y_2055_, v___y_2052_, v___y_2054_, v___y_2051_, v___y_2056_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; lean_object* v_dummy_2064_; lean_object* v_nargs_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2064_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2065_ = l_Lean_Expr_getAppNumArgs(v___y_2055_);
lean_inc(v_nargs_2065_);
v___x_2066_ = lean_mk_array(v_nargs_2065_, v_dummy_2064_);
v___x_2067_ = lean_unsigned_to_nat(1u);
v___x_2068_ = lean_nat_sub(v_nargs_2065_, v___x_2067_);
lean_dec(v_nargs_2065_);
v___x_2069_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2055_, v___x_2066_, v___x_2068_);
v___x_2070_ = lean_array_push(v___x_2069_, v_a_2062_);
v___x_2071_ = l_Lean_mkAppN(v___x_2063_, v___x_2070_);
lean_dec_ref(v___x_2070_);
lean_inc(v_mvarId_1949_);
v___x_2072_ = l_Lean_MVarId_getType(v_mvarId_1949_, v___y_2052_, v___y_2054_, v___y_2051_, v___y_2056_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
lean_inc(v_val_1980_);
v___x_2074_ = l_Lean_LocalDecl_toExpr(v_val_1980_);
v___x_2075_ = l_Lean_Meta_mkAbsurd(v_a_2073_, v___x_2074_, v___x_2071_, v___y_2052_, v___y_2054_, v___y_2051_, v___y_2056_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
lean_inc(v_mvarId_1949_);
v___x_2077_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1949_, v_a_2076_, v___y_2054_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v___x_2077_, 0);
lean_dec(v_unused_2087_);
v___x_2079_ = v___x_2077_;
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
else
{
lean_dec(v___x_2077_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_box(v___x_1959_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 1);
lean_ctor_set(v___x_2079_, 0, v___x_2081_);
v___x_2083_ = v___x_2079_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_1984_);
v_a_1966_ = v___x_2084_;
goto v___jp_1965_;
}
}
}
else
{
lean_object* v_a_2088_; 
v_a_2088_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2077_, 1);
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2051_;
v___y_2040_ = v___y_2052_;
v___y_2041_ = v___y_2053_;
v___y_2042_ = v___y_2054_;
v___y_2043_ = v___y_2056_;
v_a_2044_ = v_a_2088_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2089_; 
v_a_2089_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2075_, 1);
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2051_;
v___y_2040_ = v___y_2052_;
v___y_2041_ = v___y_2053_;
v___y_2042_ = v___y_2054_;
v___y_2043_ = v___y_2056_;
v_a_2044_ = v_a_2089_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2090_; 
lean_dec_ref(v___x_2071_);
v_a_2090_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2072_, 1);
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2051_;
v___y_2040_ = v___y_2052_;
v___y_2041_ = v___y_2053_;
v___y_2042_ = v___y_2054_;
v___y_2043_ = v___y_2056_;
v_a_2044_ = v_a_2090_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2091_; 
lean_dec_ref(v___y_2055_);
v_a_2091_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2061_, 1);
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2051_;
v___y_2040_ = v___y_2052_;
v___y_2041_ = v___y_2053_;
v___y_2042_ = v___y_2054_;
v___y_2043_ = v___y_2056_;
v_a_2044_ = v_a_2091_;
goto v___jp_2037_;
}
}
}
else
{
lean_object* v_a_2092_; 
lean_dec_ref(v___y_2055_);
v_a_2092_ = lean_ctor_get(v___y_2057_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___y_2057_, 1);
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2051_;
v___y_2040_ = v___y_2052_;
v___y_2041_ = v___y_2053_;
v___y_2042_ = v___y_2054_;
v___y_2043_ = v___y_2056_;
v_a_2044_ = v_a_2092_;
goto v___jp_2037_;
}
}
v___jp_2093_:
{
uint8_t v_useDecide_2100_; 
v_useDecide_2100_ = lean_ctor_get_uint8(v_config_1948_, sizeof(void*)*1);
if (v_useDecide_2100_ == 0)
{
v___y_2015_ = v_isHEq_2095_;
v___y_2016_ = v___y_2094_;
v___y_2017_ = v___y_2096_;
v___y_2018_ = v___y_2097_;
v___y_2019_ = v___y_2098_;
v___y_2020_ = v___y_2099_;
goto v___jp_2014_;
}
else
{
uint8_t v___x_2101_; 
v___x_2101_ = l_Lean_Expr_hasFVar(v___x_2013_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; 
lean_inc_ref(v___x_2013_);
v___x_2102_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_2013_, v___y_2097_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; uint8_t v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = l_Lean_Expr_hasMVar(v_a_2103_);
if (v___x_2104_ == 0)
{
uint8_t v___x_2105_; 
v___x_2105_ = l_Lean_Expr_hasFVar(v_a_2103_);
lean_dec(v_a_2103_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_inc_ref(v___x_2013_);
v___x_2106_ = l_Lean_Meta_mkDecide(v___x_2013_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; uint8_t v_transparency_2109_; uint8_t v___x_2110_; uint8_t v___x_2111_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = l_Lean_Meta_Context_config(v___y_2096_);
v_transparency_2109_ = lean_ctor_get_uint8(v___x_2108_, 9);
lean_dec_ref(v___x_2108_);
v___x_2110_ = 1;
v___x_2111_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2109_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v_keyedConfig_2112_; uint8_t v_trackZetaDelta_2113_; lean_object* v_zetaDeltaSet_2114_; lean_object* v_lctx_2115_; lean_object* v_localInstances_2116_; lean_object* v_defEqCtx_x3f_2117_; lean_object* v_synthPendingDepth_2118_; lean_object* v_customCanUnfoldPredicate_x3f_2119_; uint8_t v_univApprox_2120_; uint8_t v_inTypeClassResolution_2121_; uint8_t v_cacheInferType_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_keyedConfig_2112_ = lean_ctor_get(v___y_2096_, 0);
v_trackZetaDelta_2113_ = lean_ctor_get_uint8(v___y_2096_, sizeof(void*)*7);
v_zetaDeltaSet_2114_ = lean_ctor_get(v___y_2096_, 1);
v_lctx_2115_ = lean_ctor_get(v___y_2096_, 2);
v_localInstances_2116_ = lean_ctor_get(v___y_2096_, 3);
v_defEqCtx_x3f_2117_ = lean_ctor_get(v___y_2096_, 4);
v_synthPendingDepth_2118_ = lean_ctor_get(v___y_2096_, 5);
v_customCanUnfoldPredicate_x3f_2119_ = lean_ctor_get(v___y_2096_, 6);
v_univApprox_2120_ = lean_ctor_get_uint8(v___y_2096_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2121_ = lean_ctor_get_uint8(v___y_2096_, sizeof(void*)*7 + 2);
v_cacheInferType_2122_ = lean_ctor_get_uint8(v___y_2096_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2112_);
v___x_2123_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2110_, v_keyedConfig_2112_);
lean_inc(v_customCanUnfoldPredicate_x3f_2119_);
lean_inc(v_synthPendingDepth_2118_);
lean_inc(v_defEqCtx_x3f_2117_);
lean_inc_ref(v_localInstances_2116_);
lean_inc_ref(v_lctx_2115_);
lean_inc(v_zetaDeltaSet_2114_);
v___x_2124_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v_zetaDeltaSet_2114_);
lean_ctor_set(v___x_2124_, 2, v_lctx_2115_);
lean_ctor_set(v___x_2124_, 3, v_localInstances_2116_);
lean_ctor_set(v___x_2124_, 4, v_defEqCtx_x3f_2117_);
lean_ctor_set(v___x_2124_, 5, v_synthPendingDepth_2118_);
lean_ctor_set(v___x_2124_, 6, v_customCanUnfoldPredicate_x3f_2119_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*7, v_trackZetaDelta_2113_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*7 + 1, v_univApprox_2120_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2121_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*7 + 3, v_cacheInferType_2122_);
lean_inc(v___y_2099_);
lean_inc_ref(v___y_2098_);
lean_inc(v___y_2097_);
lean_inc(v_a_2107_);
v___x_2125_ = lean_whnf(v_a_2107_, v___x_2124_, v___y_2097_, v___y_2098_, v___y_2099_);
v___y_2050_ = v_isHEq_2095_;
v___y_2051_ = v___y_2098_;
v___y_2052_ = v___y_2096_;
v___y_2053_ = v___y_2094_;
v___y_2054_ = v___y_2097_;
v___y_2055_ = v_a_2107_;
v___y_2056_ = v___y_2099_;
v___y_2057_ = v___x_2125_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2126_; 
lean_inc(v___y_2099_);
lean_inc_ref(v___y_2098_);
lean_inc(v___y_2097_);
lean_inc_ref(v___y_2096_);
lean_inc(v_a_2107_);
v___x_2126_ = lean_whnf(v_a_2107_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
v___y_2050_ = v_isHEq_2095_;
v___y_2051_ = v___y_2098_;
v___y_2052_ = v___y_2096_;
v___y_2053_ = v___y_2094_;
v___y_2054_ = v___y_2097_;
v___y_2055_ = v_a_2107_;
v___y_2056_ = v___y_2099_;
v___y_2057_ = v___x_2126_;
goto v___jp_2049_;
}
}
else
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2106_, 1);
v___y_2038_ = v_isHEq_2095_;
v___y_2039_ = v___y_2098_;
v___y_2040_ = v___y_2096_;
v___y_2041_ = v___y_2094_;
v___y_2042_ = v___y_2097_;
v___y_2043_ = v___y_2099_;
v_a_2044_ = v_a_2127_;
goto v___jp_2037_;
}
}
else
{
v___y_2015_ = v_isHEq_2095_;
v___y_2016_ = v___y_2094_;
v___y_2017_ = v___y_2096_;
v___y_2018_ = v___y_2097_;
v___y_2019_ = v___y_2098_;
v___y_2020_ = v___y_2099_;
goto v___jp_2014_;
}
}
else
{
lean_dec(v_a_2103_);
v___y_2015_ = v_isHEq_2095_;
v___y_2016_ = v___y_2094_;
v___y_2017_ = v___y_2096_;
v___y_2018_ = v___y_2097_;
v___y_2019_ = v___y_2098_;
v___y_2020_ = v___y_2099_;
goto v___jp_2014_;
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2128_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2102_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2102_);
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
v___y_2015_ = v_isHEq_2095_;
v___y_2016_ = v___y_2094_;
v___y_2017_ = v___y_2096_;
v___y_2018_ = v___y_2097_;
v___y_2019_ = v___y_2098_;
v___y_2020_ = v___y_2099_;
goto v___jp_2014_;
}
}
}
v___jp_2136_:
{
lean_object* v___x_2142_; 
lean_inc_ref(v___x_2013_);
v___x_2142_ = l_Lean_Meta_matchHEq_x3f(v___x_2013_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
if (lean_obj_tag(v_a_2143_) == 1)
{
lean_object* v_val_2144_; lean_object* v_snd_2145_; lean_object* v_snd_2146_; lean_object* v_fst_2147_; lean_object* v_fst_2148_; lean_object* v_fst_2149_; lean_object* v_snd_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2243_; 
v_val_2144_ = lean_ctor_get(v_a_2143_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v_a_2143_, 1);
v_snd_2145_ = lean_ctor_get(v_val_2144_, 1);
lean_inc(v_snd_2145_);
v_snd_2146_ = lean_ctor_get(v_snd_2145_, 1);
lean_inc(v_snd_2146_);
v_fst_2147_ = lean_ctor_get(v_val_2144_, 0);
lean_inc(v_fst_2147_);
lean_dec(v_val_2144_);
v_fst_2148_ = lean_ctor_get(v_snd_2145_, 0);
lean_inc(v_fst_2148_);
lean_dec(v_snd_2145_);
v_fst_2149_ = lean_ctor_get(v_snd_2146_, 0);
v_snd_2150_ = lean_ctor_get(v_snd_2146_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_snd_2146_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2152_ = v_snd_2146_;
v_isShared_2153_ = v_isSharedCheck_2243_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_snd_2150_);
lean_inc(v_fst_2149_);
lean_dec(v_snd_2146_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2243_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2148_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
if (lean_obj_tag(v_a_2155_) == 1)
{
lean_object* v_val_2156_; lean_object* v___x_2157_; 
v_val_2156_ = lean_ctor_get(v_a_2155_, 0);
lean_inc(v_val_2156_);
lean_dec_ref_known(v_a_2155_, 1);
v___x_2157_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2150_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
if (lean_obj_tag(v_a_2158_) == 1)
{
lean_object* v_toConstantVal_2159_; lean_object* v_val_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2226_; 
v_toConstantVal_2159_ = lean_ctor_get(v_val_2156_, 0);
lean_inc_ref(v_toConstantVal_2159_);
lean_dec(v_val_2156_);
v_val_2160_ = lean_ctor_get(v_a_2158_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_a_2158_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2162_ = v_a_2158_;
v_isShared_2163_ = v_isSharedCheck_2226_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_val_2160_);
lean_dec(v_a_2158_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2226_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_toConstantVal_2164_; lean_object* v_name_2165_; lean_object* v_name_2166_; uint8_t v___x_2167_; 
v_toConstantVal_2164_ = lean_ctor_get(v_val_2160_, 0);
lean_inc_ref(v_toConstantVal_2164_);
lean_dec(v_val_2160_);
v_name_2165_ = lean_ctor_get(v_toConstantVal_2159_, 0);
lean_inc(v_name_2165_);
lean_dec_ref(v_toConstantVal_2159_);
v_name_2166_ = lean_ctor_get(v_toConstantVal_2164_, 0);
lean_inc(v_name_2166_);
lean_dec_ref(v_toConstantVal_2164_);
v___x_2167_ = lean_name_eq(v_name_2165_, v_name_2166_);
lean_dec(v_name_2166_);
lean_dec(v_name_2165_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_Meta_isExprDefEq(v_fst_2147_, v_fst_2149_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; uint8_t v___x_2170_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2170_ = lean_unbox(v_a_2169_);
lean_dec(v_a_2169_);
if (v___x_2170_ == 0)
{
lean_del_object(v___x_2162_);
lean_del_object(v___x_2152_);
v___y_2094_ = v_isEq_2137_;
v_isHEq_2095_ = v___x_1959_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
v___y_2099_ = v___y_2141_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2171_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_config_1948_);
lean_inc(v_mvarId_1949_);
v___x_2171_ = l_Lean_MVarId_getType(v_mvarId_1949_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = l_Lean_LocalDecl_toExpr(v_val_1980_);
v___x_2174_ = l_Lean_Meta_mkEqOfHEq(v___x_2173_, v___x_1959_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2176_ = l_Lean_Meta_mkNoConfusion(v_a_2172_, v_a_2175_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1949_, v_a_2177_, v___y_2139_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
lean_dec_ref_known(v___x_2178_, 1);
v___x_2179_ = lean_box(v___x_1959_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2179_);
v___x_2181_ = v___x_2162_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2183_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v___x_1984_);
lean_ctor_set(v___x_2152_, 0, v___x_2181_);
v___x_2183_ = v___x_2152_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v___x_1984_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
v_a_1966_ = v___x_2183_;
goto v___jp_1965_;
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_del_object(v___x_2162_);
lean_del_object(v___x_2152_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
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
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_del_object(v___x_2162_);
lean_del_object(v___x_2152_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2194_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2176_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2176_);
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
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_a_2172_);
lean_del_object(v___x_2162_);
lean_del_object(v___x_2152_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2202_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2174_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2174_);
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
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_del_object(v___x_2162_);
lean_del_object(v___x_2152_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2210_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2171_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2171_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_del_object(v___x_2162_);
lean_del_object(v___x_2152_);
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2218_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2168_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2168_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_del_object(v___x_2162_);
lean_del_object(v___x_2152_);
lean_dec(v_fst_2149_);
lean_dec(v_fst_2147_);
v___y_2094_ = v_isEq_2137_;
v_isHEq_2095_ = v___x_1959_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
v___y_2099_ = v___y_2141_;
goto v___jp_2093_;
}
}
}
else
{
lean_dec(v_a_2158_);
lean_dec(v_val_2156_);
lean_del_object(v___x_2152_);
lean_dec(v_fst_2149_);
lean_dec(v_fst_2147_);
v___y_2094_ = v_isEq_2137_;
v_isHEq_2095_ = v___x_1959_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
v___y_2099_ = v___y_2141_;
goto v___jp_2093_;
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_val_2156_);
lean_del_object(v___x_2152_);
lean_dec(v_fst_2149_);
lean_dec(v_fst_2147_);
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2227_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2157_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2157_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_dec(v_a_2155_);
lean_del_object(v___x_2152_);
lean_dec(v_snd_2150_);
lean_dec(v_fst_2149_);
lean_dec(v_fst_2147_);
v___y_2094_ = v_isEq_2137_;
v_isHEq_2095_ = v___x_1959_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
v___y_2099_ = v___y_2141_;
goto v___jp_2093_;
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_del_object(v___x_2152_);
lean_dec(v_snd_2150_);
lean_dec(v_fst_2149_);
lean_dec(v_fst_2147_);
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2235_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2154_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2154_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
else
{
lean_dec(v_a_2143_);
v___y_2094_ = v_isEq_2137_;
v_isHEq_2095_ = v___x_2012_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
v___y_2099_ = v___y_2141_;
goto v___jp_2093_;
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2244_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2142_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2142_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
v___jp_2252_:
{
lean_object* v___x_2257_; 
lean_inc_ref(v___x_2013_);
v___x_2257_ = l_Lean_Meta_matchEq_x3f(v___x_2013_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
if (lean_obj_tag(v_a_2258_) == 1)
{
lean_object* v_val_2259_; lean_object* v_snd_2260_; lean_object* v_fst_2261_; lean_object* v_snd_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2334_; 
v_val_2259_ = lean_ctor_get(v_a_2258_, 0);
lean_inc(v_val_2259_);
lean_dec_ref_known(v_a_2258_, 1);
v_snd_2260_ = lean_ctor_get(v_val_2259_, 1);
lean_inc(v_snd_2260_);
lean_dec(v_val_2259_);
v_fst_2261_ = lean_ctor_get(v_snd_2260_, 0);
v_snd_2262_ = lean_ctor_get(v_snd_2260_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_snd_2260_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2264_ = v_snd_2260_;
v_isShared_2265_ = v_isSharedCheck_2334_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_snd_2262_);
lean_inc(v_fst_2261_);
lean_dec(v_snd_2260_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2334_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2261_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
if (lean_obj_tag(v_a_2267_) == 1)
{
lean_object* v_val_2268_; lean_object* v___x_2269_; 
v_val_2268_ = lean_ctor_get(v_a_2267_, 0);
lean_inc(v_val_2268_);
lean_dec_ref_known(v_a_2267_, 1);
v___x_2269_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2262_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
if (lean_obj_tag(v_a_2270_) == 1)
{
lean_object* v_toConstantVal_2271_; lean_object* v_val_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2317_; 
v_toConstantVal_2271_ = lean_ctor_get(v_val_2268_, 0);
lean_inc_ref(v_toConstantVal_2271_);
lean_dec(v_val_2268_);
v_val_2272_ = lean_ctor_get(v_a_2270_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_a_2270_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2274_ = v_a_2270_;
v_isShared_2275_ = v_isSharedCheck_2317_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_val_2272_);
lean_dec(v_a_2270_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2317_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v_toConstantVal_2276_; lean_object* v_name_2277_; lean_object* v_name_2278_; uint8_t v___x_2279_; 
v_toConstantVal_2276_ = lean_ctor_get(v_val_2272_, 0);
lean_inc_ref(v_toConstantVal_2276_);
lean_dec(v_val_2272_);
v_name_2277_ = lean_ctor_get(v_toConstantVal_2271_, 0);
lean_inc(v_name_2277_);
lean_dec_ref(v_toConstantVal_2271_);
v_name_2278_ = lean_ctor_get(v_toConstantVal_2276_, 0);
lean_inc(v_name_2278_);
lean_dec_ref(v_toConstantVal_2276_);
v___x_2279_ = lean_name_eq(v_name_2277_, v_name_2278_);
lean_dec(v_name_2278_);
lean_dec(v_name_2277_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_config_1948_);
lean_inc(v_mvarId_1949_);
v___x_2280_ = l_Lean_MVarId_getType(v_mvarId_1949_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = l_Lean_LocalDecl_toExpr(v_val_1980_);
v___x_2283_ = l_Lean_Meta_mkNoConfusion(v_a_2281_, v___x_2282_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2285_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v___x_2285_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1949_, v_a_2284_, v___y_2254_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
lean_dec_ref_known(v___x_2285_, 1);
v___x_2286_ = lean_box(v___x_1959_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2286_);
v___x_2288_ = v___x_2274_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v___x_1984_);
lean_ctor_set(v___x_2264_, 0, v___x_2288_);
v___x_2290_ = v___x_2264_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v___x_1984_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
v_a_1966_ = v___x_2290_;
goto v___jp_1965_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_del_object(v___x_2274_);
lean_del_object(v___x_2264_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
v_a_2293_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2285_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2285_);
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
lean_del_object(v___x_2274_);
lean_del_object(v___x_2264_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2301_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2283_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2283_);
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
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_del_object(v___x_2274_);
lean_del_object(v___x_2264_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2309_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2280_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2280_);
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
else
{
lean_del_object(v___x_2274_);
lean_del_object(v___x_2264_);
v_isEq_2137_ = v___x_1959_;
v___y_2138_ = v___y_2253_;
v___y_2139_ = v___y_2254_;
v___y_2140_ = v___y_2255_;
v___y_2141_ = v___y_2256_;
goto v___jp_2136_;
}
}
}
else
{
lean_dec(v_a_2270_);
lean_dec(v_val_2268_);
lean_del_object(v___x_2264_);
v_isEq_2137_ = v___x_1959_;
v___y_2138_ = v___y_2253_;
v___y_2139_ = v___y_2254_;
v___y_2140_ = v___y_2255_;
v___y_2141_ = v___y_2256_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_val_2268_);
lean_del_object(v___x_2264_);
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2318_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2269_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2269_);
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
else
{
lean_dec(v_a_2267_);
lean_del_object(v___x_2264_);
lean_dec(v_snd_2262_);
v_isEq_2137_ = v___x_1959_;
v___y_2138_ = v___y_2253_;
v___y_2139_ = v___y_2254_;
v___y_2140_ = v___y_2255_;
v___y_2141_ = v___y_2256_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_del_object(v___x_2264_);
lean_dec(v_snd_2262_);
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2326_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2266_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2266_);
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
lean_dec(v_a_2258_);
v_isEq_2137_ = v___x_2012_;
v___y_2138_ = v___y_2253_;
v___y_2139_ = v___y_2254_;
v___y_2140_ = v___y_2255_;
v___y_2141_ = v___y_2256_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2335_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2257_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2257_);
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
v___jp_2343_:
{
lean_object* v___x_2348_; 
lean_inc_ref(v___x_2013_);
v___x_2348_ = l_Lean_refutableHasNotBit_x3f(v___x_2013_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
if (lean_obj_tag(v_a_2349_) == 1)
{
lean_object* v_val_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_config_1948_);
v_val_2350_ = lean_ctor_get(v_a_2349_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_a_2349_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2352_ = v_a_2349_;
v_isShared_2353_ = v_isSharedCheck_2389_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_val_2350_);
lean_dec(v_a_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2389_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; 
lean_inc(v_mvarId_1949_);
v___x_2354_ = l_Lean_MVarId_getType(v_mvarId_1949_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = l_Lean_LocalDecl_toExpr(v_val_1980_);
v___x_2357_ = l_Lean_Meta_mkAbsurd(v_a_2355_, v_val_2350_, v___x_2356_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2359_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v___x_2359_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1949_, v_a_2358_, v___y_2345_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_dec_ref_known(v___x_2359_, 1);
v___x_2360_ = lean_box(v___x_1959_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2360_);
v___x_2362_ = v___x_2352_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___x_1984_);
v_a_1966_ = v___x_2363_;
goto v___jp_1965_;
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_del_object(v___x_2352_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
v_a_2365_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2359_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2359_);
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
lean_del_object(v___x_2352_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2373_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2357_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2357_);
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
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_del_object(v___x_2352_);
lean_dec(v_val_2350_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2381_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2354_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2354_);
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
lean_object* v___x_2390_; 
lean_dec(v_a_2349_);
lean_inc_ref(v___x_2013_);
v___x_2390_ = l_Lean_Meta_matchNe_x3f(v___x_2013_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
if (lean_obj_tag(v_a_2391_) == 1)
{
lean_object* v_val_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2461_; 
v_val_2392_ = lean_ctor_get(v_a_2391_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_a_2391_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2394_ = v_a_2391_;
v_isShared_2395_ = v_isSharedCheck_2461_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_val_2392_);
lean_dec(v_a_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2461_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_snd_2396_; lean_object* v_fst_2397_; lean_object* v_snd_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2460_; 
v_snd_2396_ = lean_ctor_get(v_val_2392_, 1);
lean_inc(v_snd_2396_);
lean_dec(v_val_2392_);
v_fst_2397_ = lean_ctor_get(v_snd_2396_, 0);
v_snd_2398_ = lean_ctor_get(v_snd_2396_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_snd_2396_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2400_ = v_snd_2396_;
v_isShared_2401_ = v_isSharedCheck_2460_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_snd_2398_);
lean_inc(v_fst_2397_);
lean_dec(v_snd_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2460_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; 
lean_inc(v_fst_2397_);
v___x_2402_ = l_Lean_Meta_isExprDefEq(v_fst_2397_, v_snd_2398_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; uint8_t v___x_2404_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = lean_unbox(v_a_2403_);
lean_dec(v_a_2403_);
if (v___x_2404_ == 0)
{
lean_del_object(v___x_2400_);
lean_dec(v_fst_2397_);
lean_del_object(v___x_2394_);
v___y_2253_ = v___y_2344_;
v___y_2254_ = v___y_2345_;
v___y_2255_ = v___y_2346_;
v___y_2256_ = v___y_2347_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2405_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_config_1948_);
lean_inc(v_mvarId_1949_);
v___x_2405_ = l_Lean_MVarId_getType(v_mvarId_1949_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = l_Lean_Meta_mkEqRefl(v_fst_2397_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = l_Lean_LocalDecl_toExpr(v_val_1980_);
v___x_2410_ = l_Lean_Meta_mkAbsurd(v_a_2406_, v_a_2408_, v___x_2409_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2412_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
v___x_2412_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1949_, v_a_2411_, v___y_2345_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
lean_dec_ref_known(v___x_2412_, 1);
v___x_2413_ = lean_box(v___x_1959_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2413_);
v___x_2415_ = v___x_2394_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 1, v___x_1984_);
lean_ctor_set(v___x_2400_, 0, v___x_2415_);
v___x_2417_ = v___x_2400_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___x_1984_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
v_a_1966_ = v___x_2417_;
goto v___jp_1965_;
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_del_object(v___x_2400_);
lean_del_object(v___x_2394_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
v_a_2420_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2412_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2412_);
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
lean_del_object(v___x_2400_);
lean_del_object(v___x_2394_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2428_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2410_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2410_);
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
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_a_2406_);
lean_del_object(v___x_2400_);
lean_del_object(v___x_2394_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2436_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2407_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2407_);
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
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_del_object(v___x_2400_);
lean_dec(v_fst_2397_);
lean_del_object(v___x_2394_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
v_a_2444_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2405_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2405_);
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
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_del_object(v___x_2400_);
lean_dec(v_fst_2397_);
lean_del_object(v___x_2394_);
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2452_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2402_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2402_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2391_);
v___y_2253_ = v___y_2344_;
v___y_2254_ = v___y_2345_;
v___y_2255_ = v___y_2346_;
v___y_2256_ = v___y_2347_;
goto v___jp_2252_;
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2462_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2390_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2390_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v___x_2013_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2470_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2348_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2348_);
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
}
else
{
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
v_a_1974_ = v___x_1985_;
goto v___jp_1973_;
}
v___jp_1986_:
{
uint8_t v_emptyType_1993_; 
v_emptyType_1993_ = lean_ctor_get_uint8(v_config_1948_, sizeof(void*)*1 + 1);
if (v_emptyType_1993_ == 0)
{
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
v_a_1974_ = v___x_1985_;
goto v___jp_1973_;
}
else
{
if (v___y_1988_ == 0)
{
if (v___y_1987_ == 0)
{
lean_object* v_searchFuel_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v_searchFuel_1994_ = lean_ctor_get(v_config_1948_, 0);
v___x_1995_ = l_Lean_LocalDecl_fvarId(v_val_1980_);
lean_dec(v_val_1980_);
lean_inc(v_searchFuel_1994_);
lean_inc(v_mvarId_1949_);
v___x_1996_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_1949_, v___x_1995_, v_searchFuel_1994_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; uint8_t v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = lean_unbox(v_a_1997_);
lean_dec(v_a_1997_);
if (v___x_1998_ == 0)
{
lean_del_object(v___x_1982_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
v_a_1974_ = v___x_1985_;
goto v___jp_1973_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v___x_1999_ = lean_box(v___x_1959_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1999_);
v___x_2001_ = v___x_1982_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___x_1984_);
v_a_1966_ = v___x_2002_;
goto v___jp_1965_;
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_del_object(v___x_1982_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
lean_dec(v_mvarId_1949_);
lean_dec_ref(v_config_1948_);
v_a_2004_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1996_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1996_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
v_a_1974_ = v___x_1985_;
goto v___jp_1973_;
}
}
else
{
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_del_object(v___x_1963_);
lean_dec(v_snd_1961_);
v_a_1974_ = v___x_1985_;
goto v___jp_1973_;
}
}
}
}
}
v___jp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_a_1966_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1967_);
v___x_1969_ = v___x_1963_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_snd_1961_);
v___x_1969_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
v___jp_1973_:
{
lean_object* v___x_1975_; size_t v___x_1976_; size_t v___x_1977_; 
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
lean_ctor_set(v___x_1975_, 1, v_a_1974_);
v___x_1976_ = ((size_t)1ULL);
v___x_1977_ = lean_usize_add(v_i_1952_, v___x_1976_);
v_i_1952_ = v___x_1977_;
v_b_1953_ = v___x_1975_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2544_, lean_object* v_mvarId_2545_, lean_object* v_as_2546_, lean_object* v_sz_2547_, lean_object* v_i_2548_, lean_object* v_b_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
size_t v_sz_boxed_2555_; size_t v_i_boxed_2556_; lean_object* v_res_2557_; 
v_sz_boxed_2555_ = lean_unbox_usize(v_sz_2547_);
lean_dec(v_sz_2547_);
v_i_boxed_2556_ = lean_unbox_usize(v_i_2548_);
lean_dec(v_i_2548_);
v_res_2557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2544_, v_mvarId_2545_, v_as_2546_, v_sz_boxed_2555_, v_i_boxed_2556_, v_b_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v_as_2546_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2558_, lean_object* v_mvarId_2559_, lean_object* v_as_2560_, size_t v_sz_2561_, size_t v_i_2562_, lean_object* v_b_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_usize_dec_lt(v_i_2562_, v_sz_2561_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; 
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_b_2563_);
return v___x_2570_;
}
else
{
lean_object* v_snd_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_3152_; 
v_snd_2571_ = lean_ctor_get(v_b_2563_, 1);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_b_2563_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v_b_2563_, 0);
lean_dec(v_unused_3153_);
v___x_2573_ = v_b_2563_;
v_isShared_2574_ = v_isSharedCheck_3152_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snd_2571_);
lean_dec(v_b_2563_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_3152_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v_a_2576_; lean_object* v___x_2582_; lean_object* v_a_2584_; lean_object* v_a_2589_; 
v___x_2582_ = lean_box(0);
v_a_2589_ = lean_array_uget(v_as_2560_, v_i_2562_);
if (lean_obj_tag(v_a_2589_) == 0)
{
lean_del_object(v___x_2573_);
v_a_2584_ = v_snd_2571_;
goto v___jp_2583_;
}
else
{
lean_object* v_val_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_3151_; 
v_val_2590_ = lean_ctor_get(v_a_2589_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_a_2589_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_2592_ = v_a_2589_;
v_isShared_2593_ = v_isSharedCheck_3151_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_val_2590_);
lean_dec(v_a_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_3151_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___y_2597_; uint8_t v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; uint8_t v___x_2622_; 
v___x_2594_ = lean_box(0);
v___x_2595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2622_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2590_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; uint8_t v___y_2625_; uint8_t v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2648_; lean_object* v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2651_; uint8_t v___y_2652_; lean_object* v___y_2653_; lean_object* v_a_2654_; lean_object* v___y_2660_; lean_object* v___y_2661_; uint8_t v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; uint8_t v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; uint8_t v___y_2704_; uint8_t v_isHEq_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; uint8_t v_isEq_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___x_3088_; 
v___x_2623_ = l_Lean_LocalDecl_type(v_val_2590_);
lean_inc_ref(v___x_2623_);
v___x_3088_ = l_Lean_Meta_matchNot_x3f(v___x_2623_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
if (lean_obj_tag(v_a_3089_) == 1)
{
lean_object* v_val_3090_; lean_object* v___x_3091_; 
v_val_3090_ = lean_ctor_get(v_a_3089_, 0);
lean_inc(v_val_3090_);
lean_dec_ref_known(v_a_3089_, 1);
v___x_3091_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3090_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref_known(v___x_3091_, 1);
if (lean_obj_tag(v_a_3092_) == 1)
{
lean_object* v_val_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec_ref(v_config_2558_);
v_val_3093_ = lean_ctor_get(v_a_3092_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_a_3092_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3095_ = v_a_3092_;
v_isShared_3096_ = v_isSharedCheck_3134_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_val_3093_);
lean_dec(v_a_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3134_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; 
lean_inc(v_mvarId_2559_);
v___x_3097_ = l_Lean_MVarId_getType(v_mvarId_2559_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v___x_3099_ = l_Lean_LocalDecl_toExpr(v_val_2590_);
v___x_3100_ = l_Lean_mkFVar(v_val_3093_);
v___x_3101_ = l_Lean_Expr_app___override(v___x_3099_, v___x_3100_);
v___x_3102_ = l_Lean_Meta_mkFalseElim(v_a_3098_, v___x_3101_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3104_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3104_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2559_, v_a_3103_, v___y_2565_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
lean_dec_ref_known(v___x_3104_, 1);
v___x_3105_ = lean_box(v___x_2569_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3105_);
v___x_3107_ = v___x_3095_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; 
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
lean_ctor_set(v___x_3108_, 1, v___x_2594_);
v_a_2576_ = v___x_3108_;
goto v___jp_2575_;
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_del_object(v___x_3095_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_3110_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3104_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3104_);
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
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_del_object(v___x_3095_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_3118_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3102_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3102_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_del_object(v___x_3095_);
lean_dec(v_val_3093_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_3126_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3097_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3097_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
else
{
lean_dec(v_a_3092_);
v___y_2954_ = v___y_2564_;
v___y_2955_ = v___y_2565_;
v___y_2956_ = v___y_2566_;
v___y_2957_ = v___y_2567_;
goto v___jp_2953_;
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_3135_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3091_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3091_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
else
{
lean_dec(v_a_3089_);
v___y_2954_ = v___y_2564_;
v___y_2955_ = v___y_2565_;
v___y_2956_ = v___y_2566_;
v___y_2957_ = v___y_2567_;
goto v___jp_2953_;
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_3143_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3088_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3088_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
v___jp_2624_:
{
uint8_t v_genDiseq_2631_; 
v_genDiseq_2631_ = lean_ctor_get_uint8(v_config_2558_, sizeof(void*)*1 + 2);
if (v_genDiseq_2631_ == 0)
{
lean_dec_ref(v___x_2623_);
v___y_2597_ = v___y_2625_;
v___y_2598_ = v___y_2626_;
v___y_2599_ = v___y_2627_;
v___y_2600_ = v___y_2628_;
v___y_2601_ = v___y_2629_;
v___y_2602_ = v___y_2630_;
goto v___jp_2596_;
}
else
{
uint8_t v___x_2632_; 
v___x_2632_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2623_);
lean_dec_ref(v___x_2623_);
if (v___x_2632_ == 0)
{
v___y_2597_ = v___y_2625_;
v___y_2598_ = v___y_2626_;
v___y_2599_ = v___y_2627_;
v___y_2600_ = v___y_2628_;
v___y_2601_ = v___y_2629_;
v___y_2602_ = v___y_2630_;
goto v___jp_2596_;
}
else
{
lean_object* v___x_2633_; 
lean_inc(v_val_2590_);
lean_inc(v_mvarId_2559_);
v___x_2633_ = l_Lean_Meta_processGenDiseq(v_mvarId_2559_, v_val_2590_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; uint8_t v___x_2635_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2635_ = lean_unbox(v_a_2634_);
lean_dec(v_a_2634_);
if (v___x_2635_ == 0)
{
v___y_2597_ = v___y_2625_;
v___y_2598_ = v___y_2626_;
v___y_2599_ = v___y_2627_;
v___y_2600_ = v___y_2628_;
v___y_2601_ = v___y_2629_;
v___y_2602_ = v___y_2630_;
goto v___jp_2596_;
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v___x_2636_ = lean_box(v___x_2569_);
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___x_2594_);
v_a_2576_ = v___x_2638_;
goto v___jp_2575_;
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2639_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2633_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2633_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
}
v___jp_2647_:
{
uint8_t v___x_2655_; 
v___x_2655_ = l_Lean_Exception_isInterrupt(v_a_2654_);
if (v___x_2655_ == 0)
{
uint8_t v___x_2656_; 
lean_inc_ref(v_a_2654_);
v___x_2656_ = l_Lean_Exception_isRuntime(v_a_2654_);
if (v___x_2656_ == 0)
{
lean_dec_ref(v_a_2654_);
v___y_2625_ = v___y_2650_;
v___y_2626_ = v___y_2652_;
v___y_2627_ = v___y_2649_;
v___y_2628_ = v___y_2653_;
v___y_2629_ = v___y_2651_;
v___y_2630_ = v___y_2648_;
goto v___jp_2624_;
}
else
{
lean_object* v___x_2657_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_a_2654_);
return v___x_2657_;
}
}
else
{
lean_object* v___x_2658_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_a_2654_);
return v___x_2658_;
}
}
v___jp_2659_:
{
if (lean_obj_tag(v___y_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_a_2668_ = lean_ctor_get(v___y_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___y_2667_, 1);
v___x_2669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2670_ = l_Lean_Expr_isConstOf(v_a_2668_, v___x_2669_);
lean_dec(v_a_2668_);
if (v___x_2670_ == 0)
{
lean_dec_ref(v___y_2664_);
v___y_2625_ = v___y_2662_;
v___y_2626_ = v___y_2665_;
v___y_2627_ = v___y_2661_;
v___y_2628_ = v___y_2666_;
v___y_2629_ = v___y_2663_;
v___y_2630_ = v___y_2660_;
goto v___jp_2624_;
}
else
{
lean_object* v___x_2671_; 
lean_inc_ref(v___y_2664_);
v___x_2671_ = l_Lean_Meta_mkEqRefl(v___y_2664_, v___y_2661_, v___y_2666_, v___y_2663_, v___y_2660_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; lean_object* v_dummy_2674_; lean_object* v_nargs_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2673_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2674_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2675_ = l_Lean_Expr_getAppNumArgs(v___y_2664_);
lean_inc(v_nargs_2675_);
v___x_2676_ = lean_mk_array(v_nargs_2675_, v_dummy_2674_);
v___x_2677_ = lean_unsigned_to_nat(1u);
v___x_2678_ = lean_nat_sub(v_nargs_2675_, v___x_2677_);
lean_dec(v_nargs_2675_);
v___x_2679_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2664_, v___x_2676_, v___x_2678_);
v___x_2680_ = lean_array_push(v___x_2679_, v_a_2672_);
v___x_2681_ = l_Lean_mkAppN(v___x_2673_, v___x_2680_);
lean_dec_ref(v___x_2680_);
lean_inc(v_mvarId_2559_);
v___x_2682_ = l_Lean_MVarId_getType(v_mvarId_2559_, v___y_2661_, v___y_2666_, v___y_2663_, v___y_2660_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
lean_inc(v_val_2590_);
v___x_2684_ = l_Lean_LocalDecl_toExpr(v_val_2590_);
v___x_2685_ = l_Lean_Meta_mkAbsurd(v_a_2683_, v___x_2684_, v___x_2681_, v___y_2661_, v___y_2666_, v___y_2663_, v___y_2660_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
lean_inc(v_mvarId_2559_);
v___x_2687_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2559_, v_a_2686_, v___y_2666_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v___x_2687_, 0);
lean_dec(v_unused_2697_);
v___x_2689_ = v___x_2687_;
v_isShared_2690_ = v_isSharedCheck_2696_;
goto v_resetjp_2688_;
}
else
{
lean_dec(v___x_2687_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2696_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2691_ = lean_box(v___x_2569_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set_tag(v___x_2689_, 1);
lean_ctor_set(v___x_2689_, 0, v___x_2691_);
v___x_2693_ = v___x_2689_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v___x_2594_);
v_a_2576_ = v___x_2694_;
goto v___jp_2575_;
}
}
}
else
{
lean_object* v_a_2698_; 
v_a_2698_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2687_, 1);
v___y_2648_ = v___y_2660_;
v___y_2649_ = v___y_2661_;
v___y_2650_ = v___y_2662_;
v___y_2651_ = v___y_2663_;
v___y_2652_ = v___y_2665_;
v___y_2653_ = v___y_2666_;
v_a_2654_ = v_a_2698_;
goto v___jp_2647_;
}
}
else
{
lean_object* v_a_2699_; 
v_a_2699_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2685_, 1);
v___y_2648_ = v___y_2660_;
v___y_2649_ = v___y_2661_;
v___y_2650_ = v___y_2662_;
v___y_2651_ = v___y_2663_;
v___y_2652_ = v___y_2665_;
v___y_2653_ = v___y_2666_;
v_a_2654_ = v_a_2699_;
goto v___jp_2647_;
}
}
else
{
lean_object* v_a_2700_; 
lean_dec_ref(v___x_2681_);
v_a_2700_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2682_, 1);
v___y_2648_ = v___y_2660_;
v___y_2649_ = v___y_2661_;
v___y_2650_ = v___y_2662_;
v___y_2651_ = v___y_2663_;
v___y_2652_ = v___y_2665_;
v___y_2653_ = v___y_2666_;
v_a_2654_ = v_a_2700_;
goto v___jp_2647_;
}
}
else
{
lean_object* v_a_2701_; 
lean_dec_ref(v___y_2664_);
v_a_2701_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2671_, 1);
v___y_2648_ = v___y_2660_;
v___y_2649_ = v___y_2661_;
v___y_2650_ = v___y_2662_;
v___y_2651_ = v___y_2663_;
v___y_2652_ = v___y_2665_;
v___y_2653_ = v___y_2666_;
v_a_2654_ = v_a_2701_;
goto v___jp_2647_;
}
}
}
else
{
lean_object* v_a_2702_; 
lean_dec_ref(v___y_2664_);
v_a_2702_ = lean_ctor_get(v___y_2667_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___y_2667_, 1);
v___y_2648_ = v___y_2660_;
v___y_2649_ = v___y_2661_;
v___y_2650_ = v___y_2662_;
v___y_2651_ = v___y_2663_;
v___y_2652_ = v___y_2665_;
v___y_2653_ = v___y_2666_;
v_a_2654_ = v_a_2702_;
goto v___jp_2647_;
}
}
v___jp_2703_:
{
uint8_t v_useDecide_2710_; 
v_useDecide_2710_ = lean_ctor_get_uint8(v_config_2558_, sizeof(void*)*1);
if (v_useDecide_2710_ == 0)
{
v___y_2625_ = v_isHEq_2705_;
v___y_2626_ = v___y_2704_;
v___y_2627_ = v___y_2706_;
v___y_2628_ = v___y_2707_;
v___y_2629_ = v___y_2708_;
v___y_2630_ = v___y_2709_;
goto v___jp_2624_;
}
else
{
uint8_t v___x_2711_; 
v___x_2711_ = l_Lean_Expr_hasFVar(v___x_2623_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; 
lean_inc_ref(v___x_2623_);
v___x_2712_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_2623_, v___y_2707_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; uint8_t v___x_2714_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2712_, 1);
v___x_2714_ = l_Lean_Expr_hasMVar(v_a_2713_);
if (v___x_2714_ == 0)
{
uint8_t v___x_2715_; 
v___x_2715_ = l_Lean_Expr_hasFVar(v_a_2713_);
lean_dec(v_a_2713_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
lean_inc_ref(v___x_2623_);
v___x_2716_ = l_Lean_Meta_mkDecide(v___x_2623_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; uint8_t v_transparency_2719_; uint8_t v___x_2720_; uint8_t v___x_2721_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2718_ = l_Lean_Meta_Context_config(v___y_2706_);
v_transparency_2719_ = lean_ctor_get_uint8(v___x_2718_, 9);
lean_dec_ref(v___x_2718_);
v___x_2720_ = 1;
v___x_2721_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2719_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v_keyedConfig_2722_; uint8_t v_trackZetaDelta_2723_; lean_object* v_zetaDeltaSet_2724_; lean_object* v_lctx_2725_; lean_object* v_localInstances_2726_; lean_object* v_defEqCtx_x3f_2727_; lean_object* v_synthPendingDepth_2728_; lean_object* v_customCanUnfoldPredicate_x3f_2729_; uint8_t v_univApprox_2730_; uint8_t v_inTypeClassResolution_2731_; uint8_t v_cacheInferType_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_keyedConfig_2722_ = lean_ctor_get(v___y_2706_, 0);
v_trackZetaDelta_2723_ = lean_ctor_get_uint8(v___y_2706_, sizeof(void*)*7);
v_zetaDeltaSet_2724_ = lean_ctor_get(v___y_2706_, 1);
v_lctx_2725_ = lean_ctor_get(v___y_2706_, 2);
v_localInstances_2726_ = lean_ctor_get(v___y_2706_, 3);
v_defEqCtx_x3f_2727_ = lean_ctor_get(v___y_2706_, 4);
v_synthPendingDepth_2728_ = lean_ctor_get(v___y_2706_, 5);
v_customCanUnfoldPredicate_x3f_2729_ = lean_ctor_get(v___y_2706_, 6);
v_univApprox_2730_ = lean_ctor_get_uint8(v___y_2706_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2731_ = lean_ctor_get_uint8(v___y_2706_, sizeof(void*)*7 + 2);
v_cacheInferType_2732_ = lean_ctor_get_uint8(v___y_2706_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2722_);
v___x_2733_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2720_, v_keyedConfig_2722_);
lean_inc(v_customCanUnfoldPredicate_x3f_2729_);
lean_inc(v_synthPendingDepth_2728_);
lean_inc(v_defEqCtx_x3f_2727_);
lean_inc_ref(v_localInstances_2726_);
lean_inc_ref(v_lctx_2725_);
lean_inc(v_zetaDeltaSet_2724_);
v___x_2734_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
lean_ctor_set(v___x_2734_, 1, v_zetaDeltaSet_2724_);
lean_ctor_set(v___x_2734_, 2, v_lctx_2725_);
lean_ctor_set(v___x_2734_, 3, v_localInstances_2726_);
lean_ctor_set(v___x_2734_, 4, v_defEqCtx_x3f_2727_);
lean_ctor_set(v___x_2734_, 5, v_synthPendingDepth_2728_);
lean_ctor_set(v___x_2734_, 6, v_customCanUnfoldPredicate_x3f_2729_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*7, v_trackZetaDelta_2723_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*7 + 1, v_univApprox_2730_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2731_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*7 + 3, v_cacheInferType_2732_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc(v_a_2717_);
v___x_2735_ = lean_whnf(v_a_2717_, v___x_2734_, v___y_2707_, v___y_2708_, v___y_2709_);
v___y_2660_ = v___y_2709_;
v___y_2661_ = v___y_2706_;
v___y_2662_ = v_isHEq_2705_;
v___y_2663_ = v___y_2708_;
v___y_2664_ = v_a_2717_;
v___y_2665_ = v___y_2704_;
v___y_2666_ = v___y_2707_;
v___y_2667_ = v___x_2735_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2736_; 
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
lean_inc(v_a_2717_);
v___x_2736_ = lean_whnf(v_a_2717_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
v___y_2660_ = v___y_2709_;
v___y_2661_ = v___y_2706_;
v___y_2662_ = v_isHEq_2705_;
v___y_2663_ = v___y_2708_;
v___y_2664_ = v_a_2717_;
v___y_2665_ = v___y_2704_;
v___y_2666_ = v___y_2707_;
v___y_2667_ = v___x_2736_;
goto v___jp_2659_;
}
}
else
{
lean_object* v_a_2737_; 
v_a_2737_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2716_, 1);
v___y_2648_ = v___y_2709_;
v___y_2649_ = v___y_2706_;
v___y_2650_ = v_isHEq_2705_;
v___y_2651_ = v___y_2708_;
v___y_2652_ = v___y_2704_;
v___y_2653_ = v___y_2707_;
v_a_2654_ = v_a_2737_;
goto v___jp_2647_;
}
}
else
{
v___y_2625_ = v_isHEq_2705_;
v___y_2626_ = v___y_2704_;
v___y_2627_ = v___y_2706_;
v___y_2628_ = v___y_2707_;
v___y_2629_ = v___y_2708_;
v___y_2630_ = v___y_2709_;
goto v___jp_2624_;
}
}
else
{
lean_dec(v_a_2713_);
v___y_2625_ = v_isHEq_2705_;
v___y_2626_ = v___y_2704_;
v___y_2627_ = v___y_2706_;
v___y_2628_ = v___y_2707_;
v___y_2629_ = v___y_2708_;
v___y_2630_ = v___y_2709_;
goto v___jp_2624_;
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2738_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2712_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2712_);
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
else
{
v___y_2625_ = v_isHEq_2705_;
v___y_2626_ = v___y_2704_;
v___y_2627_ = v___y_2706_;
v___y_2628_ = v___y_2707_;
v___y_2629_ = v___y_2708_;
v___y_2630_ = v___y_2709_;
goto v___jp_2624_;
}
}
}
v___jp_2746_:
{
lean_object* v___x_2752_; 
lean_inc_ref(v___x_2623_);
v___x_2752_ = l_Lean_Meta_matchHEq_x3f(v___x_2623_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
if (lean_obj_tag(v_a_2753_) == 1)
{
lean_object* v_val_2754_; lean_object* v_snd_2755_; lean_object* v_snd_2756_; lean_object* v_fst_2757_; lean_object* v_fst_2758_; lean_object* v_fst_2759_; lean_object* v_snd_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2853_; 
v_val_2754_ = lean_ctor_get(v_a_2753_, 0);
lean_inc(v_val_2754_);
lean_dec_ref_known(v_a_2753_, 1);
v_snd_2755_ = lean_ctor_get(v_val_2754_, 1);
lean_inc(v_snd_2755_);
v_snd_2756_ = lean_ctor_get(v_snd_2755_, 1);
lean_inc(v_snd_2756_);
v_fst_2757_ = lean_ctor_get(v_val_2754_, 0);
lean_inc(v_fst_2757_);
lean_dec(v_val_2754_);
v_fst_2758_ = lean_ctor_get(v_snd_2755_, 0);
lean_inc(v_fst_2758_);
lean_dec(v_snd_2755_);
v_fst_2759_ = lean_ctor_get(v_snd_2756_, 0);
v_snd_2760_ = lean_ctor_get(v_snd_2756_, 1);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_snd_2756_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2762_ = v_snd_2756_;
v_isShared_2763_ = v_isSharedCheck_2853_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_snd_2760_);
lean_inc(v_fst_2759_);
lean_dec(v_snd_2756_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2853_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2758_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
if (lean_obj_tag(v_a_2765_) == 1)
{
lean_object* v_val_2766_; lean_object* v___x_2767_; 
v_val_2766_ = lean_ctor_get(v_a_2765_, 0);
lean_inc(v_val_2766_);
lean_dec_ref_known(v_a_2765_, 1);
v___x_2767_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2760_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
if (lean_obj_tag(v_a_2768_) == 1)
{
lean_object* v_toConstantVal_2769_; lean_object* v_val_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2836_; 
v_toConstantVal_2769_ = lean_ctor_get(v_val_2766_, 0);
lean_inc_ref(v_toConstantVal_2769_);
lean_dec(v_val_2766_);
v_val_2770_ = lean_ctor_get(v_a_2768_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_a_2768_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2772_ = v_a_2768_;
v_isShared_2773_ = v_isSharedCheck_2836_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_val_2770_);
lean_dec(v_a_2768_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2836_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v_toConstantVal_2774_; lean_object* v_name_2775_; lean_object* v_name_2776_; uint8_t v___x_2777_; 
v_toConstantVal_2774_ = lean_ctor_get(v_val_2770_, 0);
lean_inc_ref(v_toConstantVal_2774_);
lean_dec(v_val_2770_);
v_name_2775_ = lean_ctor_get(v_toConstantVal_2769_, 0);
lean_inc(v_name_2775_);
lean_dec_ref(v_toConstantVal_2769_);
v_name_2776_ = lean_ctor_get(v_toConstantVal_2774_, 0);
lean_inc(v_name_2776_);
lean_dec_ref(v_toConstantVal_2774_);
v___x_2777_ = lean_name_eq(v_name_2775_, v_name_2776_);
lean_dec(v_name_2776_);
lean_dec(v_name_2775_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Meta_isExprDefEq(v_fst_2757_, v_fst_2759_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; uint8_t v___x_2780_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = lean_unbox(v_a_2779_);
lean_dec(v_a_2779_);
if (v___x_2780_ == 0)
{
lean_del_object(v___x_2772_);
lean_del_object(v___x_2762_);
v___y_2704_ = v_isEq_2747_;
v_isHEq_2705_ = v___x_2569_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
v___y_2709_ = v___y_2751_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2781_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec_ref(v_config_2558_);
lean_inc(v_mvarId_2559_);
v___x_2781_ = l_Lean_MVarId_getType(v_mvarId_2559_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = l_Lean_LocalDecl_toExpr(v_val_2590_);
v___x_2784_ = l_Lean_Meta_mkEqOfHEq(v___x_2783_, v___x_2569_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2786_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2786_ = l_Lean_Meta_mkNoConfusion(v_a_2782_, v_a_2785_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2559_, v_a_2787_, v___y_2749_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2791_; 
lean_dec_ref_known(v___x_2788_, 1);
v___x_2789_ = lean_box(v___x_2569_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2789_);
v___x_2791_ = v___x_2772_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2793_; 
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 1, v___x_2594_);
lean_ctor_set(v___x_2762_, 0, v___x_2791_);
v___x_2793_ = v___x_2762_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v___x_2594_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
v_a_2576_ = v___x_2793_;
goto v___jp_2575_;
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_del_object(v___x_2772_);
lean_del_object(v___x_2762_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_2796_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2788_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2788_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_del_object(v___x_2772_);
lean_del_object(v___x_2762_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_2804_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2786_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2786_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_a_2782_);
lean_del_object(v___x_2772_);
lean_del_object(v___x_2762_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_2812_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2784_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2784_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_del_object(v___x_2772_);
lean_del_object(v___x_2762_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_2820_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2781_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2781_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2772_);
lean_del_object(v___x_2762_);
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2828_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2778_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2778_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_del_object(v___x_2772_);
lean_del_object(v___x_2762_);
lean_dec(v_fst_2759_);
lean_dec(v_fst_2757_);
v___y_2704_ = v_isEq_2747_;
v_isHEq_2705_ = v___x_2569_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
v___y_2709_ = v___y_2751_;
goto v___jp_2703_;
}
}
}
else
{
lean_dec(v_a_2768_);
lean_dec(v_val_2766_);
lean_del_object(v___x_2762_);
lean_dec(v_fst_2759_);
lean_dec(v_fst_2757_);
v___y_2704_ = v_isEq_2747_;
v_isHEq_2705_ = v___x_2569_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
v___y_2709_ = v___y_2751_;
goto v___jp_2703_;
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_val_2766_);
lean_del_object(v___x_2762_);
lean_dec(v_fst_2759_);
lean_dec(v_fst_2757_);
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2837_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2767_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2767_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
else
{
lean_dec(v_a_2765_);
lean_del_object(v___x_2762_);
lean_dec(v_snd_2760_);
lean_dec(v_fst_2759_);
lean_dec(v_fst_2757_);
v___y_2704_ = v_isEq_2747_;
v_isHEq_2705_ = v___x_2569_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
v___y_2709_ = v___y_2751_;
goto v___jp_2703_;
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_del_object(v___x_2762_);
lean_dec(v_snd_2760_);
lean_dec(v_fst_2759_);
lean_dec(v_fst_2757_);
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2845_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2764_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2764_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
else
{
lean_dec(v_a_2753_);
v___y_2704_ = v_isEq_2747_;
v_isHEq_2705_ = v___x_2622_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
v___y_2709_ = v___y_2751_;
goto v___jp_2703_;
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2854_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2752_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2752_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
v___jp_2862_:
{
lean_object* v___x_2867_; 
lean_inc_ref(v___x_2623_);
v___x_2867_ = l_Lean_Meta_matchEq_x3f(v___x_2623_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
if (lean_obj_tag(v_a_2868_) == 1)
{
lean_object* v_val_2869_; lean_object* v_snd_2870_; lean_object* v_fst_2871_; lean_object* v_snd_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2944_; 
v_val_2869_ = lean_ctor_get(v_a_2868_, 0);
lean_inc(v_val_2869_);
lean_dec_ref_known(v_a_2868_, 1);
v_snd_2870_ = lean_ctor_get(v_val_2869_, 1);
lean_inc(v_snd_2870_);
lean_dec(v_val_2869_);
v_fst_2871_ = lean_ctor_get(v_snd_2870_, 0);
v_snd_2872_ = lean_ctor_get(v_snd_2870_, 1);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_snd_2870_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2874_ = v_snd_2870_;
v_isShared_2875_ = v_isSharedCheck_2944_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_snd_2872_);
lean_inc(v_fst_2871_);
lean_dec(v_snd_2870_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2944_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2871_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
if (lean_obj_tag(v_a_2877_) == 1)
{
lean_object* v_val_2878_; lean_object* v___x_2879_; 
v_val_2878_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_val_2878_);
lean_dec_ref_known(v_a_2877_, 1);
v___x_2879_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2872_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
if (lean_obj_tag(v_a_2880_) == 1)
{
lean_object* v_toConstantVal_2881_; lean_object* v_val_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2927_; 
v_toConstantVal_2881_ = lean_ctor_get(v_val_2878_, 0);
lean_inc_ref(v_toConstantVal_2881_);
lean_dec(v_val_2878_);
v_val_2882_ = lean_ctor_get(v_a_2880_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_a_2880_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2884_ = v_a_2880_;
v_isShared_2885_ = v_isSharedCheck_2927_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_val_2882_);
lean_dec(v_a_2880_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2927_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v_toConstantVal_2886_; lean_object* v_name_2887_; lean_object* v_name_2888_; uint8_t v___x_2889_; 
v_toConstantVal_2886_ = lean_ctor_get(v_val_2882_, 0);
lean_inc_ref(v_toConstantVal_2886_);
lean_dec(v_val_2882_);
v_name_2887_ = lean_ctor_get(v_toConstantVal_2881_, 0);
lean_inc(v_name_2887_);
lean_dec_ref(v_toConstantVal_2881_);
v_name_2888_ = lean_ctor_get(v_toConstantVal_2886_, 0);
lean_inc(v_name_2888_);
lean_dec_ref(v_toConstantVal_2886_);
v___x_2889_ = lean_name_eq(v_name_2887_, v_name_2888_);
lean_dec(v_name_2888_);
lean_dec(v_name_2887_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec_ref(v_config_2558_);
lean_inc(v_mvarId_2559_);
v___x_2890_ = l_Lean_MVarId_getType(v_mvarId_2559_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = l_Lean_LocalDecl_toExpr(v_val_2590_);
v___x_2893_ = l_Lean_Meta_mkNoConfusion(v_a_2891_, v___x_2892_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2559_, v_a_2894_, v___y_2864_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
lean_dec_ref_known(v___x_2895_, 1);
v___x_2896_ = lean_box(v___x_2569_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2896_);
v___x_2898_ = v___x_2884_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2900_; 
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 1, v___x_2594_);
lean_ctor_set(v___x_2874_, 0, v___x_2898_);
v___x_2900_ = v___x_2874_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v___x_2594_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
v_a_2576_ = v___x_2900_;
goto v___jp_2575_;
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_del_object(v___x_2884_);
lean_del_object(v___x_2874_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_2903_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2895_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2895_);
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
lean_del_object(v___x_2884_);
lean_del_object(v___x_2874_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_2911_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2893_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2893_);
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
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_del_object(v___x_2884_);
lean_del_object(v___x_2874_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_2919_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2890_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2890_);
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
else
{
lean_del_object(v___x_2884_);
lean_del_object(v___x_2874_);
v_isEq_2747_ = v___x_2569_;
v___y_2748_ = v___y_2863_;
v___y_2749_ = v___y_2864_;
v___y_2750_ = v___y_2865_;
v___y_2751_ = v___y_2866_;
goto v___jp_2746_;
}
}
}
else
{
lean_dec(v_a_2880_);
lean_dec(v_val_2878_);
lean_del_object(v___x_2874_);
v_isEq_2747_ = v___x_2569_;
v___y_2748_ = v___y_2863_;
v___y_2749_ = v___y_2864_;
v___y_2750_ = v___y_2865_;
v___y_2751_ = v___y_2866_;
goto v___jp_2746_;
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_val_2878_);
lean_del_object(v___x_2874_);
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2928_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2879_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2879_);
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
else
{
lean_dec(v_a_2877_);
lean_del_object(v___x_2874_);
lean_dec(v_snd_2872_);
v_isEq_2747_ = v___x_2569_;
v___y_2748_ = v___y_2863_;
v___y_2749_ = v___y_2864_;
v___y_2750_ = v___y_2865_;
v___y_2751_ = v___y_2866_;
goto v___jp_2746_;
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_del_object(v___x_2874_);
lean_dec(v_snd_2872_);
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2936_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2876_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2876_);
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
lean_dec(v_a_2868_);
v_isEq_2747_ = v___x_2622_;
v___y_2748_ = v___y_2863_;
v___y_2749_ = v___y_2864_;
v___y_2750_ = v___y_2865_;
v___y_2751_ = v___y_2866_;
goto v___jp_2746_;
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2945_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2867_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2867_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
v___jp_2953_:
{
lean_object* v___x_2958_; 
lean_inc_ref(v___x_2623_);
v___x_2958_ = l_Lean_refutableHasNotBit_x3f(v___x_2623_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
if (lean_obj_tag(v_a_2959_) == 1)
{
lean_object* v_val_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec_ref(v_config_2558_);
v_val_2960_ = lean_ctor_get(v_a_2959_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_a_2959_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2962_ = v_a_2959_;
v_isShared_2963_ = v_isSharedCheck_2999_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_val_2960_);
lean_dec(v_a_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2999_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; 
lean_inc(v_mvarId_2559_);
v___x_2964_ = l_Lean_MVarId_getType(v_mvarId_2559_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2966_ = l_Lean_LocalDecl_toExpr(v_val_2590_);
v___x_2967_ = l_Lean_Meta_mkAbsurd(v_a_2965_, v_val_2960_, v___x_2966_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v___x_2969_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2559_, v_a_2968_, v___y_2955_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2972_; 
lean_dec_ref_known(v___x_2969_, 1);
v___x_2970_ = lean_box(v___x_2569_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2970_);
v___x_2972_ = v___x_2962_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v___x_2594_);
v_a_2576_ = v___x_2973_;
goto v___jp_2575_;
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_del_object(v___x_2962_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_2975_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2969_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2969_);
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
lean_del_object(v___x_2962_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_2983_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2967_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2967_);
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
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_del_object(v___x_2962_);
lean_dec(v_val_2960_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_2991_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2964_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2964_);
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
}
else
{
lean_object* v___x_3000_; 
lean_dec(v_a_2959_);
lean_inc_ref(v___x_2623_);
v___x_3000_ = l_Lean_Meta_matchNe_x3f(v___x_2623_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
if (lean_obj_tag(v_a_3001_) == 1)
{
lean_object* v_val_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3071_; 
v_val_3002_ = lean_ctor_get(v_a_3001_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_a_3001_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3004_ = v_a_3001_;
v_isShared_3005_ = v_isSharedCheck_3071_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_val_3002_);
lean_dec(v_a_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3071_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v_snd_3006_; lean_object* v_fst_3007_; lean_object* v_snd_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3070_; 
v_snd_3006_ = lean_ctor_get(v_val_3002_, 1);
lean_inc(v_snd_3006_);
lean_dec(v_val_3002_);
v_fst_3007_ = lean_ctor_get(v_snd_3006_, 0);
v_snd_3008_ = lean_ctor_get(v_snd_3006_, 1);
v_isSharedCheck_3070_ = !lean_is_exclusive(v_snd_3006_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3010_ = v_snd_3006_;
v_isShared_3011_ = v_isSharedCheck_3070_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_snd_3008_);
lean_inc(v_fst_3007_);
lean_dec(v_snd_3006_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3070_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; 
lean_inc(v_fst_3007_);
v___x_3012_ = l_Lean_Meta_isExprDefEq(v_fst_3007_, v_snd_3008_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; uint8_t v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = lean_unbox(v_a_3013_);
lean_dec(v_a_3013_);
if (v___x_3014_ == 0)
{
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_del_object(v___x_3004_);
v___y_2863_ = v___y_2954_;
v___y_2864_ = v___y_2955_;
v___y_2865_ = v___y_2956_;
v___y_2866_ = v___y_2957_;
goto v___jp_2862_;
}
else
{
lean_object* v___x_3015_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec_ref(v_config_2558_);
lean_inc(v_mvarId_2559_);
v___x_3015_ = l_Lean_MVarId_getType(v_mvarId_2559_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = l_Lean_Meta_mkEqRefl(v_fst_3007_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = l_Lean_LocalDecl_toExpr(v_val_2590_);
v___x_3020_ = l_Lean_Meta_mkAbsurd(v_a_3016_, v_a_3018_, v___x_3019_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2559_, v_a_3021_, v___y_2955_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_dec_ref_known(v___x_3022_, 1);
v___x_3023_ = lean_box(v___x_2569_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3023_);
v___x_3025_ = v___x_3004_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 1, v___x_2594_);
lean_ctor_set(v___x_3010_, 0, v___x_3025_);
v___x_3027_ = v___x_3010_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v___x_2594_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
v_a_2576_ = v___x_3027_;
goto v___jp_2575_;
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_del_object(v___x_3010_);
lean_del_object(v___x_3004_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_3030_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3022_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3022_);
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
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_del_object(v___x_3010_);
lean_del_object(v___x_3004_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_3038_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3020_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3020_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec(v_a_3016_);
lean_del_object(v___x_3010_);
lean_del_object(v___x_3004_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_3046_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3017_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3017_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_del_object(v___x_3004_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
v_a_3054_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3015_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3015_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_del_object(v___x_3010_);
lean_dec(v_fst_3007_);
lean_del_object(v___x_3004_);
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_3062_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3012_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3012_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3001_);
v___y_2863_ = v___y_2954_;
v___y_2864_ = v___y_2955_;
v___y_2865_ = v___y_2956_;
v___y_2866_ = v___y_2957_;
goto v___jp_2862_;
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_3072_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3000_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3000_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v___x_2623_);
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_3080_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_2958_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_2958_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
else
{
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_2584_ = v___x_2595_;
goto v___jp_2583_;
}
v___jp_2596_:
{
uint8_t v_emptyType_2603_; 
v_emptyType_2603_ = lean_ctor_get_uint8(v_config_2558_, sizeof(void*)*1 + 1);
if (v_emptyType_2603_ == 0)
{
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_2584_ = v___x_2595_;
goto v___jp_2583_;
}
else
{
if (v___y_2598_ == 0)
{
if (v___y_2597_ == 0)
{
lean_object* v_searchFuel_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_searchFuel_2604_ = lean_ctor_get(v_config_2558_, 0);
v___x_2605_ = l_Lean_LocalDecl_fvarId(v_val_2590_);
lean_dec(v_val_2590_);
lean_inc(v_searchFuel_2604_);
lean_inc(v_mvarId_2559_);
v___x_2606_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_2559_, v___x_2605_, v_searchFuel_2604_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
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
lean_del_object(v___x_2592_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_2584_ = v___x_2595_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v___x_2609_ = lean_box(v___x_2569_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2609_);
v___x_2611_ = v___x_2592_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2594_);
v_a_2576_ = v___x_2612_;
goto v___jp_2575_;
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_del_object(v___x_2592_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2559_);
lean_dec_ref(v_config_2558_);
v_a_2614_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2606_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2606_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_2584_ = v___x_2595_;
goto v___jp_2583_;
}
}
else
{
lean_del_object(v___x_2592_);
lean_dec(v_val_2590_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
v_a_2584_ = v___x_2595_;
goto v___jp_2583_;
}
}
}
}
}
v___jp_2575_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2577_, 0, v_a_2576_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2577_);
v___x_2579_ = v___x_2573_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_snd_2571_);
v___x_2579_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
return v___x_2580_;
}
}
v___jp_2583_:
{
lean_object* v___x_2585_; size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2582_);
lean_ctor_set(v___x_2585_, 1, v_a_2584_);
v___x_2586_ = ((size_t)1ULL);
v___x_2587_ = lean_usize_add(v_i_2562_, v___x_2586_);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2558_, v_mvarId_2559_, v_as_2560_, v_sz_2561_, v___x_2587_, v___x_2585_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3154_, lean_object* v_mvarId_3155_, lean_object* v_as_3156_, lean_object* v_sz_3157_, lean_object* v_i_3158_, lean_object* v_b_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
size_t v_sz_boxed_3165_; size_t v_i_boxed_3166_; lean_object* v_res_3167_; 
v_sz_boxed_3165_ = lean_unbox_usize(v_sz_3157_);
lean_dec(v_sz_3157_);
v_i_boxed_3166_ = lean_unbox_usize(v_i_3158_);
lean_dec(v_i_3158_);
v_res_3167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3154_, v_mvarId_3155_, v_as_3156_, v_sz_boxed_3165_, v_i_boxed_3166_, v_b_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec_ref(v_as_3156_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3171_, lean_object* v_mvarId_3172_, lean_object* v_as_3173_, size_t v_sz_3174_, size_t v_i_3175_, lean_object* v_b_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_usize_dec_lt(v_i_3175_, v_sz_3174_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; 
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v_b_3176_);
return v___x_3183_;
}
else
{
lean_object* v_snd_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3797_; 
v_snd_3184_ = lean_ctor_get(v_b_3176_, 1);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_b_3176_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; 
v_unused_3798_ = lean_ctor_get(v_b_3176_, 0);
lean_dec(v_unused_3798_);
v___x_3186_ = v_b_3176_;
v_isShared_3187_ = v_isSharedCheck_3797_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_snd_3184_);
lean_dec(v_b_3176_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3797_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v_a_3189_; lean_object* v___x_3195_; lean_object* v_a_3197_; lean_object* v_a_3202_; 
v___x_3195_ = lean_box(0);
v_a_3202_ = lean_array_uget(v_as_3173_, v_i_3175_);
if (lean_obj_tag(v_a_3202_) == 0)
{
lean_del_object(v___x_3186_);
v_a_3197_ = v_snd_3184_;
goto v___jp_3196_;
}
else
{
lean_object* v_val_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3796_; 
v_val_3203_ = lean_ctor_get(v_a_3202_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_a_3202_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3205_ = v_a_3202_;
v_isShared_3206_ = v_isSharedCheck_3796_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_val_3203_);
lean_dec(v_a_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3796_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___y_3210_; uint8_t v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; uint8_t v___x_3236_; 
v___x_3207_ = lean_box(0);
v___x_3208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3236_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3203_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; uint8_t v___y_3239_; uint8_t v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; uint8_t v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v_a_3269_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; uint8_t v___y_3279_; lean_object* v___y_3280_; uint8_t v___y_3281_; lean_object* v___y_3282_; uint8_t v___y_3326_; uint8_t v_isHEq_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; uint8_t v_isEq_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___x_3726_; 
v___x_3237_ = l_Lean_LocalDecl_type(v_val_3203_);
lean_inc_ref(v___x_3237_);
v___x_3726_ = l_Lean_Meta_matchNot_x3f(v___x_3237_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
if (lean_obj_tag(v_a_3727_) == 1)
{
lean_object* v_val_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3787_; 
v_val_3728_ = lean_ctor_get(v_a_3727_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_a_3727_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3730_ = v_a_3727_;
v_isShared_3731_ = v_isSharedCheck_3787_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_val_3728_);
lean_dec(v_a_3727_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3787_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3728_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___x_3732_, 1);
if (lean_obj_tag(v_a_3733_) == 1)
{
lean_object* v_val_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3778_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec_ref(v_config_3171_);
v_val_3734_ = lean_ctor_get(v_a_3733_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_a_3733_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3736_ = v_a_3733_;
v_isShared_3737_ = v_isSharedCheck_3778_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_val_3734_);
lean_dec(v_a_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3778_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; 
lean_inc(v_mvarId_3172_);
v___x_3738_ = l_Lean_MVarId_getType(v_mvarId_3172_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3738_, 1);
v___x_3740_ = l_Lean_LocalDecl_toExpr(v_val_3203_);
v___x_3741_ = l_Lean_mkFVar(v_val_3734_);
v___x_3742_ = l_Lean_Expr_app___override(v___x_3740_, v___x_3741_);
v___x_3743_ = l_Lean_Meta_mkFalseElim(v_a_3739_, v___x_3742_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3745_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v___x_3745_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3172_, v_a_3744_, v___y_3178_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v___x_3746_; lean_object* v___x_3748_; 
lean_dec_ref_known(v___x_3745_, 1);
v___x_3746_ = lean_box(v___x_3182_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v___x_3746_);
v___x_3748_ = v___x_3736_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3749_; lean_object* v___x_3751_; 
v___x_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v___x_3207_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set_tag(v___x_3730_, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3749_);
v___x_3751_ = v___x_3730_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
v_a_3189_ = v___x_3751_;
goto v___jp_3188_;
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_del_object(v___x_3736_);
lean_del_object(v___x_3730_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3754_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3745_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3745_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_del_object(v___x_3736_);
lean_del_object(v___x_3730_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3762_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3743_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3743_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_del_object(v___x_3736_);
lean_dec(v_val_3734_);
lean_del_object(v___x_3730_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3770_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3738_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3738_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
else
{
lean_dec(v_a_3733_);
lean_del_object(v___x_3730_);
v___y_3590_ = v___y_3177_;
v___y_3591_ = v___y_3178_;
v___y_3592_ = v___y_3179_;
v___y_3593_ = v___y_3180_;
goto v___jp_3589_;
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_del_object(v___x_3730_);
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3779_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3732_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3732_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
else
{
lean_dec(v_a_3727_);
v___y_3590_ = v___y_3177_;
v___y_3591_ = v___y_3178_;
v___y_3592_ = v___y_3179_;
v___y_3593_ = v___y_3180_;
goto v___jp_3589_;
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3788_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3726_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3726_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
v___jp_3238_:
{
uint8_t v_genDiseq_3245_; 
v_genDiseq_3245_ = lean_ctor_get_uint8(v_config_3171_, sizeof(void*)*1 + 2);
if (v_genDiseq_3245_ == 0)
{
lean_dec_ref(v___x_3237_);
v___y_3210_ = v___y_3239_;
v___y_3211_ = v___y_3240_;
v___y_3212_ = v___y_3241_;
v___y_3213_ = v___y_3242_;
v___y_3214_ = v___y_3243_;
v___y_3215_ = v___y_3244_;
goto v___jp_3209_;
}
else
{
uint8_t v___x_3246_; 
v___x_3246_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3237_);
lean_dec_ref(v___x_3237_);
if (v___x_3246_ == 0)
{
v___y_3210_ = v___y_3239_;
v___y_3211_ = v___y_3240_;
v___y_3212_ = v___y_3241_;
v___y_3213_ = v___y_3242_;
v___y_3214_ = v___y_3243_;
v___y_3215_ = v___y_3244_;
goto v___jp_3209_;
}
else
{
lean_object* v___x_3247_; 
lean_inc(v_val_3203_);
lean_inc(v_mvarId_3172_);
v___x_3247_ = l_Lean_Meta_processGenDiseq(v_mvarId_3172_, v_val_3203_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; uint8_t v___x_3249_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3247_, 1);
v___x_3249_ = lean_unbox(v_a_3248_);
lean_dec(v_a_3248_);
if (v___x_3249_ == 0)
{
v___y_3210_ = v___y_3239_;
v___y_3211_ = v___y_3240_;
v___y_3212_ = v___y_3241_;
v___y_3213_ = v___y_3242_;
v___y_3214_ = v___y_3243_;
v___y_3215_ = v___y_3244_;
goto v___jp_3209_;
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v___x_3250_ = lean_box(v___x_3182_);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
lean_ctor_set(v___x_3252_, 1, v___x_3207_);
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
v_a_3189_ = v___x_3253_;
goto v___jp_3188_;
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3254_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3247_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3247_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
}
v___jp_3262_:
{
uint8_t v___x_3270_; 
v___x_3270_ = l_Lean_Exception_isInterrupt(v_a_3269_);
if (v___x_3270_ == 0)
{
uint8_t v___x_3271_; 
lean_inc_ref(v_a_3269_);
v___x_3271_ = l_Lean_Exception_isRuntime(v_a_3269_);
if (v___x_3271_ == 0)
{
lean_dec_ref(v_a_3269_);
v___y_3239_ = v___y_3266_;
v___y_3240_ = v___y_3268_;
v___y_3241_ = v___y_3263_;
v___y_3242_ = v___y_3265_;
v___y_3243_ = v___y_3267_;
v___y_3244_ = v___y_3264_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3272_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_a_3269_);
return v___x_3272_;
}
}
else
{
lean_object* v___x_3273_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v___x_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3273_, 0, v_a_3269_);
return v___x_3273_;
}
}
v___jp_3274_:
{
if (lean_obj_tag(v___y_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_a_3283_ = lean_ctor_get(v___y_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___y_3282_, 1);
v___x_3284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3285_ = l_Lean_Expr_isConstOf(v_a_3283_, v___x_3284_);
lean_dec(v_a_3283_);
if (v___x_3285_ == 0)
{
lean_dec_ref(v___y_3278_);
v___y_3239_ = v___y_3279_;
v___y_3240_ = v___y_3281_;
v___y_3241_ = v___y_3275_;
v___y_3242_ = v___y_3277_;
v___y_3243_ = v___y_3280_;
v___y_3244_ = v___y_3276_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3286_; 
lean_inc_ref(v___y_3278_);
v___x_3286_ = l_Lean_Meta_mkEqRefl(v___y_3278_, v___y_3275_, v___y_3277_, v___y_3280_, v___y_3276_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v_dummy_3289_; lean_object* v_nargs_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3288_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3289_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3290_ = l_Lean_Expr_getAppNumArgs(v___y_3278_);
lean_inc(v_nargs_3290_);
v___x_3291_ = lean_mk_array(v_nargs_3290_, v_dummy_3289_);
v___x_3292_ = lean_unsigned_to_nat(1u);
v___x_3293_ = lean_nat_sub(v_nargs_3290_, v___x_3292_);
lean_dec(v_nargs_3290_);
v___x_3294_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3278_, v___x_3291_, v___x_3293_);
v___x_3295_ = lean_array_push(v___x_3294_, v_a_3287_);
v___x_3296_ = l_Lean_mkAppN(v___x_3288_, v___x_3295_);
lean_dec_ref(v___x_3295_);
lean_inc(v_mvarId_3172_);
v___x_3297_ = l_Lean_MVarId_getType(v_mvarId_3172_, v___y_3275_, v___y_3277_, v___y_3280_, v___y_3276_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
lean_inc(v_val_3203_);
v___x_3299_ = l_Lean_LocalDecl_toExpr(v_val_3203_);
v___x_3300_ = l_Lean_Meta_mkAbsurd(v_a_3298_, v___x_3299_, v___x_3296_, v___y_3275_, v___y_3277_, v___y_3280_, v___y_3276_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3320_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3320_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3320_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; 
lean_inc(v_mvarId_3172_);
v___x_3305_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3172_, v_a_3301_, v___y_3277_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3317_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v___x_3305_, 0);
lean_dec(v_unused_3318_);
v___x_3307_ = v___x_3305_;
v_isShared_3308_ = v_isSharedCheck_3317_;
goto v_resetjp_3306_;
}
else
{
lean_dec(v___x_3305_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3317_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3309_ = lean_box(v___x_3182_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set_tag(v___x_3307_, 1);
lean_ctor_set(v___x_3307_, 0, v___x_3309_);
v___x_3311_ = v___x_3307_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3312_; lean_object* v___x_3314_; 
v___x_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v___x_3207_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3312_);
v___x_3314_ = v___x_3303_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3312_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
v_a_3189_ = v___x_3314_;
goto v___jp_3188_;
}
}
}
}
else
{
lean_object* v_a_3319_; 
lean_del_object(v___x_3303_);
v_a_3319_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3305_, 1);
v___y_3263_ = v___y_3275_;
v___y_3264_ = v___y_3276_;
v___y_3265_ = v___y_3277_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v___y_3268_ = v___y_3281_;
v_a_3269_ = v_a_3319_;
goto v___jp_3262_;
}
}
}
else
{
lean_object* v_a_3321_; 
v_a_3321_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3321_);
lean_dec_ref_known(v___x_3300_, 1);
v___y_3263_ = v___y_3275_;
v___y_3264_ = v___y_3276_;
v___y_3265_ = v___y_3277_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v___y_3268_ = v___y_3281_;
v_a_3269_ = v_a_3321_;
goto v___jp_3262_;
}
}
else
{
lean_object* v_a_3322_; 
lean_dec_ref(v___x_3296_);
v_a_3322_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3297_, 1);
v___y_3263_ = v___y_3275_;
v___y_3264_ = v___y_3276_;
v___y_3265_ = v___y_3277_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v___y_3268_ = v___y_3281_;
v_a_3269_ = v_a_3322_;
goto v___jp_3262_;
}
}
else
{
lean_object* v_a_3323_; 
lean_dec_ref(v___y_3278_);
v_a_3323_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3286_, 1);
v___y_3263_ = v___y_3275_;
v___y_3264_ = v___y_3276_;
v___y_3265_ = v___y_3277_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v___y_3268_ = v___y_3281_;
v_a_3269_ = v_a_3323_;
goto v___jp_3262_;
}
}
}
else
{
lean_object* v_a_3324_; 
lean_dec_ref(v___y_3278_);
v_a_3324_ = lean_ctor_get(v___y_3282_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___y_3282_, 1);
v___y_3263_ = v___y_3275_;
v___y_3264_ = v___y_3276_;
v___y_3265_ = v___y_3277_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v___y_3268_ = v___y_3281_;
v_a_3269_ = v_a_3324_;
goto v___jp_3262_;
}
}
v___jp_3325_:
{
uint8_t v_useDecide_3332_; 
v_useDecide_3332_ = lean_ctor_get_uint8(v_config_3171_, sizeof(void*)*1);
if (v_useDecide_3332_ == 0)
{
v___y_3239_ = v_isHEq_3327_;
v___y_3240_ = v___y_3326_;
v___y_3241_ = v___y_3328_;
v___y_3242_ = v___y_3329_;
v___y_3243_ = v___y_3330_;
v___y_3244_ = v___y_3331_;
goto v___jp_3238_;
}
else
{
uint8_t v___x_3333_; 
v___x_3333_ = l_Lean_Expr_hasFVar(v___x_3237_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
lean_inc_ref(v___x_3237_);
v___x_3334_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_3237_, v___y_3329_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; uint8_t v___x_3336_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
v___x_3336_ = l_Lean_Expr_hasMVar(v_a_3335_);
if (v___x_3336_ == 0)
{
uint8_t v___x_3337_; 
v___x_3337_ = l_Lean_Expr_hasFVar(v_a_3335_);
lean_dec(v_a_3335_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
lean_inc_ref(v___x_3237_);
v___x_3338_ = l_Lean_Meta_mkDecide(v___x_3237_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3340_; uint8_t v_transparency_3341_; uint8_t v___x_3342_; uint8_t v___x_3343_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3340_ = l_Lean_Meta_Context_config(v___y_3328_);
v_transparency_3341_ = lean_ctor_get_uint8(v___x_3340_, 9);
lean_dec_ref(v___x_3340_);
v___x_3342_ = 1;
v___x_3343_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3341_, v___x_3342_);
if (v___x_3343_ == 0)
{
lean_object* v_keyedConfig_3344_; uint8_t v_trackZetaDelta_3345_; lean_object* v_zetaDeltaSet_3346_; lean_object* v_lctx_3347_; lean_object* v_localInstances_3348_; lean_object* v_defEqCtx_x3f_3349_; lean_object* v_synthPendingDepth_3350_; lean_object* v_customCanUnfoldPredicate_x3f_3351_; uint8_t v_univApprox_3352_; uint8_t v_inTypeClassResolution_3353_; uint8_t v_cacheInferType_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_keyedConfig_3344_ = lean_ctor_get(v___y_3328_, 0);
v_trackZetaDelta_3345_ = lean_ctor_get_uint8(v___y_3328_, sizeof(void*)*7);
v_zetaDeltaSet_3346_ = lean_ctor_get(v___y_3328_, 1);
v_lctx_3347_ = lean_ctor_get(v___y_3328_, 2);
v_localInstances_3348_ = lean_ctor_get(v___y_3328_, 3);
v_defEqCtx_x3f_3349_ = lean_ctor_get(v___y_3328_, 4);
v_synthPendingDepth_3350_ = lean_ctor_get(v___y_3328_, 5);
v_customCanUnfoldPredicate_x3f_3351_ = lean_ctor_get(v___y_3328_, 6);
v_univApprox_3352_ = lean_ctor_get_uint8(v___y_3328_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3353_ = lean_ctor_get_uint8(v___y_3328_, sizeof(void*)*7 + 2);
v_cacheInferType_3354_ = lean_ctor_get_uint8(v___y_3328_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3344_);
v___x_3355_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3342_, v_keyedConfig_3344_);
lean_inc(v_customCanUnfoldPredicate_x3f_3351_);
lean_inc(v_synthPendingDepth_3350_);
lean_inc(v_defEqCtx_x3f_3349_);
lean_inc_ref(v_localInstances_3348_);
lean_inc_ref(v_lctx_3347_);
lean_inc(v_zetaDeltaSet_3346_);
v___x_3356_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v_zetaDeltaSet_3346_);
lean_ctor_set(v___x_3356_, 2, v_lctx_3347_);
lean_ctor_set(v___x_3356_, 3, v_localInstances_3348_);
lean_ctor_set(v___x_3356_, 4, v_defEqCtx_x3f_3349_);
lean_ctor_set(v___x_3356_, 5, v_synthPendingDepth_3350_);
lean_ctor_set(v___x_3356_, 6, v_customCanUnfoldPredicate_x3f_3351_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7, v_trackZetaDelta_3345_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7 + 1, v_univApprox_3352_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3353_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7 + 3, v_cacheInferType_3354_);
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
lean_inc(v___y_3329_);
lean_inc(v_a_3339_);
v___x_3357_ = lean_whnf(v_a_3339_, v___x_3356_, v___y_3329_, v___y_3330_, v___y_3331_);
v___y_3275_ = v___y_3328_;
v___y_3276_ = v___y_3331_;
v___y_3277_ = v___y_3329_;
v___y_3278_ = v_a_3339_;
v___y_3279_ = v_isHEq_3327_;
v___y_3280_ = v___y_3330_;
v___y_3281_ = v___y_3326_;
v___y_3282_ = v___x_3357_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3358_; 
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
lean_inc(v___y_3329_);
lean_inc_ref(v___y_3328_);
lean_inc(v_a_3339_);
v___x_3358_ = lean_whnf(v_a_3339_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
v___y_3275_ = v___y_3328_;
v___y_3276_ = v___y_3331_;
v___y_3277_ = v___y_3329_;
v___y_3278_ = v_a_3339_;
v___y_3279_ = v_isHEq_3327_;
v___y_3280_ = v___y_3330_;
v___y_3281_ = v___y_3326_;
v___y_3282_ = v___x_3358_;
goto v___jp_3274_;
}
}
else
{
lean_object* v_a_3359_; 
v_a_3359_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3338_, 1);
v___y_3263_ = v___y_3328_;
v___y_3264_ = v___y_3331_;
v___y_3265_ = v___y_3329_;
v___y_3266_ = v_isHEq_3327_;
v___y_3267_ = v___y_3330_;
v___y_3268_ = v___y_3326_;
v_a_3269_ = v_a_3359_;
goto v___jp_3262_;
}
}
else
{
v___y_3239_ = v_isHEq_3327_;
v___y_3240_ = v___y_3326_;
v___y_3241_ = v___y_3328_;
v___y_3242_ = v___y_3329_;
v___y_3243_ = v___y_3330_;
v___y_3244_ = v___y_3331_;
goto v___jp_3238_;
}
}
else
{
lean_dec(v_a_3335_);
v___y_3239_ = v_isHEq_3327_;
v___y_3240_ = v___y_3326_;
v___y_3241_ = v___y_3328_;
v___y_3242_ = v___y_3329_;
v___y_3243_ = v___y_3330_;
v___y_3244_ = v___y_3331_;
goto v___jp_3238_;
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3360_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3334_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3334_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
else
{
v___y_3239_ = v_isHEq_3327_;
v___y_3240_ = v___y_3326_;
v___y_3241_ = v___y_3328_;
v___y_3242_ = v___y_3329_;
v___y_3243_ = v___y_3330_;
v___y_3244_ = v___y_3331_;
goto v___jp_3238_;
}
}
}
v___jp_3368_:
{
lean_object* v___x_3374_; 
lean_inc_ref(v___x_3237_);
v___x_3374_ = l_Lean_Meta_matchHEq_x3f(v___x_3237_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
if (lean_obj_tag(v_a_3375_) == 1)
{
lean_object* v_val_3376_; lean_object* v_snd_3377_; lean_object* v_snd_3378_; lean_object* v_fst_3379_; lean_object* v_fst_3380_; lean_object* v_fst_3381_; lean_object* v_snd_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3482_; 
v_val_3376_ = lean_ctor_get(v_a_3375_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v_a_3375_, 1);
v_snd_3377_ = lean_ctor_get(v_val_3376_, 1);
lean_inc(v_snd_3377_);
v_snd_3378_ = lean_ctor_get(v_snd_3377_, 1);
lean_inc(v_snd_3378_);
v_fst_3379_ = lean_ctor_get(v_val_3376_, 0);
lean_inc(v_fst_3379_);
lean_dec(v_val_3376_);
v_fst_3380_ = lean_ctor_get(v_snd_3377_, 0);
lean_inc(v_fst_3380_);
lean_dec(v_snd_3377_);
v_fst_3381_ = lean_ctor_get(v_snd_3378_, 0);
v_snd_3382_ = lean_ctor_get(v_snd_3378_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_snd_3378_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3384_ = v_snd_3378_;
v_isShared_3385_ = v_isSharedCheck_3482_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_snd_3382_);
lean_inc(v_fst_3381_);
lean_dec(v_snd_3378_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3482_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3380_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
if (lean_obj_tag(v_a_3387_) == 1)
{
lean_object* v_val_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3473_; 
v_val_3388_ = lean_ctor_get(v_a_3387_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_a_3387_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3390_ = v_a_3387_;
v_isShared_3391_ = v_isSharedCheck_3473_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_val_3388_);
lean_dec(v_a_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3473_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3382_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
if (lean_obj_tag(v_a_3393_) == 1)
{
lean_object* v_toConstantVal_3394_; lean_object* v_val_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3464_; 
v_toConstantVal_3394_ = lean_ctor_get(v_val_3388_, 0);
lean_inc_ref(v_toConstantVal_3394_);
lean_dec(v_val_3388_);
v_val_3395_ = lean_ctor_get(v_a_3393_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_a_3393_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3397_ = v_a_3393_;
v_isShared_3398_ = v_isSharedCheck_3464_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_val_3395_);
lean_dec(v_a_3393_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3464_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_toConstantVal_3399_; lean_object* v_name_3400_; lean_object* v_name_3401_; uint8_t v___x_3402_; 
v_toConstantVal_3399_ = lean_ctor_get(v_val_3395_, 0);
lean_inc_ref(v_toConstantVal_3399_);
lean_dec(v_val_3395_);
v_name_3400_ = lean_ctor_get(v_toConstantVal_3394_, 0);
lean_inc(v_name_3400_);
lean_dec_ref(v_toConstantVal_3394_);
v_name_3401_ = lean_ctor_get(v_toConstantVal_3399_, 0);
lean_inc(v_name_3401_);
lean_dec_ref(v_toConstantVal_3399_);
v___x_3402_ = lean_name_eq(v_name_3400_, v_name_3401_);
lean_dec(v_name_3401_);
lean_dec(v_name_3400_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_Meta_isExprDefEq(v_fst_3379_, v_fst_3381_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; uint8_t v___x_3405_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3403_, 1);
v___x_3405_ = lean_unbox(v_a_3404_);
lean_dec(v_a_3404_);
if (v___x_3405_ == 0)
{
lean_del_object(v___x_3397_);
lean_del_object(v___x_3390_);
lean_del_object(v___x_3384_);
v___y_3326_ = v_isEq_3369_;
v_isHEq_3327_ = v___x_3182_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
v___y_3331_ = v___y_3373_;
goto v___jp_3325_;
}
else
{
lean_object* v___x_3406_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec_ref(v_config_3171_);
lean_inc(v_mvarId_3172_);
v___x_3406_ = l_Lean_MVarId_getType(v_mvarId_3172_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v___x_3408_ = l_Lean_LocalDecl_toExpr(v_val_3203_);
v___x_3409_ = l_Lean_Meta_mkEqOfHEq(v___x_3408_, v___x_3182_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3411_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3409_, 1);
v___x_3411_ = l_Lean_Meta_mkNoConfusion(v_a_3407_, v_a_3410_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v___x_3413_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v___x_3413_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3172_, v_a_3412_, v___y_3371_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec_ref_known(v___x_3413_, 1);
v___x_3414_ = lean_box(v___x_3182_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3414_);
v___x_3416_ = v___x_3397_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3418_; 
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 1, v___x_3207_);
lean_ctor_set(v___x_3384_, 0, v___x_3416_);
v___x_3418_ = v___x_3384_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v___x_3207_);
v___x_3418_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3418_);
v___x_3420_ = v___x_3390_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
v_a_3189_ = v___x_3420_;
goto v___jp_3188_;
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_del_object(v___x_3397_);
lean_del_object(v___x_3390_);
lean_del_object(v___x_3384_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3424_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3413_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3413_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_del_object(v___x_3397_);
lean_del_object(v___x_3390_);
lean_del_object(v___x_3384_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3432_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3411_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3411_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_a_3407_);
lean_del_object(v___x_3397_);
lean_del_object(v___x_3390_);
lean_del_object(v___x_3384_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3440_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3409_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3409_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_del_object(v___x_3397_);
lean_del_object(v___x_3390_);
lean_del_object(v___x_3384_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3448_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3406_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3406_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_del_object(v___x_3397_);
lean_del_object(v___x_3390_);
lean_del_object(v___x_3384_);
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3456_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3403_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3403_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_del_object(v___x_3397_);
lean_del_object(v___x_3390_);
lean_del_object(v___x_3384_);
lean_dec(v_fst_3381_);
lean_dec(v_fst_3379_);
v___y_3326_ = v_isEq_3369_;
v_isHEq_3327_ = v___x_3182_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
v___y_3331_ = v___y_3373_;
goto v___jp_3325_;
}
}
}
else
{
lean_dec(v_a_3393_);
lean_del_object(v___x_3390_);
lean_dec(v_val_3388_);
lean_del_object(v___x_3384_);
lean_dec(v_fst_3381_);
lean_dec(v_fst_3379_);
v___y_3326_ = v_isEq_3369_;
v_isHEq_3327_ = v___x_3182_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
v___y_3331_ = v___y_3373_;
goto v___jp_3325_;
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_del_object(v___x_3390_);
lean_dec(v_val_3388_);
lean_del_object(v___x_3384_);
lean_dec(v_fst_3381_);
lean_dec(v_fst_3379_);
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3465_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3392_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3392_);
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
}
else
{
lean_dec(v_a_3387_);
lean_del_object(v___x_3384_);
lean_dec(v_snd_3382_);
lean_dec(v_fst_3381_);
lean_dec(v_fst_3379_);
v___y_3326_ = v_isEq_3369_;
v_isHEq_3327_ = v___x_3182_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
v___y_3331_ = v___y_3373_;
goto v___jp_3325_;
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_del_object(v___x_3384_);
lean_dec(v_snd_3382_);
lean_dec(v_fst_3381_);
lean_dec(v_fst_3379_);
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3474_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3386_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3386_);
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
}
else
{
lean_dec(v_a_3375_);
v___y_3326_ = v_isEq_3369_;
v_isHEq_3327_ = v___x_3236_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
v___y_3331_ = v___y_3373_;
goto v___jp_3325_;
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3483_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3374_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3374_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
v___jp_3491_:
{
lean_object* v___x_3496_; 
lean_inc_ref(v___x_3237_);
v___x_3496_ = l_Lean_Meta_matchEq_x3f(v___x_3237_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
if (lean_obj_tag(v_a_3497_) == 1)
{
lean_object* v_val_3498_; lean_object* v_snd_3499_; lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3580_; 
v_val_3498_ = lean_ctor_get(v_a_3497_, 0);
lean_inc(v_val_3498_);
lean_dec_ref_known(v_a_3497_, 1);
v_snd_3499_ = lean_ctor_get(v_val_3498_, 1);
lean_inc(v_snd_3499_);
lean_dec(v_val_3498_);
v_fst_3500_ = lean_ctor_get(v_snd_3499_, 0);
v_snd_3501_ = lean_ctor_get(v_snd_3499_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_snd_3499_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3503_ = v_snd_3499_;
v_isShared_3504_ = v_isSharedCheck_3580_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_snd_3501_);
lean_inc(v_fst_3500_);
lean_dec(v_snd_3499_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3580_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3500_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
if (lean_obj_tag(v_a_3506_) == 1)
{
lean_object* v_val_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3571_; 
v_val_3507_ = lean_ctor_get(v_a_3506_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_a_3506_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3509_ = v_a_3506_;
v_isShared_3510_ = v_isSharedCheck_3571_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_val_3507_);
lean_dec(v_a_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3571_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3501_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
if (lean_obj_tag(v_a_3512_) == 1)
{
lean_object* v_toConstantVal_3513_; lean_object* v_val_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3562_; 
v_toConstantVal_3513_ = lean_ctor_get(v_val_3507_, 0);
lean_inc_ref(v_toConstantVal_3513_);
lean_dec(v_val_3507_);
v_val_3514_ = lean_ctor_get(v_a_3512_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_a_3512_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3516_ = v_a_3512_;
v_isShared_3517_ = v_isSharedCheck_3562_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_val_3514_);
lean_dec(v_a_3512_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3562_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v_toConstantVal_3518_; lean_object* v_name_3519_; lean_object* v_name_3520_; uint8_t v___x_3521_; 
v_toConstantVal_3518_ = lean_ctor_get(v_val_3514_, 0);
lean_inc_ref(v_toConstantVal_3518_);
lean_dec(v_val_3514_);
v_name_3519_ = lean_ctor_get(v_toConstantVal_3513_, 0);
lean_inc(v_name_3519_);
lean_dec_ref(v_toConstantVal_3513_);
v_name_3520_ = lean_ctor_get(v_toConstantVal_3518_, 0);
lean_inc(v_name_3520_);
lean_dec_ref(v_toConstantVal_3518_);
v___x_3521_ = lean_name_eq(v_name_3519_, v_name_3520_);
lean_dec(v_name_3520_);
lean_dec(v_name_3519_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec_ref(v_config_3171_);
lean_inc(v_mvarId_3172_);
v___x_3522_ = l_Lean_MVarId_getType(v_mvarId_3172_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3522_, 1);
v___x_3524_ = l_Lean_LocalDecl_toExpr(v_val_3203_);
v___x_3525_ = l_Lean_Meta_mkNoConfusion(v_a_3523_, v___x_3524_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3527_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref_known(v___x_3525_, 1);
v___x_3527_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3172_, v_a_3526_, v___y_3493_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3530_; 
lean_dec_ref_known(v___x_3527_, 1);
v___x_3528_ = lean_box(v___x_3182_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3528_);
v___x_3530_ = v___x_3516_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3532_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 1, v___x_3207_);
lean_ctor_set(v___x_3503_, 0, v___x_3530_);
v___x_3532_ = v___x_3503_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3207_);
v___x_3532_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3534_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set_tag(v___x_3509_, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3532_);
v___x_3534_ = v___x_3509_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
v_a_3189_ = v___x_3534_;
goto v___jp_3188_;
}
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_del_object(v___x_3516_);
lean_del_object(v___x_3509_);
lean_del_object(v___x_3503_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3538_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3527_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3527_);
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
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_del_object(v___x_3516_);
lean_del_object(v___x_3509_);
lean_del_object(v___x_3503_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3546_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3525_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3525_);
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
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_del_object(v___x_3516_);
lean_del_object(v___x_3509_);
lean_del_object(v___x_3503_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3554_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3522_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3522_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
else
{
lean_del_object(v___x_3516_);
lean_del_object(v___x_3509_);
lean_del_object(v___x_3503_);
v_isEq_3369_ = v___x_3182_;
v___y_3370_ = v___y_3492_;
v___y_3371_ = v___y_3493_;
v___y_3372_ = v___y_3494_;
v___y_3373_ = v___y_3495_;
goto v___jp_3368_;
}
}
}
else
{
lean_dec(v_a_3512_);
lean_del_object(v___x_3509_);
lean_dec(v_val_3507_);
lean_del_object(v___x_3503_);
v_isEq_3369_ = v___x_3182_;
v___y_3370_ = v___y_3492_;
v___y_3371_ = v___y_3493_;
v___y_3372_ = v___y_3494_;
v___y_3373_ = v___y_3495_;
goto v___jp_3368_;
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_del_object(v___x_3509_);
lean_dec(v_val_3507_);
lean_del_object(v___x_3503_);
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3563_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3511_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3511_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
else
{
lean_dec(v_a_3506_);
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
v_isEq_3369_ = v___x_3182_;
v___y_3370_ = v___y_3492_;
v___y_3371_ = v___y_3493_;
v___y_3372_ = v___y_3494_;
v___y_3373_ = v___y_3495_;
goto v___jp_3368_;
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3572_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3505_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3505_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
else
{
lean_dec(v_a_3497_);
v_isEq_3369_ = v___x_3236_;
v___y_3370_ = v___y_3492_;
v___y_3371_ = v___y_3493_;
v___y_3372_ = v___y_3494_;
v___y_3373_ = v___y_3495_;
goto v___jp_3368_;
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3581_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3496_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3496_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
v___jp_3589_:
{
lean_object* v___x_3594_; 
lean_inc_ref(v___x_3237_);
v___x_3594_ = l_Lean_refutableHasNotBit_x3f(v___x_3237_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
if (lean_obj_tag(v_a_3595_) == 1)
{
lean_object* v_val_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3636_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec_ref(v_config_3171_);
v_val_3596_ = lean_ctor_get(v_a_3595_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_a_3595_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3598_ = v_a_3595_;
v_isShared_3599_ = v_isSharedCheck_3636_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_val_3596_);
lean_dec(v_a_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3636_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; 
lean_inc(v_mvarId_3172_);
v___x_3600_ = l_Lean_MVarId_getType(v_mvarId_3172_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = l_Lean_LocalDecl_toExpr(v_val_3203_);
v___x_3603_ = l_Lean_Meta_mkAbsurd(v_a_3601_, v_val_3596_, v___x_3602_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
v___x_3605_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3172_, v_a_3604_, v___y_3591_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
lean_dec_ref_known(v___x_3605_, 1);
v___x_3606_ = lean_box(v___x_3182_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v___x_3606_);
v___x_3608_ = v___x_3598_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
lean_ctor_set(v___x_3609_, 1, v___x_3207_);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
v_a_3189_ = v___x_3610_;
goto v___jp_3188_;
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_del_object(v___x_3598_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3612_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3605_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3605_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_del_object(v___x_3598_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3620_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3603_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3603_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_del_object(v___x_3598_);
lean_dec(v_val_3596_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3628_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3600_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3600_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
else
{
lean_object* v___x_3637_; 
lean_dec(v_a_3595_);
lean_inc_ref(v___x_3237_);
v___x_3637_ = l_Lean_Meta_matchNe_x3f(v___x_3237_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
if (lean_obj_tag(v_a_3638_) == 1)
{
lean_object* v_val_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3709_; 
v_val_3639_ = lean_ctor_get(v_a_3638_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_a_3638_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3641_ = v_a_3638_;
v_isShared_3642_ = v_isSharedCheck_3709_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_val_3639_);
lean_dec(v_a_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3709_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v_snd_3643_; lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3708_; 
v_snd_3643_ = lean_ctor_get(v_val_3639_, 1);
lean_inc(v_snd_3643_);
lean_dec(v_val_3639_);
v_fst_3644_ = lean_ctor_get(v_snd_3643_, 0);
v_snd_3645_ = lean_ctor_get(v_snd_3643_, 1);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_snd_3643_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3647_ = v_snd_3643_;
v_isShared_3648_ = v_isSharedCheck_3708_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_snd_3645_);
lean_inc(v_fst_3644_);
lean_dec(v_snd_3643_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3708_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; 
lean_inc(v_fst_3644_);
v___x_3649_ = l_Lean_Meta_isExprDefEq(v_fst_3644_, v_snd_3645_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; uint8_t v___x_3651_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v___x_3651_ = lean_unbox(v_a_3650_);
lean_dec(v_a_3650_);
if (v___x_3651_ == 0)
{
lean_del_object(v___x_3647_);
lean_dec(v_fst_3644_);
lean_del_object(v___x_3641_);
v___y_3492_ = v___y_3590_;
v___y_3493_ = v___y_3591_;
v___y_3494_ = v___y_3592_;
v___y_3495_ = v___y_3593_;
goto v___jp_3491_;
}
else
{
lean_object* v___x_3652_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec_ref(v_config_3171_);
lean_inc(v_mvarId_3172_);
v___x_3652_ = l_Lean_MVarId_getType(v_mvarId_3172_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3654_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3652_, 1);
v___x_3654_ = l_Lean_Meta_mkEqRefl(v_fst_3644_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3654_, 1);
v___x_3656_ = l_Lean_LocalDecl_toExpr(v_val_3203_);
v___x_3657_ = l_Lean_Meta_mkAbsurd(v_a_3653_, v_a_3655_, v___x_3656_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3659_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v___x_3657_, 1);
v___x_3659_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3172_, v_a_3658_, v___y_3591_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3662_; 
lean_dec_ref_known(v___x_3659_, 1);
v___x_3660_ = lean_box(v___x_3182_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3660_);
v___x_3662_ = v___x_3641_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 1, v___x_3207_);
lean_ctor_set(v___x_3647_, 0, v___x_3662_);
v___x_3664_ = v___x_3647_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3207_);
v___x_3664_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; 
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
v_a_3189_ = v___x_3665_;
goto v___jp_3188_;
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_del_object(v___x_3647_);
lean_del_object(v___x_3641_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3668_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3659_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3659_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_del_object(v___x_3647_);
lean_del_object(v___x_3641_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3676_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3657_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3657_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec(v_a_3653_);
lean_del_object(v___x_3647_);
lean_del_object(v___x_3641_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3684_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3654_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3654_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_del_object(v___x_3647_);
lean_dec(v_fst_3644_);
lean_del_object(v___x_3641_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
v_a_3692_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3652_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3652_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_del_object(v___x_3647_);
lean_dec(v_fst_3644_);
lean_del_object(v___x_3641_);
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3700_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3649_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3649_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3638_);
v___y_3492_ = v___y_3590_;
v___y_3493_ = v___y_3591_;
v___y_3494_ = v___y_3592_;
v___y_3495_ = v___y_3593_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3710_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3637_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3637_);
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
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v___x_3237_);
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3718_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3594_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3594_);
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
}
else
{
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3197_ = v___x_3208_;
goto v___jp_3196_;
}
v___jp_3209_:
{
uint8_t v_emptyType_3216_; 
v_emptyType_3216_ = lean_ctor_get_uint8(v_config_3171_, sizeof(void*)*1 + 1);
if (v_emptyType_3216_ == 0)
{
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3197_ = v___x_3208_;
goto v___jp_3196_;
}
else
{
if (v___y_3211_ == 0)
{
if (v___y_3210_ == 0)
{
lean_object* v_searchFuel_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v_searchFuel_3217_ = lean_ctor_get(v_config_3171_, 0);
v___x_3218_ = l_Lean_LocalDecl_fvarId(v_val_3203_);
lean_dec(v_val_3203_);
lean_inc(v_searchFuel_3217_);
lean_inc(v_mvarId_3172_);
v___x_3219_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_3172_, v___x_3218_, v_searchFuel_3217_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; uint8_t v___x_3221_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___x_3221_ = lean_unbox(v_a_3220_);
lean_dec(v_a_3220_);
if (v___x_3221_ == 0)
{
lean_del_object(v___x_3205_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3197_ = v___x_3208_;
goto v___jp_3196_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v___x_3222_ = lean_box(v___x_3182_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3222_);
v___x_3224_ = v___x_3205_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___x_3207_);
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
v_a_3189_ = v___x_3226_;
goto v___jp_3188_;
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_del_object(v___x_3205_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
lean_dec(v_mvarId_3172_);
lean_dec_ref(v_config_3171_);
v_a_3228_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3219_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3219_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
else
{
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3197_ = v___x_3208_;
goto v___jp_3196_;
}
}
else
{
lean_del_object(v___x_3205_);
lean_dec(v_val_3203_);
lean_del_object(v___x_3186_);
lean_dec(v_snd_3184_);
v_a_3197_ = v___x_3208_;
goto v___jp_3196_;
}
}
}
}
}
v___jp_3188_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v_a_3189_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v___x_3190_);
v___x_3192_ = v___x_3186_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_snd_3184_);
v___x_3192_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; 
v___x_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
return v___x_3193_;
}
}
v___jp_3196_:
{
lean_object* v___x_3198_; size_t v___x_3199_; size_t v___x_3200_; 
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3195_);
lean_ctor_set(v___x_3198_, 1, v_a_3197_);
v___x_3199_ = ((size_t)1ULL);
v___x_3200_ = lean_usize_add(v_i_3175_, v___x_3199_);
v_i_3175_ = v___x_3200_;
v_b_3176_ = v___x_3198_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3799_, lean_object* v_mvarId_3800_, lean_object* v_as_3801_, lean_object* v_sz_3802_, lean_object* v_i_3803_, lean_object* v_b_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
size_t v_sz_boxed_3810_; size_t v_i_boxed_3811_; lean_object* v_res_3812_; 
v_sz_boxed_3810_ = lean_unbox_usize(v_sz_3802_);
lean_dec(v_sz_3802_);
v_i_boxed_3811_ = lean_unbox_usize(v_i_3803_);
lean_dec(v_i_3803_);
v_res_3812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3799_, v_mvarId_3800_, v_as_3801_, v_sz_boxed_3810_, v_i_boxed_3811_, v_b_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec_ref(v_as_3801_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3813_, lean_object* v_mvarId_3814_, lean_object* v_as_3815_, size_t v_sz_3816_, size_t v_i_3817_, lean_object* v_b_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
uint8_t v___x_3824_; 
v___x_3824_ = lean_usize_dec_lt(v_i_3817_, v_sz_3816_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; 
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v___x_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3825_, 0, v_b_3818_);
return v___x_3825_;
}
else
{
lean_object* v_snd_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_4439_; 
v_snd_3826_ = lean_ctor_get(v_b_3818_, 1);
v_isSharedCheck_4439_ = !lean_is_exclusive(v_b_3818_);
if (v_isSharedCheck_4439_ == 0)
{
lean_object* v_unused_4440_; 
v_unused_4440_ = lean_ctor_get(v_b_3818_, 0);
lean_dec(v_unused_4440_);
v___x_3828_ = v_b_3818_;
v_isShared_3829_ = v_isSharedCheck_4439_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_snd_3826_);
lean_dec(v_b_3818_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_4439_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v_a_3831_; lean_object* v___x_3837_; lean_object* v_a_3839_; lean_object* v_a_3844_; 
v___x_3837_ = lean_box(0);
v_a_3844_ = lean_array_uget(v_as_3815_, v_i_3817_);
if (lean_obj_tag(v_a_3844_) == 0)
{
lean_del_object(v___x_3828_);
v_a_3839_ = v_snd_3826_;
goto v___jp_3838_;
}
else
{
lean_object* v_val_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_4438_; 
v_val_3845_ = lean_ctor_get(v_a_3844_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v_a_3844_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_3847_ = v_a_3844_;
v_isShared_3848_ = v_isSharedCheck_4438_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_val_3845_);
lean_dec(v_a_3844_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_4438_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___y_3852_; uint8_t v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; uint8_t v___x_3878_; 
v___x_3849_ = lean_box(0);
v___x_3850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3878_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3845_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; uint8_t v___y_3881_; uint8_t v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; uint8_t v___y_3905_; uint8_t v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v_a_3911_; lean_object* v___y_3917_; uint8_t v___y_3918_; uint8_t v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; uint8_t v___y_3968_; uint8_t v_isHEq_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; uint8_t v_isEq_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___x_4368_; 
v___x_3879_ = l_Lean_LocalDecl_type(v_val_3845_);
lean_inc_ref(v___x_3879_);
v___x_4368_ = l_Lean_Meta_matchNot_x3f(v___x_3879_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4368_, 1);
if (lean_obj_tag(v_a_4369_) == 1)
{
lean_object* v_val_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4429_; 
v_val_4370_ = lean_ctor_get(v_a_4369_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v_a_4369_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4372_ = v_a_4369_;
v_isShared_4373_ = v_isSharedCheck_4429_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_val_4370_);
lean_dec(v_a_4369_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4429_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4370_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref_known(v___x_4374_, 1);
if (lean_obj_tag(v_a_4375_) == 1)
{
lean_object* v_val_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4420_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec_ref(v_config_3813_);
v_val_4376_ = lean_ctor_get(v_a_4375_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v_a_4375_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4378_ = v_a_4375_;
v_isShared_4379_ = v_isSharedCheck_4420_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_val_4376_);
lean_dec(v_a_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4420_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; 
lean_inc(v_mvarId_3814_);
v___x_4380_ = l_Lean_MVarId_getType(v_mvarId_3814_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4381_);
lean_dec_ref_known(v___x_4380_, 1);
v___x_4382_ = l_Lean_LocalDecl_toExpr(v_val_3845_);
v___x_4383_ = l_Lean_mkFVar(v_val_4376_);
v___x_4384_ = l_Lean_Expr_app___override(v___x_4382_, v___x_4383_);
v___x_4385_ = l_Lean_Meta_mkFalseElim(v_a_4381_, v___x_4384_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4387_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___x_4385_, 1);
v___x_4387_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3814_, v_a_4386_, v___y_3820_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v___x_4388_; lean_object* v___x_4390_; 
lean_dec_ref_known(v___x_4387_, 1);
v___x_4388_ = lean_box(v___x_3824_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4388_);
v___x_4390_ = v___x_4378_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4388_);
v___x_4390_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4393_; 
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
lean_ctor_set(v___x_4391_, 1, v___x_3849_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set_tag(v___x_4372_, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4391_);
v___x_4393_ = v___x_4372_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
v_a_3831_ = v___x_4393_;
goto v___jp_3830_;
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_del_object(v___x_4378_);
lean_del_object(v___x_4372_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_4396_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4387_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4387_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_del_object(v___x_4378_);
lean_del_object(v___x_4372_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4404_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4385_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4385_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_del_object(v___x_4378_);
lean_dec(v_val_4376_);
lean_del_object(v___x_4372_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4412_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4380_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4380_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
else
{
lean_dec(v_a_4375_);
lean_del_object(v___x_4372_);
v___y_4232_ = v___y_3819_;
v___y_4233_ = v___y_3820_;
v___y_4234_ = v___y_3821_;
v___y_4235_ = v___y_3822_;
goto v___jp_4231_;
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_del_object(v___x_4372_);
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4421_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4374_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4374_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
else
{
lean_dec(v_a_4369_);
v___y_4232_ = v___y_3819_;
v___y_4233_ = v___y_3820_;
v___y_4234_ = v___y_3821_;
v___y_4235_ = v___y_3822_;
goto v___jp_4231_;
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4430_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4368_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4368_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
v___jp_3880_:
{
uint8_t v_genDiseq_3887_; 
v_genDiseq_3887_ = lean_ctor_get_uint8(v_config_3813_, sizeof(void*)*1 + 2);
if (v_genDiseq_3887_ == 0)
{
lean_dec_ref(v___x_3879_);
v___y_3852_ = v___y_3881_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3884_;
v___y_3856_ = v___y_3885_;
v___y_3857_ = v___y_3886_;
goto v___jp_3851_;
}
else
{
uint8_t v___x_3888_; 
v___x_3888_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3879_);
lean_dec_ref(v___x_3879_);
if (v___x_3888_ == 0)
{
v___y_3852_ = v___y_3881_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3884_;
v___y_3856_ = v___y_3885_;
v___y_3857_ = v___y_3886_;
goto v___jp_3851_;
}
else
{
lean_object* v___x_3889_; 
lean_inc(v_val_3845_);
lean_inc(v_mvarId_3814_);
v___x_3889_ = l_Lean_Meta_processGenDiseq(v_mvarId_3814_, v_val_3845_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; uint8_t v___x_3891_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
v___x_3891_ = lean_unbox(v_a_3890_);
lean_dec(v_a_3890_);
if (v___x_3891_ == 0)
{
v___y_3852_ = v___y_3881_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3884_;
v___y_3856_ = v___y_3885_;
v___y_3857_ = v___y_3886_;
goto v___jp_3851_;
}
else
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v___x_3892_ = lean_box(v___x_3824_);
v___x_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
v___x_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
lean_ctor_set(v___x_3894_, 1, v___x_3849_);
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
v_a_3831_ = v___x_3895_;
goto v___jp_3830_;
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_3896_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3889_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3889_);
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
}
}
v___jp_3904_:
{
uint8_t v___x_3912_; 
v___x_3912_ = l_Lean_Exception_isInterrupt(v_a_3911_);
if (v___x_3912_ == 0)
{
uint8_t v___x_3913_; 
lean_inc_ref(v_a_3911_);
v___x_3913_ = l_Lean_Exception_isRuntime(v_a_3911_);
if (v___x_3913_ == 0)
{
lean_dec_ref(v_a_3911_);
v___y_3881_ = v___y_3905_;
v___y_3882_ = v___y_3906_;
v___y_3883_ = v___y_3907_;
v___y_3884_ = v___y_3909_;
v___y_3885_ = v___y_3910_;
v___y_3886_ = v___y_3908_;
goto v___jp_3880_;
}
else
{
lean_object* v___x_3914_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v___x_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3914_, 0, v_a_3911_);
return v___x_3914_;
}
}
else
{
lean_object* v___x_3915_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v___x_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3915_, 0, v_a_3911_);
return v___x_3915_;
}
}
v___jp_3916_:
{
if (lean_obj_tag(v___y_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; 
v_a_3925_ = lean_ctor_get(v___y_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___y_3924_, 1);
v___x_3926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3927_ = l_Lean_Expr_isConstOf(v_a_3925_, v___x_3926_);
lean_dec(v_a_3925_);
if (v___x_3927_ == 0)
{
lean_dec_ref(v___y_3917_);
v___y_3881_ = v___y_3918_;
v___y_3882_ = v___y_3919_;
v___y_3883_ = v___y_3920_;
v___y_3884_ = v___y_3922_;
v___y_3885_ = v___y_3923_;
v___y_3886_ = v___y_3921_;
goto v___jp_3880_;
}
else
{
lean_object* v___x_3928_; 
lean_inc_ref(v___y_3917_);
v___x_3928_ = l_Lean_Meta_mkEqRefl(v___y_3917_, v___y_3920_, v___y_3922_, v___y_3923_, v___y_3921_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; lean_object* v_dummy_3931_; lean_object* v_nargs_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3930_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3932_ = l_Lean_Expr_getAppNumArgs(v___y_3917_);
lean_inc(v_nargs_3932_);
v___x_3933_ = lean_mk_array(v_nargs_3932_, v_dummy_3931_);
v___x_3934_ = lean_unsigned_to_nat(1u);
v___x_3935_ = lean_nat_sub(v_nargs_3932_, v___x_3934_);
lean_dec(v_nargs_3932_);
v___x_3936_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3917_, v___x_3933_, v___x_3935_);
v___x_3937_ = lean_array_push(v___x_3936_, v_a_3929_);
v___x_3938_ = l_Lean_mkAppN(v___x_3930_, v___x_3937_);
lean_dec_ref(v___x_3937_);
lean_inc(v_mvarId_3814_);
v___x_3939_ = l_Lean_MVarId_getType(v_mvarId_3814_, v___y_3920_, v___y_3922_, v___y_3923_, v___y_3921_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
lean_inc(v_val_3845_);
v___x_3941_ = l_Lean_LocalDecl_toExpr(v_val_3845_);
v___x_3942_ = l_Lean_Meta_mkAbsurd(v_a_3940_, v___x_3941_, v___x_3938_, v___y_3920_, v___y_3922_, v___y_3923_, v___y_3921_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3962_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3962_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3962_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; 
lean_inc(v_mvarId_3814_);
v___x_3947_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3814_, v_a_3943_, v___y_3922_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3959_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3959_ == 0)
{
lean_object* v_unused_3960_; 
v_unused_3960_ = lean_ctor_get(v___x_3947_, 0);
lean_dec(v_unused_3960_);
v___x_3949_ = v___x_3947_;
v_isShared_3950_ = v_isSharedCheck_3959_;
goto v_resetjp_3948_;
}
else
{
lean_dec(v___x_3947_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3959_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3951_; lean_object* v___x_3953_; 
v___x_3951_ = lean_box(v___x_3824_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set_tag(v___x_3949_, 1);
lean_ctor_set(v___x_3949_, 0, v___x_3951_);
v___x_3953_ = v___x_3949_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3954_; lean_object* v___x_3956_; 
v___x_3954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
lean_ctor_set(v___x_3954_, 1, v___x_3849_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3954_);
v___x_3956_ = v___x_3945_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
v_a_3831_ = v___x_3956_;
goto v___jp_3830_;
}
}
}
}
else
{
lean_object* v_a_3961_; 
lean_del_object(v___x_3945_);
v_a_3961_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___x_3947_, 1);
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v___y_3910_ = v___y_3923_;
v_a_3911_ = v_a_3961_;
goto v___jp_3904_;
}
}
}
else
{
lean_object* v_a_3963_; 
v_a_3963_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3942_, 1);
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v___y_3910_ = v___y_3923_;
v_a_3911_ = v_a_3963_;
goto v___jp_3904_;
}
}
else
{
lean_object* v_a_3964_; 
lean_dec_ref(v___x_3938_);
v_a_3964_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3939_, 1);
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v___y_3910_ = v___y_3923_;
v_a_3911_ = v_a_3964_;
goto v___jp_3904_;
}
}
else
{
lean_object* v_a_3965_; 
lean_dec_ref(v___y_3917_);
v_a_3965_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3928_, 1);
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v___y_3910_ = v___y_3923_;
v_a_3911_ = v_a_3965_;
goto v___jp_3904_;
}
}
}
else
{
lean_object* v_a_3966_; 
lean_dec_ref(v___y_3917_);
v_a_3966_ = lean_ctor_get(v___y_3924_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___y_3924_, 1);
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v___y_3910_ = v___y_3923_;
v_a_3911_ = v_a_3966_;
goto v___jp_3904_;
}
}
v___jp_3967_:
{
uint8_t v_useDecide_3974_; 
v_useDecide_3974_ = lean_ctor_get_uint8(v_config_3813_, sizeof(void*)*1);
if (v_useDecide_3974_ == 0)
{
v___y_3881_ = v___y_3968_;
v___y_3882_ = v_isHEq_3969_;
v___y_3883_ = v___y_3970_;
v___y_3884_ = v___y_3971_;
v___y_3885_ = v___y_3972_;
v___y_3886_ = v___y_3973_;
goto v___jp_3880_;
}
else
{
uint8_t v___x_3975_; 
v___x_3975_ = l_Lean_Expr_hasFVar(v___x_3879_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; 
lean_inc_ref(v___x_3879_);
v___x_3976_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_3879_, v___y_3971_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; uint8_t v___x_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = l_Lean_Expr_hasMVar(v_a_3977_);
if (v___x_3978_ == 0)
{
uint8_t v___x_3979_; 
v___x_3979_ = l_Lean_Expr_hasFVar(v_a_3977_);
lean_dec(v_a_3977_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; 
lean_inc_ref(v___x_3879_);
v___x_3980_ = l_Lean_Meta_mkDecide(v___x_3879_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3982_; uint8_t v_transparency_3983_; uint8_t v___x_3984_; uint8_t v___x_3985_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v___x_3980_, 1);
v___x_3982_ = l_Lean_Meta_Context_config(v___y_3970_);
v_transparency_3983_ = lean_ctor_get_uint8(v___x_3982_, 9);
lean_dec_ref(v___x_3982_);
v___x_3984_ = 1;
v___x_3985_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3983_, v___x_3984_);
if (v___x_3985_ == 0)
{
lean_object* v_keyedConfig_3986_; uint8_t v_trackZetaDelta_3987_; lean_object* v_zetaDeltaSet_3988_; lean_object* v_lctx_3989_; lean_object* v_localInstances_3990_; lean_object* v_defEqCtx_x3f_3991_; lean_object* v_synthPendingDepth_3992_; lean_object* v_customCanUnfoldPredicate_x3f_3993_; uint8_t v_univApprox_3994_; uint8_t v_inTypeClassResolution_3995_; uint8_t v_cacheInferType_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_keyedConfig_3986_ = lean_ctor_get(v___y_3970_, 0);
v_trackZetaDelta_3987_ = lean_ctor_get_uint8(v___y_3970_, sizeof(void*)*7);
v_zetaDeltaSet_3988_ = lean_ctor_get(v___y_3970_, 1);
v_lctx_3989_ = lean_ctor_get(v___y_3970_, 2);
v_localInstances_3990_ = lean_ctor_get(v___y_3970_, 3);
v_defEqCtx_x3f_3991_ = lean_ctor_get(v___y_3970_, 4);
v_synthPendingDepth_3992_ = lean_ctor_get(v___y_3970_, 5);
v_customCanUnfoldPredicate_x3f_3993_ = lean_ctor_get(v___y_3970_, 6);
v_univApprox_3994_ = lean_ctor_get_uint8(v___y_3970_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3995_ = lean_ctor_get_uint8(v___y_3970_, sizeof(void*)*7 + 2);
v_cacheInferType_3996_ = lean_ctor_get_uint8(v___y_3970_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3986_);
v___x_3997_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3984_, v_keyedConfig_3986_);
lean_inc(v_customCanUnfoldPredicate_x3f_3993_);
lean_inc(v_synthPendingDepth_3992_);
lean_inc(v_defEqCtx_x3f_3991_);
lean_inc_ref(v_localInstances_3990_);
lean_inc_ref(v_lctx_3989_);
lean_inc(v_zetaDeltaSet_3988_);
v___x_3998_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
lean_ctor_set(v___x_3998_, 1, v_zetaDeltaSet_3988_);
lean_ctor_set(v___x_3998_, 2, v_lctx_3989_);
lean_ctor_set(v___x_3998_, 3, v_localInstances_3990_);
lean_ctor_set(v___x_3998_, 4, v_defEqCtx_x3f_3991_);
lean_ctor_set(v___x_3998_, 5, v_synthPendingDepth_3992_);
lean_ctor_set(v___x_3998_, 6, v_customCanUnfoldPredicate_x3f_3993_);
lean_ctor_set_uint8(v___x_3998_, sizeof(void*)*7, v_trackZetaDelta_3987_);
lean_ctor_set_uint8(v___x_3998_, sizeof(void*)*7 + 1, v_univApprox_3994_);
lean_ctor_set_uint8(v___x_3998_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3995_);
lean_ctor_set_uint8(v___x_3998_, sizeof(void*)*7 + 3, v_cacheInferType_3996_);
lean_inc(v___y_3973_);
lean_inc_ref(v___y_3972_);
lean_inc(v___y_3971_);
lean_inc(v_a_3981_);
v___x_3999_ = lean_whnf(v_a_3981_, v___x_3998_, v___y_3971_, v___y_3972_, v___y_3973_);
v___y_3917_ = v_a_3981_;
v___y_3918_ = v___y_3968_;
v___y_3919_ = v_isHEq_3969_;
v___y_3920_ = v___y_3970_;
v___y_3921_ = v___y_3973_;
v___y_3922_ = v___y_3971_;
v___y_3923_ = v___y_3972_;
v___y_3924_ = v___x_3999_;
goto v___jp_3916_;
}
else
{
lean_object* v___x_4000_; 
lean_inc(v___y_3973_);
lean_inc_ref(v___y_3972_);
lean_inc(v___y_3971_);
lean_inc_ref(v___y_3970_);
lean_inc(v_a_3981_);
v___x_4000_ = lean_whnf(v_a_3981_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
v___y_3917_ = v_a_3981_;
v___y_3918_ = v___y_3968_;
v___y_3919_ = v_isHEq_3969_;
v___y_3920_ = v___y_3970_;
v___y_3921_ = v___y_3973_;
v___y_3922_ = v___y_3971_;
v___y_3923_ = v___y_3972_;
v___y_3924_ = v___x_4000_;
goto v___jp_3916_;
}
}
else
{
lean_object* v_a_4001_; 
v_a_4001_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_3980_, 1);
v___y_3905_ = v___y_3968_;
v___y_3906_ = v_isHEq_3969_;
v___y_3907_ = v___y_3970_;
v___y_3908_ = v___y_3973_;
v___y_3909_ = v___y_3971_;
v___y_3910_ = v___y_3972_;
v_a_3911_ = v_a_4001_;
goto v___jp_3904_;
}
}
else
{
v___y_3881_ = v___y_3968_;
v___y_3882_ = v_isHEq_3969_;
v___y_3883_ = v___y_3970_;
v___y_3884_ = v___y_3971_;
v___y_3885_ = v___y_3972_;
v___y_3886_ = v___y_3973_;
goto v___jp_3880_;
}
}
else
{
lean_dec(v_a_3977_);
v___y_3881_ = v___y_3968_;
v___y_3882_ = v_isHEq_3969_;
v___y_3883_ = v___y_3970_;
v___y_3884_ = v___y_3971_;
v___y_3885_ = v___y_3972_;
v___y_3886_ = v___y_3973_;
goto v___jp_3880_;
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4002_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3976_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3976_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
else
{
v___y_3881_ = v___y_3968_;
v___y_3882_ = v_isHEq_3969_;
v___y_3883_ = v___y_3970_;
v___y_3884_ = v___y_3971_;
v___y_3885_ = v___y_3972_;
v___y_3886_ = v___y_3973_;
goto v___jp_3880_;
}
}
}
v___jp_4010_:
{
lean_object* v___x_4016_; 
lean_inc_ref(v___x_3879_);
v___x_4016_ = l_Lean_Meta_matchHEq_x3f(v___x_3879_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4016_, 1);
if (lean_obj_tag(v_a_4017_) == 1)
{
lean_object* v_val_4018_; lean_object* v_snd_4019_; lean_object* v_snd_4020_; lean_object* v_fst_4021_; lean_object* v_fst_4022_; lean_object* v_fst_4023_; lean_object* v_snd_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4124_; 
v_val_4018_ = lean_ctor_get(v_a_4017_, 0);
lean_inc(v_val_4018_);
lean_dec_ref_known(v_a_4017_, 1);
v_snd_4019_ = lean_ctor_get(v_val_4018_, 1);
lean_inc(v_snd_4019_);
v_snd_4020_ = lean_ctor_get(v_snd_4019_, 1);
lean_inc(v_snd_4020_);
v_fst_4021_ = lean_ctor_get(v_val_4018_, 0);
lean_inc(v_fst_4021_);
lean_dec(v_val_4018_);
v_fst_4022_ = lean_ctor_get(v_snd_4019_, 0);
lean_inc(v_fst_4022_);
lean_dec(v_snd_4019_);
v_fst_4023_ = lean_ctor_get(v_snd_4020_, 0);
v_snd_4024_ = lean_ctor_get(v_snd_4020_, 1);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_snd_4020_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4026_ = v_snd_4020_;
v_isShared_4027_ = v_isSharedCheck_4124_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_snd_4024_);
lean_inc(v_fst_4023_);
lean_dec(v_snd_4020_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4124_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4022_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref_known(v___x_4028_, 1);
if (lean_obj_tag(v_a_4029_) == 1)
{
lean_object* v_val_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4115_; 
v_val_4030_ = lean_ctor_get(v_a_4029_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v_a_4029_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4032_ = v_a_4029_;
v_isShared_4033_ = v_isSharedCheck_4115_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_val_4030_);
lean_dec(v_a_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4115_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4024_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
if (lean_obj_tag(v_a_4035_) == 1)
{
lean_object* v_toConstantVal_4036_; lean_object* v_val_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4106_; 
v_toConstantVal_4036_ = lean_ctor_get(v_val_4030_, 0);
lean_inc_ref(v_toConstantVal_4036_);
lean_dec(v_val_4030_);
v_val_4037_ = lean_ctor_get(v_a_4035_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_a_4035_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4039_ = v_a_4035_;
v_isShared_4040_ = v_isSharedCheck_4106_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_val_4037_);
lean_dec(v_a_4035_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4106_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v_toConstantVal_4041_; lean_object* v_name_4042_; lean_object* v_name_4043_; uint8_t v___x_4044_; 
v_toConstantVal_4041_ = lean_ctor_get(v_val_4037_, 0);
lean_inc_ref(v_toConstantVal_4041_);
lean_dec(v_val_4037_);
v_name_4042_ = lean_ctor_get(v_toConstantVal_4036_, 0);
lean_inc(v_name_4042_);
lean_dec_ref(v_toConstantVal_4036_);
v_name_4043_ = lean_ctor_get(v_toConstantVal_4041_, 0);
lean_inc(v_name_4043_);
lean_dec_ref(v_toConstantVal_4041_);
v___x_4044_ = lean_name_eq(v_name_4042_, v_name_4043_);
lean_dec(v_name_4043_);
lean_dec(v_name_4042_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_Meta_isExprDefEq(v_fst_4021_, v_fst_4023_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; uint8_t v___x_4047_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc(v_a_4046_);
lean_dec_ref_known(v___x_4045_, 1);
v___x_4047_ = lean_unbox(v_a_4046_);
lean_dec(v_a_4046_);
if (v___x_4047_ == 0)
{
lean_del_object(v___x_4039_);
lean_del_object(v___x_4032_);
lean_del_object(v___x_4026_);
v___y_3968_ = v_isEq_4011_;
v_isHEq_3969_ = v___x_3824_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
v___y_3973_ = v___y_4015_;
goto v___jp_3967_;
}
else
{
lean_object* v___x_4048_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec_ref(v_config_3813_);
lean_inc(v_mvarId_3814_);
v___x_4048_ = l_Lean_MVarId_getType(v_mvarId_3814_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref_known(v___x_4048_, 1);
v___x_4050_ = l_Lean_LocalDecl_toExpr(v_val_3845_);
v___x_4051_ = l_Lean_Meta_mkEqOfHEq(v___x_4050_, v___x_3824_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4053_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_a_4052_);
lean_dec_ref_known(v___x_4051_, 1);
v___x_4053_ = l_Lean_Meta_mkNoConfusion(v_a_4049_, v_a_4052_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4055_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref_known(v___x_4053_, 1);
v___x_4055_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3814_, v_a_4054_, v___y_4013_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v___x_4056_; lean_object* v___x_4058_; 
lean_dec_ref_known(v___x_4055_, 1);
v___x_4056_ = lean_box(v___x_3824_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4056_);
v___x_4058_ = v___x_4039_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4056_);
v___x_4058_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4060_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_3849_);
lean_ctor_set(v___x_4026_, 0, v___x_4058_);
v___x_4060_ = v___x_4026_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_3849_);
v___x_4060_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4062_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set_tag(v___x_4032_, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4060_);
v___x_4062_ = v___x_4032_;
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
v_a_3831_ = v___x_4062_;
goto v___jp_3830_;
}
}
}
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
lean_del_object(v___x_4039_);
lean_del_object(v___x_4032_);
lean_del_object(v___x_4026_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_4066_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_4055_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4055_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_del_object(v___x_4039_);
lean_del_object(v___x_4032_);
lean_del_object(v___x_4026_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4074_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4053_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4053_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec(v_a_4049_);
lean_del_object(v___x_4039_);
lean_del_object(v___x_4032_);
lean_del_object(v___x_4026_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4082_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4051_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4051_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_del_object(v___x_4039_);
lean_del_object(v___x_4032_);
lean_del_object(v___x_4026_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4090_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4048_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4048_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_del_object(v___x_4039_);
lean_del_object(v___x_4032_);
lean_del_object(v___x_4026_);
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4098_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4045_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4045_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
else
{
lean_del_object(v___x_4039_);
lean_del_object(v___x_4032_);
lean_del_object(v___x_4026_);
lean_dec(v_fst_4023_);
lean_dec(v_fst_4021_);
v___y_3968_ = v_isEq_4011_;
v_isHEq_3969_ = v___x_3824_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
v___y_3973_ = v___y_4015_;
goto v___jp_3967_;
}
}
}
else
{
lean_dec(v_a_4035_);
lean_del_object(v___x_4032_);
lean_dec(v_val_4030_);
lean_del_object(v___x_4026_);
lean_dec(v_fst_4023_);
lean_dec(v_fst_4021_);
v___y_3968_ = v_isEq_4011_;
v_isHEq_3969_ = v___x_3824_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
v___y_3973_ = v___y_4015_;
goto v___jp_3967_;
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_del_object(v___x_4032_);
lean_dec(v_val_4030_);
lean_del_object(v___x_4026_);
lean_dec(v_fst_4023_);
lean_dec(v_fst_4021_);
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4107_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4034_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4034_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
}
else
{
lean_dec(v_a_4029_);
lean_del_object(v___x_4026_);
lean_dec(v_snd_4024_);
lean_dec(v_fst_4023_);
lean_dec(v_fst_4021_);
v___y_3968_ = v_isEq_4011_;
v_isHEq_3969_ = v___x_3824_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
v___y_3973_ = v___y_4015_;
goto v___jp_3967_;
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_del_object(v___x_4026_);
lean_dec(v_snd_4024_);
lean_dec(v_fst_4023_);
lean_dec(v_fst_4021_);
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4116_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4028_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4028_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
}
else
{
lean_dec(v_a_4017_);
v___y_3968_ = v_isEq_4011_;
v_isHEq_3969_ = v___x_3878_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
v___y_3973_ = v___y_4015_;
goto v___jp_3967_;
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4125_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4016_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4016_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
v___jp_4133_:
{
lean_object* v___x_4138_; 
lean_inc_ref(v___x_3879_);
v___x_4138_ = l_Lean_Meta_matchEq_x3f(v___x_3879_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
if (lean_obj_tag(v_a_4139_) == 1)
{
lean_object* v_val_4140_; lean_object* v_snd_4141_; lean_object* v_fst_4142_; lean_object* v_snd_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4222_; 
v_val_4140_ = lean_ctor_get(v_a_4139_, 0);
lean_inc(v_val_4140_);
lean_dec_ref_known(v_a_4139_, 1);
v_snd_4141_ = lean_ctor_get(v_val_4140_, 1);
lean_inc(v_snd_4141_);
lean_dec(v_val_4140_);
v_fst_4142_ = lean_ctor_get(v_snd_4141_, 0);
v_snd_4143_ = lean_ctor_get(v_snd_4141_, 1);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_snd_4141_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4145_ = v_snd_4141_;
v_isShared_4146_ = v_isSharedCheck_4222_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_snd_4143_);
lean_inc(v_fst_4142_);
lean_dec(v_snd_4141_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4222_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4142_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
if (lean_obj_tag(v_a_4148_) == 1)
{
lean_object* v_val_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4213_; 
v_val_4149_ = lean_ctor_get(v_a_4148_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v_a_4148_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4151_ = v_a_4148_;
v_isShared_4152_ = v_isSharedCheck_4213_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_val_4149_);
lean_dec(v_a_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4213_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4143_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4153_, 1);
if (lean_obj_tag(v_a_4154_) == 1)
{
lean_object* v_toConstantVal_4155_; lean_object* v_val_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4204_; 
v_toConstantVal_4155_ = lean_ctor_get(v_val_4149_, 0);
lean_inc_ref(v_toConstantVal_4155_);
lean_dec(v_val_4149_);
v_val_4156_ = lean_ctor_get(v_a_4154_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_a_4154_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4158_ = v_a_4154_;
v_isShared_4159_ = v_isSharedCheck_4204_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_val_4156_);
lean_dec(v_a_4154_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4204_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v_toConstantVal_4160_; lean_object* v_name_4161_; lean_object* v_name_4162_; uint8_t v___x_4163_; 
v_toConstantVal_4160_ = lean_ctor_get(v_val_4156_, 0);
lean_inc_ref(v_toConstantVal_4160_);
lean_dec(v_val_4156_);
v_name_4161_ = lean_ctor_get(v_toConstantVal_4155_, 0);
lean_inc(v_name_4161_);
lean_dec_ref(v_toConstantVal_4155_);
v_name_4162_ = lean_ctor_get(v_toConstantVal_4160_, 0);
lean_inc(v_name_4162_);
lean_dec_ref(v_toConstantVal_4160_);
v___x_4163_ = lean_name_eq(v_name_4161_, v_name_4162_);
lean_dec(v_name_4162_);
lean_dec(v_name_4161_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec_ref(v_config_3813_);
lean_inc(v_mvarId_3814_);
v___x_4164_ = l_Lean_MVarId_getType(v_mvarId_3814_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v___x_4166_ = l_Lean_LocalDecl_toExpr(v_val_3845_);
v___x_4167_ = l_Lean_Meta_mkNoConfusion(v_a_4165_, v___x_4166_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4169_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4168_);
lean_dec_ref_known(v___x_4167_, 1);
v___x_4169_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3814_, v_a_4168_, v___y_4135_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v___x_4170_; lean_object* v___x_4172_; 
lean_dec_ref_known(v___x_4169_, 1);
v___x_4170_ = lean_box(v___x_3824_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 0, v___x_4170_);
v___x_4172_ = v___x_4158_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4174_; 
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 1, v___x_3849_);
lean_ctor_set(v___x_4145_, 0, v___x_4172_);
v___x_4174_ = v___x_4145_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4172_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v___x_3849_);
v___x_4174_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_object* v___x_4176_; 
if (v_isShared_4152_ == 0)
{
lean_ctor_set_tag(v___x_4151_, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4174_);
v___x_4176_ = v___x_4151_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
v_a_3831_ = v___x_4176_;
goto v___jp_3830_;
}
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_del_object(v___x_4158_);
lean_del_object(v___x_4151_);
lean_del_object(v___x_4145_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_4180_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4169_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4169_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
lean_del_object(v___x_4158_);
lean_del_object(v___x_4151_);
lean_del_object(v___x_4145_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4188_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4167_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4167_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
else
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
lean_del_object(v___x_4158_);
lean_del_object(v___x_4151_);
lean_del_object(v___x_4145_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4196_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_4164_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4164_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
else
{
lean_del_object(v___x_4158_);
lean_del_object(v___x_4151_);
lean_del_object(v___x_4145_);
v_isEq_4011_ = v___x_3824_;
v___y_4012_ = v___y_4134_;
v___y_4013_ = v___y_4135_;
v___y_4014_ = v___y_4136_;
v___y_4015_ = v___y_4137_;
goto v___jp_4010_;
}
}
}
else
{
lean_dec(v_a_4154_);
lean_del_object(v___x_4151_);
lean_dec(v_val_4149_);
lean_del_object(v___x_4145_);
v_isEq_4011_ = v___x_3824_;
v___y_4012_ = v___y_4134_;
v___y_4013_ = v___y_4135_;
v___y_4014_ = v___y_4136_;
v___y_4015_ = v___y_4137_;
goto v___jp_4010_;
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_del_object(v___x_4151_);
lean_dec(v_val_4149_);
lean_del_object(v___x_4145_);
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4205_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4153_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4153_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
}
else
{
lean_dec(v_a_4148_);
lean_del_object(v___x_4145_);
lean_dec(v_snd_4143_);
v_isEq_4011_ = v___x_3824_;
v___y_4012_ = v___y_4134_;
v___y_4013_ = v___y_4135_;
v___y_4014_ = v___y_4136_;
v___y_4015_ = v___y_4137_;
goto v___jp_4010_;
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_del_object(v___x_4145_);
lean_dec(v_snd_4143_);
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4214_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4147_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4147_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
else
{
lean_dec(v_a_4139_);
v_isEq_4011_ = v___x_3878_;
v___y_4012_ = v___y_4134_;
v___y_4013_ = v___y_4135_;
v___y_4014_ = v___y_4136_;
v___y_4015_ = v___y_4137_;
goto v___jp_4010_;
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4223_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4138_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4138_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
v___jp_4231_:
{
lean_object* v___x_4236_; 
lean_inc_ref(v___x_3879_);
v___x_4236_ = l_Lean_refutableHasNotBit_x3f(v___x_3879_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
if (lean_obj_tag(v_a_4237_) == 1)
{
lean_object* v_val_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4278_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec_ref(v_config_3813_);
v_val_4238_ = lean_ctor_get(v_a_4237_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v_a_4237_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4240_ = v_a_4237_;
v_isShared_4241_ = v_isSharedCheck_4278_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_val_4238_);
lean_dec(v_a_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4278_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4242_; 
lean_inc(v_mvarId_3814_);
v___x_4242_ = l_Lean_MVarId_getType(v_mvarId_3814_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v___x_4242_, 1);
v___x_4244_ = l_Lean_LocalDecl_toExpr(v_val_3845_);
v___x_4245_ = l_Lean_Meta_mkAbsurd(v_a_4243_, v_val_4238_, v___x_4244_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4247_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref_known(v___x_4245_, 1);
v___x_4247_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3814_, v_a_4246_, v___y_4233_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
lean_dec_ref_known(v___x_4247_, 1);
v___x_4248_ = lean_box(v___x_3824_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4248_);
v___x_4250_ = v___x_4240_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
lean_ctor_set(v___x_4251_, 1, v___x_3849_);
v___x_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4251_);
v_a_3831_ = v___x_4252_;
goto v___jp_3830_;
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_del_object(v___x_4240_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_4254_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4247_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4247_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_del_object(v___x_4240_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4262_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4245_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4245_);
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
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_del_object(v___x_4240_);
lean_dec(v_val_4238_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4270_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4242_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4242_);
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
}
else
{
lean_object* v___x_4279_; 
lean_dec(v_a_4237_);
lean_inc_ref(v___x_3879_);
v___x_4279_ = l_Lean_Meta_matchNe_x3f(v___x_3879_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
if (lean_obj_tag(v_a_4280_) == 1)
{
lean_object* v_val_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4351_; 
v_val_4281_ = lean_ctor_get(v_a_4280_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v_a_4280_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4283_ = v_a_4280_;
v_isShared_4284_ = v_isSharedCheck_4351_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_val_4281_);
lean_dec(v_a_4280_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4351_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v_snd_4285_; lean_object* v_fst_4286_; lean_object* v_snd_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4350_; 
v_snd_4285_ = lean_ctor_get(v_val_4281_, 1);
lean_inc(v_snd_4285_);
lean_dec(v_val_4281_);
v_fst_4286_ = lean_ctor_get(v_snd_4285_, 0);
v_snd_4287_ = lean_ctor_get(v_snd_4285_, 1);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_snd_4285_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4289_ = v_snd_4285_;
v_isShared_4290_ = v_isSharedCheck_4350_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_snd_4287_);
lean_inc(v_fst_4286_);
lean_dec(v_snd_4285_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4350_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4291_; 
lean_inc(v_fst_4286_);
v___x_4291_ = l_Lean_Meta_isExprDefEq(v_fst_4286_, v_snd_4287_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; uint8_t v___x_4293_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = lean_unbox(v_a_4292_);
lean_dec(v_a_4292_);
if (v___x_4293_ == 0)
{
lean_del_object(v___x_4289_);
lean_dec(v_fst_4286_);
lean_del_object(v___x_4283_);
v___y_4134_ = v___y_4232_;
v___y_4135_ = v___y_4233_;
v___y_4136_ = v___y_4234_;
v___y_4137_ = v___y_4235_;
goto v___jp_4133_;
}
else
{
lean_object* v___x_4294_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec_ref(v_config_3813_);
lean_inc(v_mvarId_3814_);
v___x_4294_ = l_Lean_MVarId_getType(v_mvarId_3814_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4296_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
lean_inc(v_a_4295_);
lean_dec_ref_known(v___x_4294_, 1);
v___x_4296_ = l_Lean_Meta_mkEqRefl(v_fst_4286_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref_known(v___x_4296_, 1);
v___x_4298_ = l_Lean_LocalDecl_toExpr(v_val_3845_);
v___x_4299_ = l_Lean_Meta_mkAbsurd(v_a_4295_, v_a_4297_, v___x_4298_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4301_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4299_, 1);
v___x_4301_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3814_, v_a_4300_, v___y_4233_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v___x_4302_; lean_object* v___x_4304_; 
lean_dec_ref_known(v___x_4301_, 1);
v___x_4302_ = lean_box(v___x_3824_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4302_);
v___x_4304_ = v___x_4283_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4306_; 
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 1, v___x_3849_);
lean_ctor_set(v___x_4289_, 0, v___x_4304_);
v___x_4306_ = v___x_4289_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4304_);
lean_ctor_set(v_reuseFailAlloc_4308_, 1, v___x_3849_);
v___x_4306_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
v_a_3831_ = v___x_4307_;
goto v___jp_3830_;
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_del_object(v___x_4289_);
lean_del_object(v___x_4283_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_4310_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4301_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4301_);
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
lean_del_object(v___x_4289_);
lean_del_object(v___x_4283_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4318_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4299_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4299_);
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
lean_dec(v_a_4295_);
lean_del_object(v___x_4289_);
lean_del_object(v___x_4283_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4326_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4296_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4296_);
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
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_del_object(v___x_4289_);
lean_dec(v_fst_4286_);
lean_del_object(v___x_4283_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
v_a_4334_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4294_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4294_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
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
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
lean_del_object(v___x_4289_);
lean_dec(v_fst_4286_);
lean_del_object(v___x_4283_);
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4342_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4291_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4291_);
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
}
}
else
{
lean_dec(v_a_4280_);
v___y_4134_ = v___y_4232_;
v___y_4135_ = v___y_4233_;
v___y_4136_ = v___y_4234_;
v___y_4137_ = v___y_4235_;
goto v___jp_4133_;
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4352_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4279_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4279_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec_ref(v___x_3879_);
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_4360_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4236_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4236_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
else
{
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_3839_ = v___x_3850_;
goto v___jp_3838_;
}
v___jp_3851_:
{
uint8_t v_emptyType_3858_; 
v_emptyType_3858_ = lean_ctor_get_uint8(v_config_3813_, sizeof(void*)*1 + 1);
if (v_emptyType_3858_ == 0)
{
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_3839_ = v___x_3850_;
goto v___jp_3838_;
}
else
{
if (v___y_3852_ == 0)
{
if (v___y_3853_ == 0)
{
lean_object* v_searchFuel_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v_searchFuel_3859_ = lean_ctor_get(v_config_3813_, 0);
v___x_3860_ = l_Lean_LocalDecl_fvarId(v_val_3845_);
lean_dec(v_val_3845_);
lean_inc(v_searchFuel_3859_);
lean_inc(v_mvarId_3814_);
v___x_3861_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_3814_, v___x_3860_, v_searchFuel_3859_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; uint8_t v___x_3863_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v___x_3861_, 1);
v___x_3863_ = lean_unbox(v_a_3862_);
lean_dec(v_a_3862_);
if (v___x_3863_ == 0)
{
lean_del_object(v___x_3847_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_3839_ = v___x_3850_;
goto v___jp_3838_;
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3866_; 
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v___x_3864_ = lean_box(v___x_3824_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3864_);
v___x_3866_ = v___x_3847_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v___x_3849_);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
v_a_3831_ = v___x_3868_;
goto v___jp_3830_;
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_del_object(v___x_3847_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
lean_dec(v_mvarId_3814_);
lean_dec_ref(v_config_3813_);
v_a_3870_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3861_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3861_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_3839_ = v___x_3850_;
goto v___jp_3838_;
}
}
else
{
lean_del_object(v___x_3847_);
lean_dec(v_val_3845_);
lean_del_object(v___x_3828_);
lean_dec(v_snd_3826_);
v_a_3839_ = v___x_3850_;
goto v___jp_3838_;
}
}
}
}
}
v___jp_3830_:
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3832_, 0, v_a_3831_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3832_);
v___x_3834_ = v___x_3828_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_snd_3826_);
v___x_3834_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
return v___x_3835_;
}
}
v___jp_3838_:
{
lean_object* v___x_3840_; size_t v___x_3841_; size_t v___x_3842_; lean_object* v___x_3843_; 
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3837_);
lean_ctor_set(v___x_3840_, 1, v_a_3839_);
v___x_3841_ = ((size_t)1ULL);
v___x_3842_ = lean_usize_add(v_i_3817_, v___x_3841_);
v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3813_, v_mvarId_3814_, v_as_3815_, v_sz_3816_, v___x_3842_, v___x_3840_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
return v___x_3843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4441_, lean_object* v_mvarId_4442_, lean_object* v_as_4443_, lean_object* v_sz_4444_, lean_object* v_i_4445_, lean_object* v_b_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
size_t v_sz_boxed_4452_; size_t v_i_boxed_4453_; lean_object* v_res_4454_; 
v_sz_boxed_4452_ = lean_unbox_usize(v_sz_4444_);
lean_dec(v_sz_4444_);
v_i_boxed_4453_ = lean_unbox_usize(v_i_4445_);
lean_dec(v_i_4445_);
v_res_4454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4441_, v_mvarId_4442_, v_as_4443_, v_sz_boxed_4452_, v_i_boxed_4453_, v_b_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec_ref(v_as_4443_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4455_, lean_object* v_config_4456_, lean_object* v_mvarId_4457_, lean_object* v_n_4458_, lean_object* v_b_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
if (lean_obj_tag(v_n_4458_) == 0)
{
lean_object* v_cs_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; size_t v_sz_4468_; size_t v___x_4469_; lean_object* v___x_4470_; 
v_cs_4465_ = lean_ctor_get(v_n_4458_, 0);
v___x_4466_ = lean_box(0);
v___x_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
lean_ctor_set(v___x_4467_, 1, v_b_4459_);
v_sz_4468_ = lean_array_size(v_cs_4465_);
v___x_4469_ = ((size_t)0ULL);
v___x_4470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4455_, v_config_4456_, v_mvarId_4457_, v_cs_4465_, v_sz_4468_, v___x_4469_, v___x_4467_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4485_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4473_ = v___x_4470_;
v_isShared_4474_ = v_isSharedCheck_4485_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4485_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v_fst_4475_; 
v_fst_4475_ = lean_ctor_get(v_a_4471_, 0);
if (lean_obj_tag(v_fst_4475_) == 0)
{
lean_object* v_snd_4476_; lean_object* v___x_4477_; lean_object* v___x_4479_; 
v_snd_4476_ = lean_ctor_get(v_a_4471_, 1);
lean_inc(v_snd_4476_);
lean_dec(v_a_4471_);
v___x_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4477_, 0, v_snd_4476_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v___x_4477_);
v___x_4479_ = v___x_4473_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
else
{
lean_object* v_val_4481_; lean_object* v___x_4483_; 
lean_inc_ref(v_fst_4475_);
lean_dec(v_a_4471_);
v_val_4481_ = lean_ctor_get(v_fst_4475_, 0);
lean_inc(v_val_4481_);
lean_dec_ref_known(v_fst_4475_, 1);
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v_val_4481_);
v___x_4483_ = v___x_4473_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_val_4481_);
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
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
v_a_4486_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4470_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4470_);
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
}
else
{
lean_object* v_vs_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; size_t v_sz_4497_; size_t v___x_4498_; lean_object* v___x_4499_; 
v_vs_4494_ = lean_ctor_get(v_n_4458_, 0);
v___x_4495_ = lean_box(0);
v___x_4496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
lean_ctor_set(v___x_4496_, 1, v_b_4459_);
v_sz_4497_ = lean_array_size(v_vs_4494_);
v___x_4498_ = ((size_t)0ULL);
v___x_4499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4456_, v_mvarId_4457_, v_vs_4494_, v_sz_4497_, v___x_4498_, v___x_4496_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4514_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4502_ = v___x_4499_;
v_isShared_4503_ = v_isSharedCheck_4514_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4499_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4514_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v_fst_4504_; 
v_fst_4504_ = lean_ctor_get(v_a_4500_, 0);
if (lean_obj_tag(v_fst_4504_) == 0)
{
lean_object* v_snd_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v_snd_4505_ = lean_ctor_get(v_a_4500_, 1);
lean_inc(v_snd_4505_);
lean_dec(v_a_4500_);
v___x_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4506_, 0, v_snd_4505_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v___x_4506_);
v___x_4508_ = v___x_4502_;
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
return v___x_4508_;
}
}
else
{
lean_object* v_val_4510_; lean_object* v___x_4512_; 
lean_inc_ref(v_fst_4504_);
lean_dec(v_a_4500_);
v_val_4510_ = lean_ctor_get(v_fst_4504_, 0);
lean_inc(v_val_4510_);
lean_dec_ref_known(v_fst_4504_, 1);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v_val_4510_);
v___x_4512_ = v___x_4502_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_val_4510_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
v_a_4515_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4499_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4499_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4523_, lean_object* v_config_4524_, lean_object* v_mvarId_4525_, lean_object* v_as_4526_, size_t v_sz_4527_, size_t v_i_4528_, lean_object* v_b_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
uint8_t v___x_4535_; 
v___x_4535_ = lean_usize_dec_lt(v_i_4528_, v_sz_4527_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; 
lean_dec(v_mvarId_4525_);
lean_dec_ref(v_config_4524_);
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v_b_4529_);
return v___x_4536_;
}
else
{
lean_object* v_snd_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4571_; 
v_snd_4537_ = lean_ctor_get(v_b_4529_, 1);
v_isSharedCheck_4571_ = !lean_is_exclusive(v_b_4529_);
if (v_isSharedCheck_4571_ == 0)
{
lean_object* v_unused_4572_; 
v_unused_4572_ = lean_ctor_get(v_b_4529_, 0);
lean_dec(v_unused_4572_);
v___x_4539_ = v_b_4529_;
v_isShared_4540_ = v_isSharedCheck_4571_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_snd_4537_);
lean_dec(v_b_4529_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4571_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4541_; lean_object* v_a_4542_; lean_object* v___x_4543_; 
v___x_4541_ = lean_box(0);
v_a_4542_ = lean_array_uget_borrowed(v_as_4526_, v_i_4528_);
lean_inc(v_snd_4537_);
lean_inc(v_mvarId_4525_);
lean_inc_ref(v_config_4524_);
v___x_4543_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4523_, v_config_4524_, v_mvarId_4525_, v_a_4542_, v_snd_4537_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4562_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4562_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4543_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4562_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
if (lean_obj_tag(v_a_4544_) == 0)
{
lean_object* v___x_4548_; lean_object* v___x_4550_; 
lean_dec(v_mvarId_4525_);
lean_dec_ref(v_config_4524_);
v___x_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4548_, 0, v_a_4544_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4548_);
v___x_4550_ = v___x_4539_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4554_, 1, v_snd_4537_);
v___x_4550_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4552_; 
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v___x_4550_);
v___x_4552_ = v___x_4546_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4550_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; 
lean_del_object(v___x_4546_);
lean_dec(v_snd_4537_);
v_a_4555_ = lean_ctor_get(v_a_4544_, 0);
lean_inc(v_a_4555_);
lean_dec_ref_known(v_a_4544_, 1);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 1, v_a_4555_);
lean_ctor_set(v___x_4539_, 0, v___x_4541_);
v___x_4557_ = v___x_4539_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4541_);
lean_ctor_set(v_reuseFailAlloc_4561_, 1, v_a_4555_);
v___x_4557_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
size_t v___x_4558_; size_t v___x_4559_; 
v___x_4558_ = ((size_t)1ULL);
v___x_4559_ = lean_usize_add(v_i_4528_, v___x_4558_);
v_i_4528_ = v___x_4559_;
v_b_4529_ = v___x_4557_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_del_object(v___x_4539_);
lean_dec(v_snd_4537_);
lean_dec(v_mvarId_4525_);
lean_dec_ref(v_config_4524_);
v_a_4563_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4543_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4543_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4573_, lean_object* v_config_4574_, lean_object* v_mvarId_4575_, lean_object* v_as_4576_, lean_object* v_sz_4577_, lean_object* v_i_4578_, lean_object* v_b_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
size_t v_sz_boxed_4585_; size_t v_i_boxed_4586_; lean_object* v_res_4587_; 
v_sz_boxed_4585_ = lean_unbox_usize(v_sz_4577_);
lean_dec(v_sz_4577_);
v_i_boxed_4586_ = lean_unbox_usize(v_i_4578_);
lean_dec(v_i_4578_);
v_res_4587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4573_, v_config_4574_, v_mvarId_4575_, v_as_4576_, v_sz_boxed_4585_, v_i_boxed_4586_, v_b_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec_ref(v_as_4576_);
lean_dec_ref(v_init_4573_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4588_, lean_object* v_config_4589_, lean_object* v_mvarId_4590_, lean_object* v_n_4591_, lean_object* v_b_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4588_, v_config_4589_, v_mvarId_4590_, v_n_4591_, v_b_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec_ref(v_n_4591_);
lean_dec_ref(v_init_4588_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4599_, lean_object* v_mvarId_4600_, lean_object* v_t_4601_, lean_object* v_init_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v_root_4608_; lean_object* v_tail_4609_; lean_object* v___x_4610_; 
v_root_4608_ = lean_ctor_get(v_t_4601_, 0);
v_tail_4609_ = lean_ctor_get(v_t_4601_, 1);
lean_inc(v_mvarId_4600_);
lean_inc_ref(v_config_4599_);
lean_inc_ref(v_init_4602_);
v___x_4610_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4602_, v_config_4599_, v_mvarId_4600_, v_root_4608_, v_init_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
lean_dec_ref(v_init_4602_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4647_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4647_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4647_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
if (lean_obj_tag(v_a_4611_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; 
lean_dec(v_mvarId_4600_);
lean_dec_ref(v_config_4599_);
v_a_4615_ = lean_ctor_get(v_a_4611_, 0);
lean_inc(v_a_4615_);
lean_dec_ref_known(v_a_4611_, 1);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v_a_4615_);
v___x_4617_ = v___x_4613_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4615_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
else
{
lean_object* v_a_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; size_t v_sz_4622_; size_t v___x_4623_; lean_object* v___x_4624_; 
lean_del_object(v___x_4613_);
v_a_4619_ = lean_ctor_get(v_a_4611_, 0);
lean_inc(v_a_4619_);
lean_dec_ref_known(v_a_4611_, 1);
v___x_4620_ = lean_box(0);
v___x_4621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
lean_ctor_set(v___x_4621_, 1, v_a_4619_);
v_sz_4622_ = lean_array_size(v_tail_4609_);
v___x_4623_ = ((size_t)0ULL);
v___x_4624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4599_, v_mvarId_4600_, v_tail_4609_, v_sz_4622_, v___x_4623_, v___x_4621_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4638_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4627_ = v___x_4624_;
v_isShared_4628_ = v_isSharedCheck_4638_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4624_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4638_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v_fst_4629_; 
v_fst_4629_ = lean_ctor_get(v_a_4625_, 0);
if (lean_obj_tag(v_fst_4629_) == 0)
{
lean_object* v_snd_4630_; lean_object* v___x_4632_; 
v_snd_4630_ = lean_ctor_get(v_a_4625_, 1);
lean_inc(v_snd_4630_);
lean_dec(v_a_4625_);
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 0, v_snd_4630_);
v___x_4632_ = v___x_4627_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_snd_4630_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
else
{
lean_object* v_val_4634_; lean_object* v___x_4636_; 
lean_inc_ref(v_fst_4629_);
lean_dec(v_a_4625_);
v_val_4634_ = lean_ctor_get(v_fst_4629_, 0);
lean_inc(v_val_4634_);
lean_dec_ref_known(v_fst_4629_, 1);
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 0, v_val_4634_);
v___x_4636_ = v___x_4627_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_val_4634_);
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
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
v_a_4639_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4624_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4624_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
}
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
lean_dec(v_mvarId_4600_);
lean_dec_ref(v_config_4599_);
v_a_4648_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4610_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4610_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4656_, lean_object* v_mvarId_4657_, lean_object* v_t_4658_, lean_object* v_init_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4656_, v_mvarId_4657_, v_t_4658_, v_init_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec_ref(v_t_4658_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4666_, lean_object* v___x_4667_, lean_object* v_config_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v___x_4674_; 
lean_inc(v_mvarId_4666_);
v___x_4674_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4666_, v___x_4667_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v___x_4675_; 
lean_dec_ref_known(v___x_4674_, 1);
lean_inc(v_mvarId_4666_);
v___x_4675_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4666_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4709_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4709_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4709_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
uint8_t v___x_4680_; 
v___x_4680_ = lean_unbox(v_a_4676_);
if (v___x_4680_ == 0)
{
lean_object* v_lctx_4681_; lean_object* v_decls_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
lean_del_object(v___x_4678_);
v_lctx_4681_ = lean_ctor_get(v___y_4669_, 2);
v_decls_4682_ = lean_ctor_get(v_lctx_4681_, 1);
v___x_4683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4684_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4668_, v_mvarId_4666_, v_decls_4682_, v___x_4683_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4697_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4687_ = v___x_4684_;
v_isShared_4688_ = v_isSharedCheck_4697_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___x_4684_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4697_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v_fst_4689_; 
v_fst_4689_ = lean_ctor_get(v_a_4685_, 0);
lean_inc(v_fst_4689_);
lean_dec(v_a_4685_);
if (lean_obj_tag(v_fst_4689_) == 0)
{
lean_object* v___x_4691_; 
if (v_isShared_4688_ == 0)
{
lean_ctor_set(v___x_4687_, 0, v_a_4676_);
v___x_4691_ = v___x_4687_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4676_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
else
{
lean_object* v_val_4693_; lean_object* v___x_4695_; 
lean_dec(v_a_4676_);
v_val_4693_ = lean_ctor_get(v_fst_4689_, 0);
lean_inc(v_val_4693_);
lean_dec_ref_known(v_fst_4689_, 1);
if (v_isShared_4688_ == 0)
{
lean_ctor_set(v___x_4687_, 0, v_val_4693_);
v___x_4695_ = v___x_4687_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_val_4693_);
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
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
lean_dec(v_a_4676_);
v_a_4698_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4684_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4684_);
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
else
{
lean_object* v___x_4707_; 
lean_dec_ref(v_config_4668_);
lean_dec(v_mvarId_4666_);
if (v_isShared_4679_ == 0)
{
v___x_4707_ = v___x_4678_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4676_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
else
{
lean_dec_ref(v_config_4668_);
lean_dec(v_mvarId_4666_);
return v___x_4675_;
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
lean_dec_ref(v_config_4668_);
lean_dec(v_mvarId_4666_);
v_a_4710_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4674_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4674_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4718_, lean_object* v___x_4719_, lean_object* v_config_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4718_, v___x_4719_, v_config_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4729_, lean_object* v_config_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v___x_4736_; lean_object* v___f_4737_; lean_object* v___x_4738_; 
v___x_4736_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4729_);
v___f_4737_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4737_, 0, v_mvarId_4729_);
lean_closure_set(v___f_4737_, 1, v___x_4736_);
lean_closure_set(v___f_4737_, 2, v_config_4730_);
v___x_4738_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4729_, v___f_4737_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4739_, lean_object* v_config_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l_Lean_MVarId_contradictionCore(v_mvarId_4739_, v_config_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
lean_dec(v_a_4744_);
lean_dec_ref(v_a_4743_);
lean_dec(v_a_4742_);
lean_dec_ref(v_a_4741_);
return v_res_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4747_, lean_object* v_config_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v___x_4754_; 
lean_inc(v_mvarId_4747_);
v___x_4754_ = l_Lean_MVarId_contradictionCore(v_mvarId_4747_, v_config_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4767_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4757_ = v___x_4754_;
v_isShared_4758_ = v_isSharedCheck_4767_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4754_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4767_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
uint8_t v___x_4759_; 
v___x_4759_ = lean_unbox(v_a_4755_);
lean_dec(v_a_4755_);
if (v___x_4759_ == 0)
{
lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_del_object(v___x_4757_);
v___x_4760_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4761_ = lean_box(0);
v___x_4762_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4760_, v_mvarId_4747_, v___x_4761_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
return v___x_4762_;
}
else
{
lean_object* v___x_4763_; lean_object* v___x_4765_; 
lean_dec(v_mvarId_4747_);
v___x_4763_ = lean_box(0);
if (v_isShared_4758_ == 0)
{
lean_ctor_set(v___x_4757_, 0, v___x_4763_);
v___x_4765_ = v___x_4757_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v___x_4763_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
}
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4775_; 
lean_dec(v_mvarId_4747_);
v_a_4768_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4770_ = v___x_4754_;
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4754_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4773_; 
if (v_isShared_4771_ == 0)
{
v___x_4773_ = v___x_4770_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_a_4768_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4776_, lean_object* v_config_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Lean_MVarId_contradiction(v_mvarId_4776_, v_config_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_);
lean_dec(v_a_4781_);
lean_dec_ref(v_a_4780_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4846_; uint8_t v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4846_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4847_ = 0;
v___x_4848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4849_ = l_Lean_registerTraceClass(v___x_4846_, v___x_4847_, v___x_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4851_;
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
