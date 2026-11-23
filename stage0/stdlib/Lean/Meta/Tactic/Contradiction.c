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
size_t v_x_1116__boxed_155_; size_t v_x_1117__boxed_156_; lean_object* v_res_157_; 
v_x_1116__boxed_155_ = lean_unbox_usize(v_x_151_);
lean_dec(v_x_151_);
v_x_1117__boxed_156_ = lean_unbox_usize(v_x_152_);
lean_dec(v_x_152_);
v_res_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_150_, v_x_1116__boxed_155_, v_x_1117__boxed_156_, v_x_153_, v_x_154_);
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
lean_object* v___x_169_; lean_object* v_mctx_170_; lean_object* v_cache_171_; lean_object* v_zetaDeltaFVarIds_172_; lean_object* v_postponed_173_; lean_object* v_diag_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_202_; 
v___x_169_ = lean_st_ref_take(v___y_167_);
v_mctx_170_ = lean_ctor_get(v___x_169_, 0);
v_cache_171_ = lean_ctor_get(v___x_169_, 1);
v_zetaDeltaFVarIds_172_ = lean_ctor_get(v___x_169_, 2);
v_postponed_173_ = lean_ctor_get(v___x_169_, 3);
v_diag_174_ = lean_ctor_get(v___x_169_, 4);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_202_ == 0)
{
v___x_176_ = v___x_169_;
v_isShared_177_ = v_isSharedCheck_202_;
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
v_isShared_177_ = v_isSharedCheck_202_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_depth_178_; lean_object* v_levelAssignDepth_179_; lean_object* v_lmvarCounter_180_; lean_object* v_mvarCounter_181_; lean_object* v_lDecls_182_; lean_object* v_decls_183_; lean_object* v_userNames_184_; lean_object* v_lAssignment_185_; lean_object* v_eAssignment_186_; lean_object* v_dAssignment_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_201_; 
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
v_isSharedCheck_201_ = !lean_is_exclusive(v_mctx_170_);
if (v_isSharedCheck_201_ == 0)
{
v___x_189_ = v_mctx_170_;
v_isShared_190_ = v_isSharedCheck_201_;
goto v_resetjp_188_;
}
else
{
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
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_201_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_191_ = lean_box(0);
v___x_192_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_186_, v_mvarId_165_, v_val_166_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 8, v___x_192_);
v___x_194_ = v___x_189_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_depth_178_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_levelAssignDepth_179_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_lmvarCounter_180_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_mvarCounter_181_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_lDecls_182_);
lean_ctor_set(v_reuseFailAlloc_200_, 5, v_decls_183_);
lean_ctor_set(v_reuseFailAlloc_200_, 6, v_userNames_184_);
lean_ctor_set(v_reuseFailAlloc_200_, 7, v_lAssignment_185_);
lean_ctor_set(v_reuseFailAlloc_200_, 8, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_200_, 9, v_dAssignment_187_);
v___x_194_ = v_reuseFailAlloc_200_;
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
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_cache_171_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_zetaDeltaFVarIds_172_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_postponed_173_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_diag_174_);
v___x_196_ = v_reuseFailAlloc_199_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_st_ref_put(v___y_167_, v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_191_);
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object* v_mvarId_203_, lean_object* v_val_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_203_, v_val_204_, v___y_205_);
lean_dec(v___y_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object* v_mvarId_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___f_215_; lean_object* v___x_216_; 
v___f_215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
lean_inc(v_mvarId_209_);
v___x_216_ = l_Lean_MVarId_getType(v_mvarId_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_260_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_260_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_260_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_260_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; 
v___x_221_ = lean_find_expr(v___f_215_, v_a_217_);
lean_dec(v_a_217_);
if (lean_obj_tag(v___x_221_) == 1)
{
lean_object* v_val_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
lean_del_object(v___x_219_);
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
v___x_223_ = l_Lean_Expr_appArg_x21(v_val_222_);
lean_dec(v_val_222_);
lean_inc(v_mvarId_209_);
v___x_224_ = l_Lean_MVarId_getType(v_mvarId_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
v___x_226_ = l_Lean_Meta_mkFalseElim(v_a_225_, v___x_223_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_237_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_209_, v_a_227_, v_a_211_);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v___x_228_, 0);
lean_dec(v_unused_238_);
v___x_230_ = v___x_228_;
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
else
{
lean_dec(v___x_228_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = 1;
v___x_233_ = lean_box(v___x_232_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_mvarId_209_);
v_a_239_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_226_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_226_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v___x_223_);
lean_dec(v_mvarId_209_);
v_a_247_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_224_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_224_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
uint8_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
lean_dec(v___x_221_);
lean_dec(v_mvarId_209_);
v___x_255_ = 0;
v___x_256_ = lean_box(v___x_255_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_256_);
v___x_258_ = v___x_219_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
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
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v_mvarId_209_);
v_a_261_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_216_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_216_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object* v_mvarId_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object* v_mvarId_276_, lean_object* v_val_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_276_, v_val_277_, v___y_279_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object* v_mvarId_284_, lean_object* v_val_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(v_mvarId_284_, v_val_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object* v_00_u03b2_292_, lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_x_293_, v_x_294_, v_x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_297_, lean_object* v_x_298_, size_t v_x_299_, size_t v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_298_, v_x_299_, v_x_300_, v_x_301_, v_x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
size_t v_x_1467__boxed_310_; size_t v_x_1468__boxed_311_; lean_object* v_res_312_; 
v_x_1467__boxed_310_ = lean_unbox_usize(v_x_306_);
lean_dec(v_x_306_);
v_x_1468__boxed_311_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_res_312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_304_, v_x_305_, v_x_1467__boxed_310_, v_x_1468__boxed_311_, v_x_308_, v_x_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_313_, lean_object* v_n_314_, lean_object* v_k_315_, lean_object* v_v_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v_n_314_, v_k_315_, v_v_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_318_, size_t v_depth_319_, lean_object* v_keys_320_, lean_object* v_vals_321_, lean_object* v_heq_322_, lean_object* v_i_323_, lean_object* v_entries_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_319_, v_keys_320_, v_vals_321_, v_i_323_, v_entries_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_326_, lean_object* v_depth_327_, lean_object* v_keys_328_, lean_object* v_vals_329_, lean_object* v_heq_330_, lean_object* v_i_331_, lean_object* v_entries_332_){
_start:
{
size_t v_depth_boxed_333_; lean_object* v_res_334_; 
v_depth_boxed_333_ = lean_unbox_usize(v_depth_327_);
lean_dec(v_depth_327_);
v_res_334_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_326_, v_depth_boxed_333_, v_keys_328_, v_vals_329_, v_heq_330_, v_i_331_, v_entries_332_);
lean_dec_ref(v_vals_329_);
lean_dec_ref(v_keys_328_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_336_, v_x_337_, v_x_338_, v_x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* v_fvarId_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_FVarId_getType___redArg(v_fvarId_341_, v_a_342_, v_a_344_, v_a_345_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = l_Lean_Meta_whnfD(v_a_352_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_380_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_380_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_380_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_380_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Expr_getAppFn(v_a_354_);
lean_dec(v_a_354_);
if (lean_obj_tag(v___x_358_) == 4)
{
lean_object* v_declName_359_; lean_object* v___x_360_; lean_object* v_env_361_; uint8_t v___x_362_; lean_object* v___x_363_; 
v_declName_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_declName_359_);
lean_dec_ref_known(v___x_358_, 2);
v___x_360_ = lean_st_ref_get(v_a_345_);
v_env_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_env_361_);
lean_dec(v___x_360_);
v___x_362_ = 0;
v___x_363_ = l_Lean_Environment_find_x3f(v_env_361_, v_declName_359_, v___x_362_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_del_object(v___x_356_);
goto v___jp_347_;
}
else
{
lean_object* v_val_364_; 
v_val_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v___x_363_, 1);
if (lean_obj_tag(v_val_364_) == 5)
{
lean_object* v_val_365_; lean_object* v_numIndices_366_; lean_object* v_ctors_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_val_365_ = lean_ctor_get(v_val_364_, 0);
lean_inc_ref(v_val_365_);
lean_dec_ref_known(v_val_364_, 1);
v_numIndices_366_ = lean_ctor_get(v_val_365_, 2);
lean_inc(v_numIndices_366_);
v_ctors_367_ = lean_ctor_get(v_val_365_, 4);
lean_inc(v_ctors_367_);
lean_dec_ref(v_val_365_);
v___x_368_ = l_List_lengthTR___redArg(v_ctors_367_);
lean_dec(v_ctors_367_);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_nat_dec_eq(v___x_368_, v___x_369_);
lean_dec(v___x_368_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_371_ = lean_nat_dec_lt(v___x_369_, v_numIndices_366_);
lean_dec(v_numIndices_366_);
v___x_372_ = lean_box(v___x_371_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_372_);
v___x_374_ = v___x_356_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
lean_object* v___x_376_; lean_object* v___x_378_; 
lean_dec(v_numIndices_366_);
v___x_376_ = lean_box(v___x_370_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_376_);
v___x_378_ = v___x_356_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
else
{
lean_dec(v_val_364_);
lean_del_object(v___x_356_);
goto v___jp_347_;
}
}
}
else
{
lean_dec_ref(v___x_358_);
lean_del_object(v___x_356_);
goto v___jp_347_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_a_381_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_353_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_353_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
v_a_389_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_351_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_351_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
v___jp_347_:
{
uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = 0;
v___x_349_ = lean_box(v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object* v_fvarId_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object* v_s_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_SavedState_restore___redArg(v_s_404_, v___y_407_, v___y_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object* v_s_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(v_s_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object* v_x_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
lean_inc(v___y_429_);
v___x_435_ = lean_apply_6(v_x_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object* v_x_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(v_x_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_437_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* v_mvarId_444_, lean_object* v_x_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___f_452_; lean_object* v___x_453_; 
lean_inc(v___y_446_);
v___f_452_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_452_, 0, v_x_445_);
lean_closure_set(v___f_452_, 1, v___y_446_);
v___x_453_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_444_, v___f_452_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_453_) == 0)
{
return v___x_453_;
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object* v_mvarId_462_, lean_object* v_x_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_462_, v_x_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object* v_00_u03b1_471_, lean_object* v_mvarId_472_, lean_object* v_x_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_472_, v_x_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object* v_00_u03b1_481_, lean_object* v_mvarId_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(v_00_u03b1_481_, v_mvarId_482_, v_x_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* v_x_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Meta_saveState___redArg(v___y_494_, v___y_496_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___y_501_; lean_object* v_a_502_; lean_object* v___x_522_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
lean_inc_ref(v___y_493_);
lean_inc(v___y_492_);
v___x_522_ = lean_apply_6(v_x_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, lean_box(0));
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; uint8_t v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
v___x_524_ = lean_unbox(v_a_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec_ref_known(v___x_522_, 1);
lean_inc(v_a_499_);
v___x_525_ = l_Lean_Meta_SavedState_restore___redArg(v_a_499_, v___y_494_, v___y_496_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_499_);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v___x_525_, 0);
lean_dec(v_unused_533_);
v___x_527_ = v___x_525_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_dec(v___x_525_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v_a_523_);
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_523_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_a_523_);
v_a_534_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_525_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_525_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
lean_inc(v_a_534_);
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
v___y_501_ = v___x_539_;
v_a_502_ = v_a_534_;
goto v___jp_500_;
}
}
}
}
else
{
lean_dec(v_a_523_);
lean_dec(v_a_499_);
return v___x_522_;
}
}
else
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_542_);
v___y_501_ = v___x_522_;
v_a_502_ = v_a_542_;
goto v___jp_500_;
}
v___jp_500_:
{
uint8_t v___x_503_; 
v___x_503_ = l_Lean_Exception_isInterrupt(v_a_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
lean_inc_ref(v_a_502_);
v___x_504_ = l_Lean_Exception_isRuntime(v_a_502_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v___y_501_);
v___x_505_ = l_Lean_Meta_SavedState_restore___redArg(v_a_499_, v___y_494_, v___y_496_);
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
lean_ctor_set(v___x_507_, 0, v_a_502_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_502_);
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
lean_dec_ref(v_a_502_);
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
lean_dec_ref(v_a_502_);
lean_dec(v_a_499_);
return v___y_501_;
}
}
else
{
lean_dec_ref(v_a_502_);
lean_dec(v_a_499_);
return v___y_501_;
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec_ref(v_x_491_);
v_a_543_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_498_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_498_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object* v_msgData_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; lean_object* v_env_566_; uint8_t v___x_567_; lean_object* v_env_568_; lean_object* v___x_569_; lean_object* v_toCold_570_; lean_object* v_mctx_571_; lean_object* v_lctx_572_; lean_object* v_options_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_565_ = lean_st_ref_get(v___y_563_);
v_env_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_ref(v_env_566_);
lean_dec(v___x_565_);
v___x_567_ = 0;
v_env_568_ = l_Lean_Environment_setRecordingDeps(v_env_566_, v___x_567_);
v___x_569_ = lean_st_ref_get(v___y_561_);
v_toCold_570_ = lean_ctor_get(v___y_562_, 0);
v_mctx_571_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_mctx_571_);
lean_dec(v___x_569_);
v_lctx_572_ = lean_ctor_get(v___y_560_, 2);
v_options_573_ = lean_ctor_get(v_toCold_570_, 2);
lean_inc_ref(v_options_573_);
lean_inc_ref(v_lctx_572_);
v___x_574_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_574_, 0, v_env_568_);
lean_ctor_set(v___x_574_, 1, v_mctx_571_);
lean_ctor_set(v___x_574_, 2, v_lctx_572_);
lean_ctor_set(v___x_574_, 3, v_options_573_);
v___x_575_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_msgData_559_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_583_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_584_; double v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_float_of_nat(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_589_, lean_object* v_msg_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_ref_596_; lean_object* v___x_597_; lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_643_; 
v_ref_596_ = lean_ctor_get(v___y_593_, 2);
v___x_597_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_643_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_643_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_643_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v_traceState_603_; lean_object* v_env_604_; lean_object* v_nextMacroScope_605_; lean_object* v_ngen_606_; lean_object* v_auxDeclNGen_607_; lean_object* v_cache_608_; lean_object* v_recordedDeps_609_; lean_object* v_messages_610_; lean_object* v_infoState_611_; lean_object* v_snapshotTasks_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_642_; 
v___x_602_ = lean_st_ref_take(v___y_594_);
v_traceState_603_ = lean_ctor_get(v___x_602_, 4);
v_env_604_ = lean_ctor_get(v___x_602_, 0);
v_nextMacroScope_605_ = lean_ctor_get(v___x_602_, 1);
v_ngen_606_ = lean_ctor_get(v___x_602_, 2);
v_auxDeclNGen_607_ = lean_ctor_get(v___x_602_, 3);
v_cache_608_ = lean_ctor_get(v___x_602_, 5);
v_recordedDeps_609_ = lean_ctor_get(v___x_602_, 6);
v_messages_610_ = lean_ctor_get(v___x_602_, 7);
v_infoState_611_ = lean_ctor_get(v___x_602_, 8);
v_snapshotTasks_612_ = lean_ctor_get(v___x_602_, 9);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_642_ == 0)
{
v___x_614_ = v___x_602_;
v_isShared_615_ = v_isSharedCheck_642_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snapshotTasks_612_);
lean_inc(v_infoState_611_);
lean_inc(v_messages_610_);
lean_inc(v_recordedDeps_609_);
lean_inc(v_cache_608_);
lean_inc(v_traceState_603_);
lean_inc(v_auxDeclNGen_607_);
lean_inc(v_ngen_606_);
lean_inc(v_nextMacroScope_605_);
lean_inc(v_env_604_);
lean_dec(v___x_602_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_642_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
uint64_t v_tid_616_; lean_object* v_traces_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_641_; 
v_tid_616_ = lean_ctor_get_uint64(v_traceState_603_, sizeof(void*)*1);
v_traces_617_ = lean_ctor_get(v_traceState_603_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_traceState_603_);
if (v_isSharedCheck_641_ == 0)
{
v___x_619_ = v_traceState_603_;
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_traces_617_);
lean_dec(v_traceState_603_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; double v___x_623_; uint8_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_621_ = lean_box(0);
v___x_622_ = lean_box(0);
v___x_623_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_624_ = 0;
v___x_625_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_626_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_626_, 0, v_cls_589_);
lean_ctor_set(v___x_626_, 1, v___x_622_);
lean_ctor_set(v___x_626_, 2, v___x_625_);
lean_ctor_set_float(v___x_626_, sizeof(void*)*3, v___x_623_);
lean_ctor_set_float(v___x_626_, sizeof(void*)*3 + 8, v___x_623_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*3 + 16, v___x_624_);
v___x_627_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_628_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v_a_598_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_inc(v_ref_596_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_ref_596_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = l_Lean_PersistentArray_push___redArg(v_traces_617_, v___x_629_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_630_);
v___x_632_ = v___x_619_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_630_);
lean_ctor_set_uint64(v_reuseFailAlloc_640_, sizeof(void*)*1, v_tid_616_);
v___x_632_ = v_reuseFailAlloc_640_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 4, v___x_632_);
v___x_634_ = v___x_614_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_env_604_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_nextMacroScope_605_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_ngen_606_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_auxDeclNGen_607_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_639_, 5, v_cache_608_);
lean_ctor_set(v_reuseFailAlloc_639_, 6, v_recordedDeps_609_);
lean_ctor_set(v_reuseFailAlloc_639_, 7, v_messages_610_);
lean_ctor_set(v_reuseFailAlloc_639_, 8, v_infoState_611_);
lean_ctor_set(v_reuseFailAlloc_639_, 9, v_snapshotTasks_612_);
v___x_634_ = v_reuseFailAlloc_639_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_st_ref_put(v___y_594_, v___x_634_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_621_);
v___x_637_ = v___x_600_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_621_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_644_, lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_644_, v_msg_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_659_, lean_object* v_mvarId_660_, lean_object* v_fields_661_, lean_object* v_sz_662_, lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
size_t v_sz_boxed_672_; size_t v___x_15997__boxed_673_; uint8_t v___x_15999__boxed_674_; lean_object* v_res_675_; 
v_sz_boxed_672_ = lean_unbox_usize(v_sz_662_);
lean_dec(v_sz_662_);
v___x_15997__boxed_673_ = lean_unbox_usize(v___x_663_);
lean_dec(v___x_663_);
v___x_15999__boxed_674_ = lean_unbox(v___x_665_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_659_, v_mvarId_660_, v_fields_661_, v_sz_boxed_672_, v___x_15997__boxed_673_, v___x_664_, v___x_15999__boxed_674_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v_fields_661_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_676_, lean_object* v_as_677_, size_t v_sz_678_, size_t v_i_679_, lean_object* v_b_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_lt(v_i_679_, v_sz_678_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v_b_680_);
return v___x_688_;
}
else
{
lean_object* v_a_689_; lean_object* v_toInductionSubgoal_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v_b_680_);
v_a_689_ = lean_array_uget(v_as_677_, v_i_679_);
v_toInductionSubgoal_690_ = lean_ctor_get(v_a_689_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v_a_689_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_a_689_, 1);
lean_dec(v_unused_732_);
v___x_692_ = v_a_689_;
v_isShared_693_ = v_isSharedCheck_731_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_toInductionSubgoal_690_);
lean_dec(v_a_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_731_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_mvarId_694_; lean_object* v_fields_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; size_t v_sz_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___f_704_; lean_object* v___x_705_; 
v_mvarId_694_ = lean_ctor_get(v_toInductionSubgoal_690_, 0);
lean_inc_n(v_mvarId_694_, 2);
v_fields_695_ = lean_ctor_get(v_toInductionSubgoal_690_, 1);
lean_inc_ref(v_fields_695_);
v___x_696_ = lean_box(0);
v___x_697_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_eq(v_val_676_, v___x_698_);
v_sz_700_ = lean_array_size(v_fields_695_);
v___x_701_ = lean_box_usize(v_sz_700_);
v___x_702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_703_ = lean_box(v___x_699_);
v___f_704_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_704_, 0, v_toInductionSubgoal_690_);
lean_closure_set(v___f_704_, 1, v_mvarId_694_);
lean_closure_set(v___f_704_, 2, v_fields_695_);
lean_closure_set(v___f_704_, 3, v___x_701_);
lean_closure_set(v___f_704_, 4, v___x_702_);
lean_closure_set(v___f_704_, 5, v___x_697_);
lean_closure_set(v___f_704_, 6, v___x_703_);
v___x_705_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_694_, v___f_704_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_722_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_722_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
uint8_t v___x_710_; 
v___x_710_ = lean_unbox(v_a_706_);
lean_dec(v_a_706_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_711_ = lean_box(v___x_699_);
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_696_);
lean_ctor_set(v___x_692_, 0, v___x_712_);
v___x_714_ = v___x_692_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_696_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_714_);
v___x_716_ = v___x_708_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
size_t v___x_719_; size_t v___x_720_; 
lean_del_object(v___x_708_);
lean_del_object(v___x_692_);
v___x_719_ = ((size_t)1ULL);
v___x_720_ = lean_usize_add(v_i_679_, v___x_719_);
v_i_679_ = v___x_720_;
v_b_680_ = v___x_697_;
goto _start;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_del_object(v___x_692_);
v_a_723_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_705_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_705_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
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
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_744_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_745_ = l_Lean_Name_append(v___x_744_, v___x_743_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_749_, lean_object* v_fvarId_750_, lean_object* v___x_751_, uint8_t v___x_752_, lean_object* v___x_753_, lean_object* v_val_754_, uint8_t v___x_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_MVarId_cases(v_mvarId_749_, v_fvarId_750_, v___x_751_, v___x_752_, v___x_753_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v_toCold_796_; lean_object* v_options_797_; uint8_t v_hasTrace_798_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v_toCold_796_ = lean_ctor_get(v___y_759_, 0);
v_options_797_ = lean_ctor_get(v_toCold_796_, 2);
v_hasTrace_798_ = lean_ctor_get_uint8(v_options_797_, sizeof(void*)*1);
if (v_hasTrace_798_ == 0)
{
v___y_765_ = v___y_756_;
v___y_766_ = v___y_757_;
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
goto v___jp_764_;
}
else
{
lean_object* v_inheritedTraceOptions_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_inheritedTraceOptions_799_ = lean_ctor_get(v_toCold_796_, 11);
v___x_800_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_801_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_802_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_799_, v_options_797_, v___x_801_);
if (v___x_802_ == 0)
{
v___y_765_ = v___y_756_;
v___y_766_ = v___y_757_;
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
goto v___jp_764_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_803_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_804_ = lean_array_get_size(v_a_763_);
v___x_805_ = l_Nat_reprFast(v___x_804_);
v___x_806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
v___x_807_ = l_Lean_MessageData_ofFormat(v___x_806_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_803_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_800_, v___x_808_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_dec_ref_known(v___x_809_, 1);
v___y_765_ = v___y_756_;
v___y_766_ = v___y_757_;
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
goto v___jp_764_;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_a_763_);
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
v___jp_764_:
{
lean_object* v___x_770_; size_t v_sz_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_771_ = lean_array_size(v_a_763_);
v___x_772_ = ((size_t)0ULL);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_754_, v_a_763_, v_sz_771_, v___x_772_, v___x_770_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v_a_763_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_787_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_787_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_787_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_787_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_fst_778_; 
v_fst_778_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_fst_778_);
lean_dec(v_a_774_);
if (lean_obj_tag(v_fst_778_) == 0)
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_box(v___x_755_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_779_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
lean_object* v_val_783_; lean_object* v___x_785_; 
v_val_783_ = lean_ctor_get(v_fst_778_, 0);
lean_inc(v_val_783_);
lean_dec_ref_known(v_fst_778_, 1);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_val_783_);
v___x_785_ = v___x_776_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_val_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_773_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_773_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_864_; 
v_a_818_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_864_ == 0)
{
v___x_820_ = v___x_762_;
v_isShared_821_ = v_isSharedCheck_864_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_762_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_864_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___x_822_; 
v___x_822_ = l_Lean_Exception_isInterrupt(v_a_818_);
if (v___x_822_ == 0)
{
uint8_t v___x_823_; 
lean_inc(v_a_818_);
v___x_823_ = l_Lean_Exception_isRuntime(v_a_818_);
if (v___x_823_ == 0)
{
lean_object* v_toCold_824_; lean_object* v_options_825_; uint8_t v_hasTrace_826_; 
v_toCold_824_ = lean_ctor_get(v___y_759_, 0);
v_options_825_ = lean_ctor_get(v_toCold_824_, 2);
v_hasTrace_826_ = lean_ctor_get_uint8(v_options_825_, sizeof(void*)*1);
if (v_hasTrace_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec(v_a_818_);
v___x_827_ = lean_box(v___x_752_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 0);
lean_ctor_set(v___x_820_, 0, v___x_827_);
v___x_829_ = v___x_820_;
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
v_inheritedTraceOptions_831_ = lean_ctor_get(v_toCold_824_, 11);
v___x_832_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_833_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_831_, v_options_825_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_dec(v_a_818_);
v___x_835_ = lean_box(v___x_752_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 0);
lean_ctor_set(v___x_820_, 0, v___x_835_);
v___x_837_ = v___x_820_;
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
lean_del_object(v___x_820_);
v___x_839_ = l_Lean_Exception_toMessageData(v_a_818_);
v___x_840_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_832_, v___x_839_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
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
v___x_844_ = lean_box(v___x_752_);
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
if (v_isShared_821_ == 0)
{
v___x_859_ = v___x_820_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_818_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_object* v___x_862_; 
if (v_isShared_821_ == 0)
{
v___x_862_ = v___x_820_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_818_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_865_, lean_object* v_fvarId_866_, lean_object* v___x_867_, lean_object* v___x_868_, lean_object* v___x_869_, lean_object* v_val_870_, lean_object* v___x_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v___x_16119__boxed_878_; uint8_t v___x_16122__boxed_879_; lean_object* v_res_880_; 
v___x_16119__boxed_878_ = lean_unbox(v___x_868_);
v___x_16122__boxed_879_ = lean_unbox(v___x_871_);
v_res_880_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_865_, v_fvarId_866_, v___x_867_, v___x_16119__boxed_878_, v___x_869_, v_val_870_, v___x_16122__boxed_879_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
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
uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; 
v___x_899_ = 1;
v___x_900_ = lean_st_ref_take(v_a_886_);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_sub(v___x_900_, v___x_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_st_ref_put(v_a_886_, v___x_902_);
v___x_904_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_905_ = lean_box(0);
v___x_906_ = lean_box(v___x_898_);
v___x_907_ = lean_box(v___x_899_);
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
lean_object* v_toCold_910_; lean_object* v_options_911_; uint8_t v_hasTrace_912_; 
lean_dec(v___x_896_);
lean_dec(v_fvarId_885_);
lean_dec(v_mvarId_884_);
v_toCold_910_ = lean_ctor_get(v_a_889_, 0);
v_options_911_ = lean_ctor_get(v_toCold_910_, 2);
v_hasTrace_912_ = lean_ctor_get_uint8(v_options_911_, sizeof(void*)*1);
if (v_hasTrace_912_ == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v_inheritedTraceOptions_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_inheritedTraceOptions_913_ = lean_ctor_get(v_toCold_910_, 11);
v___x_914_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_915_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_916_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_913_, v_options_911_, v___x_915_);
if (v___x_916_ == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_918_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_914_, v___x_917_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_dec_ref_known(v___x_918_, 1);
goto v___jp_892_;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_927_, lean_object* v___x_928_, lean_object* v_as_929_, size_t v_sz_930_, size_t v_i_931_, lean_object* v_b_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_a_940_; uint8_t v___x_944_; 
v___x_944_ = lean_usize_dec_lt(v_i_931_, v_sz_930_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
lean_dec(v___x_928_);
lean_dec_ref(v___x_927_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v_b_932_);
return v___x_945_;
}
else
{
lean_object* v_subst_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v_a_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
lean_dec_ref(v_b_932_);
v_subst_946_ = lean_ctor_get(v___x_927_, 2);
v___x_947_ = lean_box(0);
v___x_948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_949_ = lean_array_uget_borrowed(v_as_929_, v_i_931_);
lean_inc(v_subst_946_);
v___x_950_ = l_Lean_Meta_FVarSubst_apply(v_subst_946_, v_a_949_);
v___x_951_ = l_Lean_Expr_isFVar(v___x_950_);
if (v___x_951_ == 0)
{
lean_dec_ref(v___x_950_);
v_a_940_ = v___x_948_;
goto v___jp_939_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = l_Lean_Expr_fvarId_x21(v___x_950_);
lean_dec_ref(v___x_950_);
lean_inc(v___x_952_);
v___x_953_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_952_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; uint8_t v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = lean_unbox(v_a_954_);
lean_dec(v_a_954_);
if (v___x_955_ == 0)
{
lean_dec(v___x_952_);
v_a_940_ = v___x_948_;
goto v___jp_939_;
}
else
{
lean_object* v___x_956_; 
lean_inc(v___x_928_);
v___x_956_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_928_, v___x_952_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_968_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_968_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
uint8_t v___x_961_; 
v___x_961_ = lean_unbox(v_a_957_);
lean_dec(v_a_957_);
if (v___x_961_ == 0)
{
lean_del_object(v___x_959_);
v_a_940_ = v___x_948_;
goto v___jp_939_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v___x_928_);
lean_dec_ref(v___x_927_);
v___x_962_ = lean_box(v___x_951_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_947_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_964_);
v___x_966_ = v___x_959_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec(v___x_928_);
lean_dec_ref(v___x_927_);
v_a_969_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_956_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_956_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v___x_952_);
lean_dec(v___x_928_);
lean_dec_ref(v___x_927_);
v_a_977_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_953_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_953_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
v___jp_939_:
{
size_t v___x_941_; size_t v___x_942_; 
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_add(v_i_931_, v___x_941_);
lean_inc_ref(v_a_940_);
v_i_931_ = v___x_942_;
v_b_932_ = v_a_940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_985_, lean_object* v_mvarId_986_, lean_object* v_fields_987_, size_t v_sz_988_, size_t v___x_989_, lean_object* v___x_990_, uint8_t v___x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_985_, v_mvarId_986_, v_fields_987_, v_sz_988_, v___x_989_, v___x_990_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1012_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_fst_1003_; 
v_fst_1003_ = lean_ctor_get(v_a_999_, 0);
lean_inc(v_fst_1003_);
lean_dec(v_a_999_);
if (lean_obj_tag(v_fst_1003_) == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_box(v___x_991_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1006_ = v___x_1001_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1010_; 
v_val_1008_ = lean_ctor_get(v_fst_1003_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v_fst_1003_, 1);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_val_1008_);
v___x_1010_ = v___x_1001_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_val_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_998_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_998_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1021_, lean_object* v_as_1022_, lean_object* v_sz_1023_, lean_object* v_i_1024_, lean_object* v_b_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
size_t v_sz_boxed_1032_; size_t v_i_boxed_1033_; lean_object* v_res_1034_; 
v_sz_boxed_1032_ = lean_unbox_usize(v_sz_1023_);
lean_dec(v_sz_1023_);
v_i_boxed_1033_ = lean_unbox_usize(v_i_1024_);
lean_dec(v_i_1024_);
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1021_, v_as_1022_, v_sz_boxed_1032_, v_i_boxed_1033_, v_b_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v_as_1022_);
lean_dec(v_val_1021_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_as_1037_, lean_object* v_sz_1038_, lean_object* v_i_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
size_t v_sz_boxed_1047_; size_t v_i_boxed_1048_; lean_object* v_res_1049_; 
v_sz_boxed_1047_ = lean_unbox_usize(v_sz_1038_);
lean_dec(v_sz_1038_);
v_i_boxed_1048_ = lean_unbox_usize(v_i_1039_);
lean_dec(v_i_1039_);
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1035_, v___x_1036_, v_as_1037_, v_sz_boxed_1047_, v_i_boxed_1048_, v_b_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v_as_1037_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1050_, lean_object* v_fvarId_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1050_, v_fvarId_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1059_, lean_object* v_msg_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1059_, v_msg_1060_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1068_, lean_object* v_msg_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1068_, v_msg_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Meta_saveState___redArg(v___y_1079_, v___y_1081_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___y_1086_; lean_object* v_a_1087_; lean_object* v___x_1107_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
v___x_1107_ = lean_apply_5(v_x_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, lean_box(0));
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
lean_inc(v_a_1084_);
v___x_1110_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1084_, v___y_1079_, v___y_1081_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v_a_1084_);
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
v___y_1086_ = v___x_1124_;
v_a_1087_ = v_a_1119_;
goto v___jp_1085_;
}
}
}
}
else
{
lean_dec(v_a_1108_);
lean_dec(v_a_1084_);
return v___x_1107_;
}
}
else
{
lean_object* v_a_1127_; 
v_a_1127_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1127_);
v___y_1086_ = v___x_1107_;
v_a_1087_ = v_a_1127_;
goto v___jp_1085_;
}
v___jp_1085_:
{
uint8_t v___x_1088_; 
v___x_1088_ = l_Lean_Exception_isInterrupt(v_a_1087_);
if (v___x_1088_ == 0)
{
uint8_t v___x_1089_; 
lean_inc_ref(v_a_1087_);
v___x_1089_ = l_Lean_Exception_isRuntime(v_a_1087_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec_ref(v___y_1086_);
v___x_1090_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1084_, v___y_1079_, v___y_1081_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v___x_1090_, 0);
lean_dec(v_unused_1098_);
v___x_1092_ = v___x_1090_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v___x_1090_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 1);
lean_ctor_set(v___x_1092_, 0, v_a_1087_);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1087_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_a_1087_);
v_a_1099_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1090_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1090_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1084_);
return v___y_1086_;
}
}
else
{
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1084_);
return v___y_1086_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_x_1077_);
v_a_1128_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1083_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1083_);
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
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0(v_x_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1143_, lean_object* v_x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1167_, v_x_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1175_, lean_object* v_mvarId_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1176_, v_x_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_mvarId_1185_, lean_object* v_x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1184_, v_mvarId_1185_, v_x_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1193_, lean_object* v_fuel_1194_, lean_object* v_fvarId_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1222_, lean_object* v_fuel_1223_, lean_object* v_fvarId_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1222_, v_fuel_1223_, v_fvarId_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1231_, lean_object* v___f_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1231_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; uint8_t v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v___x_1240_ = lean_unbox(v_a_1239_);
if (v___x_1240_ == 0)
{
lean_dec_ref(v___f_1232_);
return v___x_1238_;
}
else
{
lean_object* v___x_1241_; 
lean_dec_ref_known(v___x_1238_, 1);
v___x_1241_ = l_Lean_commitWhen___at___00Lean_Meta_elimEmptyInductive_spec__0(v___f_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1242_, lean_object* v___f_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1242_, v___f_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1250_, lean_object* v_fvarId_1251_, lean_object* v_fuel_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; 
lean_inc(v_fvarId_1251_);
lean_inc(v_mvarId_1250_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1258_, 0, v_mvarId_1250_);
lean_closure_set(v___f_1258_, 1, v_fuel_1252_);
lean_closure_set(v___f_1258_, 2, v_fvarId_1251_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1259_, 0, v_fvarId_1251_);
lean_closure_set(v___f_1259_, 1, v___f_1258_);
v___x_1260_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1250_, v___f_1259_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1261_, lean_object* v_fvarId_1262_, lean_object* v_fuel_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_1261_, v_fvarId_1262_, v_fuel_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
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
lean_dec_ref(v_e_1272_);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0(lean_object* v_msg_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___f_1306_; lean_object* v___x_3742__overap_1307_; lean_object* v___x_1308_; 
v___f_1306_ = ((lean_object*)(l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0___closed__0));
v___x_3742__overap_1307_ = lean_panic_fn_borrowed(v___f_1306_, v_msg_1300_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
lean_inc(v___y_1302_);
lean_inc_ref(v___y_1301_);
v___x_1308_ = lean_apply_5(v___x_3742__overap_1307_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, lean_box(0));
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0___boxed(lean_object* v_msg_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0(v_msg_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(lean_object* v_e_1316_, lean_object* v___y_1317_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg___boxed(lean_object* v_e_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v_e_1341_, v___y_1342_);
lean_dec(v___y_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2(lean_object* v_e_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v_e_1345_, v___y_1347_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___boxed(lean_object* v_e_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2(v_e_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg(lean_object* v_k_1359_, uint8_t v_allowLevelAssignments_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg___boxed(lean_object* v_k_1383_, lean_object* v_allowLevelAssignments_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1390_; lean_object* v_res_1391_; 
v_allowLevelAssignments_boxed_1390_ = lean_unbox(v_allowLevelAssignments_1384_);
v_res_1391_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg(v_k_1383_, v_allowLevelAssignments_boxed_1390_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3(lean_object* v_00_u03b1_1392_, lean_object* v_k_1393_, uint8_t v_allowLevelAssignments_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg(v_k_1393_, v_allowLevelAssignments_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_k_1402_, lean_object* v_allowLevelAssignments_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1409_; lean_object* v_res_1410_; 
v_allowLevelAssignments_boxed_1409_ = lean_unbox(v_allowLevelAssignments_1403_);
v_res_1410_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3(v_00_u03b1_1401_, v_k_1402_, v_allowLevelAssignments_boxed_1409_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1(lean_object* v_as_1413_, size_t v_sz_1414_, size_t v_i_1415_, lean_object* v_b_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
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
v___x_1544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___closed__0));
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
v___x_1478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___closed__0));
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1___boxed(lean_object* v_as_1593_, lean_object* v_sz_1594_, lean_object* v_i_1595_, lean_object* v_b_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
size_t v_sz_boxed_1602_; size_t v_i_boxed_1603_; lean_object* v_res_1604_; 
v_sz_boxed_1602_ = lean_unbox_usize(v_sz_1594_);
lean_dec(v_sz_1594_);
v_i_boxed_1603_ = lean_unbox_usize(v_i_1595_);
lean_dec(v_i_1595_);
v_res_1604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1(v_as_1593_, v_sz_boxed_1602_, v_i_boxed_1603_, v_b_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec_ref(v_as_1593_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0(lean_object* v_type_1605_, uint8_t v___x_1606_, lean_object* v_h_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; 
lean_inc_ref(v_type_1605_);
v___x_1613_ = l_Lean_Meta_forallMetaTelescope(v_type_1605_, v___x_1606_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v_fst_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1679_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v_fst_1615_ = lean_ctor_get(v_a_1614_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_a_1614_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v_a_1614_, 1);
lean_dec(v_unused_1680_);
v___x_1617_ = v_a_1614_;
v_isShared_1618_ = v_isSharedCheck_1679_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_fst_1615_);
lean_dec(v_a_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1679_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1619_ = l_Lean_Meta_mkGenDiseqMask(v_type_1605_);
lean_dec_ref(v_type_1605_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_array_get_size(v___x_1619_);
v___x_1622_ = l_Array_toSubarray___redArg(v___x_1619_, v___x_1620_, v___x_1621_);
v___x_1623_ = lean_box(0);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 1, v___x_1622_);
lean_ctor_set(v___x_1617_, 0, v___x_1623_);
v___x_1625_ = v___x_1617_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1622_);
v___x_1625_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
size_t v_sz_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v_sz_1626_ = lean_array_size(v_fst_1615_);
v___x_1627_ = ((size_t)0ULL);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__1(v_fst_1615_, v_sz_1626_, v___x_1627_, v___x_1625_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1669_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1669_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1669_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_fst_1633_; 
v_fst_1633_ = lean_ctor_get(v_a_1629_, 0);
lean_inc(v_fst_1633_);
lean_dec(v_a_1629_);
if (lean_obj_tag(v_fst_1633_) == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1631_);
v___x_1634_ = l_Lean_mkAppN(v_h_1607_, v_fst_1615_);
lean_dec(v_fst_1615_);
v___x_1635_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_1634_, v___y_1609_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1664_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1664_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; 
lean_inc(v_a_1636_);
v___x_1640_ = l_Lean_Meta_hasAssignableMVar(v_a_1636_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1655_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1655_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1655_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_unbox(v_a_1641_);
lean_dec(v_a_1641_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1647_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set_tag(v___x_1638_, 1);
v___x_1647_ = v___x_1638_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1636_);
v___x_1647_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1647_);
v___x_1649_ = v___x_1643_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
lean_object* v___x_1653_; 
lean_del_object(v___x_1638_);
lean_dec(v_a_1636_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1623_);
v___x_1653_ = v___x_1643_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1623_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_del_object(v___x_1638_);
lean_dec(v_a_1636_);
v_a_1656_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1640_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1640_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
else
{
lean_object* v_val_1665_; lean_object* v___x_1667_; 
lean_dec(v_fst_1615_);
lean_dec_ref(v_h_1607_);
v_val_1665_ = lean_ctor_get(v_fst_1633_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v_fst_1633_, 1);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_val_1665_);
v___x_1667_ = v___x_1631_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_val_1665_);
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
lean_dec(v_fst_1615_);
lean_dec_ref(v_h_1607_);
v_a_1670_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1628_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1628_);
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
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_h_1607_);
lean_dec_ref(v_type_1605_);
v_a_1681_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1613_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1613_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0___boxed(lean_object* v_type_1689_, lean_object* v___x_1690_, lean_object* v_h_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
uint8_t v___x_5460__boxed_1697_; lean_object* v_res_1698_; 
v___x_5460__boxed_1697_ = lean_unbox(v___x_1690_);
v_res_1698_ = l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0(v_type_1689_, v___x_5460__boxed_1697_, v_h_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1698_;
}
}
static lean_object* _init_l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1702_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__2));
v___x_1703_ = lean_unsigned_to_nat(2u);
v___x_1704_ = lean_unsigned_to_nat(122u);
v___x_1705_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__1));
v___x_1706_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__0));
v___x_1707_ = l_mkPanicMessageWithDecl(v___x_1706_, v___x_1705_, v___x_1704_, v___x_1703_, v___x_1702_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f(lean_object* v_h_1708_, lean_object* v_type_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_type_1709_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec_ref(v_type_1709_);
lean_dec_ref(v_h_1708_);
v___x_1716_ = lean_obj_once(&l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3, &l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3_once, _init_l_Lean_Meta_mkGenDiseqFalseProof_x3f___closed__3);
v___x_1717_ = l_panic___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__0(v___x_1716_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
return v___x_1717_;
}
else
{
uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___f_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; 
v___x_1718_ = 0;
v___x_1719_ = lean_box(v___x_1718_);
v___f_1720_ = lean_alloc_closure((void*)(l_Lean_Meta_mkGenDiseqFalseProof_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1720_, 0, v_type_1709_);
lean_closure_set(v___f_1720_, 1, v___x_1719_);
lean_closure_set(v___f_1720_, 2, v_h_1708_);
v___x_1721_ = 0;
v___x_1722_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__3___redArg(v___f_1720_, v___x_1721_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqFalseProof_x3f___boxed(lean_object* v_h_1723_, lean_object* v_type_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Meta_mkGenDiseqFalseProof_x3f(v_h_1723_, v_type_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_processGenDiseq(lean_object* v_mvarId_1731_, lean_object* v_localDecl_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_inc_ref(v_localDecl_1732_);
v___x_1738_ = l_Lean_LocalDecl_toExpr(v_localDecl_1732_);
v___x_1739_ = l_Lean_LocalDecl_type(v_localDecl_1732_);
lean_dec_ref(v_localDecl_1732_);
v___x_1740_ = l_Lean_Meta_mkGenDiseqFalseProof_x3f(v___x_1738_, v___x_1739_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1782_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1782_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1782_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
if (lean_obj_tag(v_a_1741_) == 1)
{
lean_object* v_val_1745_; lean_object* v___x_1746_; 
lean_del_object(v___x_1743_);
v_val_1745_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v_a_1741_, 1);
lean_inc(v_mvarId_1731_);
v___x_1746_ = l_Lean_MVarId_getType(v_mvarId_1731_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = l_Lean_Meta_mkFalseElim(v_a_1747_, v_val_1745_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1759_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v___x_1750_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1731_, v_a_1749_, v_a_1734_);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v___x_1750_, 0);
lean_dec(v_unused_1760_);
v___x_1752_ = v___x_1750_;
v_isShared_1753_ = v_isSharedCheck_1759_;
goto v_resetjp_1751_;
}
else
{
lean_dec(v___x_1750_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1759_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1754_ = 1;
v___x_1755_ = lean_box(v___x_1754_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_mvarId_1731_);
v_a_1761_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1748_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1748_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_val_1745_);
lean_dec(v_mvarId_1731_);
v_a_1769_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1746_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1746_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
lean_dec(v_a_1741_);
lean_dec(v_mvarId_1731_);
v___x_1777_ = 0;
v___x_1778_ = lean_box(v___x_1777_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1778_);
v___x_1780_ = v___x_1743_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v_mvarId_1731_);
v_a_1783_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1740_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1740_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1791_, lean_object* v_localDecl_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Meta_processGenDiseq(v_mvarId_1791_, v_localDecl_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(lean_object* v_x_1799_, lean_object* v_x_1800_){
_start:
{
if (lean_obj_tag(v_x_1799_) == 0)
{
if (lean_obj_tag(v_x_1800_) == 0)
{
uint8_t v___x_1801_; 
v___x_1801_ = 1;
return v___x_1801_;
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = 0;
return v___x_1802_;
}
}
else
{
if (lean_obj_tag(v_x_1800_) == 0)
{
uint8_t v___x_1803_; 
v___x_1803_ = 0;
return v___x_1803_;
}
else
{
lean_object* v_val_1804_; uint8_t v___x_1805_; 
v_val_1804_ = lean_ctor_get(v_x_1800_, 0);
v___x_1805_ = lean_unbox(v_val_1804_);
if (v___x_1805_ == 0)
{
lean_object* v_val_1806_; uint8_t v___x_1807_; 
v_val_1806_ = lean_ctor_get(v_x_1799_, 0);
v___x_1807_ = lean_unbox(v_val_1806_);
if (v___x_1807_ == 0)
{
uint8_t v___x_1808_; 
v___x_1808_ = 1;
return v___x_1808_;
}
else
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_unbox(v_val_1804_);
return v___x_1809_;
}
}
else
{
lean_object* v_val_1810_; uint8_t v___x_1811_; 
v_val_1810_ = lean_ctor_get(v_x_1799_, 0);
v___x_1811_ = lean_unbox(v_val_1810_);
return v___x_1811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0___boxed(lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
uint8_t v_res_1814_; lean_object* v_r_1815_; 
v_res_1814_ = l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(v_x_1812_, v_x_1813_);
lean_dec(v_x_1813_);
lean_dec(v_x_1812_);
v_r_1815_ = lean_box(v_res_1814_);
return v_r_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0(lean_object* v_lhs_1819_, lean_object* v_rhs_1820_, lean_object* v_mvarId_1821_, lean_object* v_h_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
lean_inc_ref(v_rhs_1820_);
lean_inc_ref(v_lhs_1819_);
v___x_1828_ = l_Lean_Meta_floatLitValuesEq_x3f(v_lhs_1819_, v_rhs_1820_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1891_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1891_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1891_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
uint8_t v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = 0;
v___x_1834_ = ((lean_object*)(l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___closed__0));
v___x_1835_ = l_instBEqOption_beq___at___00Lean_MVarId_closeIfDistinctFloatLits_spec__0(v_a_1829_, v___x_1834_);
lean_dec(v_a_1829_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_dec_ref(v_h_1822_);
lean_dec(v_mvarId_1821_);
lean_dec_ref(v_rhs_1820_);
lean_dec_ref(v_lhs_1819_);
v___x_1836_ = lean_box(v___x_1833_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1836_);
v___x_1838_ = v___x_1831_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v___x_1840_; 
lean_del_object(v___x_1831_);
v___x_1840_ = l_Lean_Meta_mkEq(v_lhs_1819_, v_rhs_1820_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = l_Lean_mkNot(v_a_1841_);
v___x_1843_ = l_Lean_Meta_mkDecideProof(v___x_1842_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
lean_inc(v_mvarId_1821_);
v___x_1845_ = l_Lean_MVarId_getType(v_mvarId_1821_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = l_Lean_Meta_mkAbsurd(v_a_1846_, v_h_1822_, v_a_1844_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v___x_1849_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1821_, v_a_1848_, v___y_1824_);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1858_);
v___x_1851_ = v___x_1849_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_dec(v___x_1849_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_box(v___x_1835_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_mvarId_1821_);
v_a_1859_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1847_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1847_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_a_1844_);
lean_dec_ref(v_h_1822_);
lean_dec(v_mvarId_1821_);
v_a_1867_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1845_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1845_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v_h_1822_);
lean_dec(v_mvarId_1821_);
v_a_1875_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1843_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1843_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref(v_h_1822_);
lean_dec(v_mvarId_1821_);
v_a_1883_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1840_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1840_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec_ref(v_h_1822_);
lean_dec(v_mvarId_1821_);
lean_dec_ref(v_rhs_1820_);
lean_dec_ref(v_lhs_1819_);
v_a_1892_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1828_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1828_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___boxed(lean_object* v_lhs_1900_, lean_object* v_rhs_1901_, lean_object* v_mvarId_1902_, lean_object* v_h_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_MVarId_closeIfDistinctFloatLits___lam__0(v_lhs_1900_, v_rhs_1901_, v_mvarId_1902_, v_h_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits(lean_object* v_mvarId_1910_, lean_object* v_h_1911_, lean_object* v_lhs_1912_, lean_object* v_rhs_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___f_1919_; lean_object* v___x_1920_; 
lean_inc(v_mvarId_1910_);
v___f_1919_ = lean_alloc_closure((void*)(l_Lean_MVarId_closeIfDistinctFloatLits___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1919_, 0, v_lhs_1912_);
lean_closure_set(v___f_1919_, 1, v_rhs_1913_);
lean_closure_set(v___f_1919_, 2, v_mvarId_1910_);
lean_closure_set(v___f_1919_, 3, v_h_1911_);
v___x_1920_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1910_, v___f_1919_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_closeIfDistinctFloatLits___boxed(lean_object* v_mvarId_1921_, lean_object* v_h_1922_, lean_object* v_lhs_1923_, lean_object* v_rhs_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_MVarId_closeIfDistinctFloatLits(v_mvarId_1921_, v_h_1922_, v_lhs_1923_, v_rhs_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
return v_res_1930_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_box(0);
v___x_1943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1944_ = l_Lean_mkConst(v___x_1943_, v___x_1942_);
return v___x_1944_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1945_; lean_object* v_dummy_1946_; 
v___x_1945_ = lean_box(0);
v_dummy_1946_ = l_Lean_Expr_sort___override(v___x_1945_);
return v_dummy_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1947_, lean_object* v_mvarId_1948_, lean_object* v_as_1949_, size_t v_sz_1950_, size_t v_i_1951_, lean_object* v_b_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_usize_dec_lt(v_i_1951_, v_sz_1950_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_b_1952_);
return v___x_1959_;
}
else
{
lean_object* v_snd_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2541_; 
v_snd_1960_ = lean_ctor_get(v_b_1952_, 1);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_b_1952_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v_b_1952_, 0);
lean_dec(v_unused_2542_);
v___x_1962_ = v_b_1952_;
v_isShared_1963_ = v_isSharedCheck_2541_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snd_1960_);
lean_dec(v_b_1952_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2541_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_a_1965_; lean_object* v___x_1971_; lean_object* v_a_1973_; lean_object* v_a_1978_; 
v___x_1971_ = lean_box(0);
v_a_1978_ = lean_array_uget(v_as_1949_, v_i_1951_);
if (lean_obj_tag(v_a_1978_) == 0)
{
lean_del_object(v___x_1962_);
v_a_1973_ = v_snd_1960_;
goto v___jp_1972_;
}
else
{
lean_object* v_val_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2540_; 
v_val_1979_ = lean_ctor_get(v_a_1978_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_a_1978_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_1981_ = v_a_1978_;
v_isShared_1982_ = v_isSharedCheck_2540_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_val_1979_);
lean_dec(v_a_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2540_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___y_1986_; uint8_t v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; uint8_t v___x_2011_; 
v___x_1983_ = lean_box(0);
v___x_1984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2011_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1979_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; uint8_t v___y_2014_; uint8_t v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; uint8_t v___y_2040_; uint8_t v___y_2041_; lean_object* v___y_2042_; lean_object* v_a_2043_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; uint8_t v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; uint8_t v___y_2093_; uint8_t v_isHEq_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; uint8_t v_isEq_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___x_2477_; 
v___x_2012_ = l_Lean_LocalDecl_type(v_val_1979_);
lean_inc_ref(v___x_2012_);
v___x_2477_ = l_Lean_Meta_matchNot_x3f(v___x_2012_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
if (lean_obj_tag(v_a_2478_) == 1)
{
lean_object* v_val_2479_; lean_object* v___x_2480_; 
v_val_2479_ = lean_ctor_get(v_a_2478_, 0);
lean_inc(v_val_2479_);
lean_dec_ref_known(v_a_2478_, 1);
v___x_2480_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2479_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
if (lean_obj_tag(v_a_2481_) == 1)
{
lean_object* v_val_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2523_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec_ref(v_config_1947_);
v_val_2482_ = lean_ctor_get(v_a_2481_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_a_2481_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2484_ = v_a_2481_;
v_isShared_2485_ = v_isSharedCheck_2523_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_val_2482_);
lean_dec(v_a_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2523_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; 
lean_inc(v_mvarId_1948_);
v___x_2486_ = l_Lean_MVarId_getType(v_mvarId_1948_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2488_ = l_Lean_LocalDecl_toExpr(v_val_1979_);
v___x_2489_ = l_Lean_mkFVar(v_val_2482_);
v___x_2490_ = l_Lean_Expr_app___override(v___x_2488_, v___x_2489_);
v___x_2491_ = l_Lean_Meta_mkFalseElim(v_a_2487_, v___x_2490_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2493_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2493_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1948_, v_a_2492_, v___y_1954_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_dec_ref_known(v___x_2493_, 1);
v___x_2494_ = lean_box(v___x_1958_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2494_);
v___x_2496_ = v___x_2484_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_1983_);
v_a_1965_ = v___x_2497_;
goto v___jp_1964_;
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_del_object(v___x_2484_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_2499_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2493_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2493_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_del_object(v___x_2484_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2507_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2491_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2491_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_del_object(v___x_2484_);
lean_dec(v_val_2482_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2515_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2486_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2486_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
else
{
lean_dec(v_a_2481_);
v___y_2343_ = v___y_1953_;
v___y_2344_ = v___y_1954_;
v___y_2345_ = v___y_1955_;
v___y_2346_ = v___y_1956_;
goto v___jp_2342_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2524_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2480_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2480_);
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
lean_dec(v_a_2478_);
v___y_2343_ = v___y_1953_;
v___y_2344_ = v___y_1954_;
v___y_2345_ = v___y_1955_;
v___y_2346_ = v___y_1956_;
goto v___jp_2342_;
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2532_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2477_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2477_);
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
v___jp_2013_:
{
uint8_t v_genDiseq_2020_; 
v_genDiseq_2020_ = lean_ctor_get_uint8(v_config_1947_, sizeof(void*)*1 + 2);
if (v_genDiseq_2020_ == 0)
{
lean_dec_ref(v___x_2012_);
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
goto v___jp_1985_;
}
else
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2012_);
lean_dec_ref(v___x_2012_);
if (v___x_2021_ == 0)
{
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2022_; 
lean_inc(v_val_1979_);
lean_inc(v_mvarId_1948_);
v___x_2022_ = l_Lean_Meta_processGenDiseq(v_mvarId_1948_, v_val_1979_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; uint8_t v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = lean_unbox(v_a_2023_);
lean_dec(v_a_2023_);
if (v___x_2024_ == 0)
{
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2018_;
v___y_1991_ = v___y_2019_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v___x_2025_ = lean_box(v___x_1958_);
v___x_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v___x_1983_);
v_a_1965_ = v___x_2027_;
goto v___jp_1964_;
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2028_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2022_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2022_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
v___jp_2036_:
{
uint8_t v___x_2044_; 
v___x_2044_ = l_Lean_Exception_isInterrupt(v_a_2043_);
if (v___x_2044_ == 0)
{
uint8_t v___x_2045_; 
lean_inc_ref(v_a_2043_);
v___x_2045_ = l_Lean_Exception_isRuntime(v_a_2043_);
if (v___x_2045_ == 0)
{
lean_dec_ref(v_a_2043_);
v___y_2014_ = v___y_2040_;
v___y_2015_ = v___y_2041_;
v___y_2016_ = v___y_2038_;
v___y_2017_ = v___y_2039_;
v___y_2018_ = v___y_2042_;
v___y_2019_ = v___y_2037_;
goto v___jp_2013_;
}
else
{
lean_object* v___x_2046_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_a_2043_);
return v___x_2046_;
}
}
else
{
lean_object* v___x_2047_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_a_2043_);
return v___x_2047_;
}
}
v___jp_2048_:
{
if (lean_obj_tag(v___y_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v_a_2057_ = lean_ctor_get(v___y_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___y_2056_, 1);
v___x_2058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2059_ = l_Lean_Expr_isConstOf(v_a_2057_, v___x_2058_);
lean_dec(v_a_2057_);
if (v___x_2059_ == 0)
{
lean_dec_ref(v___y_2051_);
v___y_2014_ = v___y_2053_;
v___y_2015_ = v___y_2054_;
v___y_2016_ = v___y_2050_;
v___y_2017_ = v___y_2052_;
v___y_2018_ = v___y_2055_;
v___y_2019_ = v___y_2049_;
goto v___jp_2013_;
}
else
{
lean_object* v___x_2060_; 
lean_inc_ref(v___y_2051_);
v___x_2060_ = l_Lean_Meta_mkEqRefl(v___y_2051_, v___y_2050_, v___y_2052_, v___y_2055_, v___y_2049_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; lean_object* v_dummy_2063_; lean_object* v_nargs_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2063_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2064_ = l_Lean_Expr_getAppNumArgs(v___y_2051_);
lean_inc(v_nargs_2064_);
v___x_2065_ = lean_mk_array(v_nargs_2064_, v_dummy_2063_);
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = lean_nat_sub(v_nargs_2064_, v___x_2066_);
lean_dec(v_nargs_2064_);
v___x_2068_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2051_, v___x_2065_, v___x_2067_);
v___x_2069_ = lean_array_push(v___x_2068_, v_a_2061_);
v___x_2070_ = l_Lean_mkAppN(v___x_2062_, v___x_2069_);
lean_dec_ref(v___x_2069_);
lean_inc(v_mvarId_1948_);
v___x_2071_ = l_Lean_MVarId_getType(v_mvarId_1948_, v___y_2050_, v___y_2052_, v___y_2055_, v___y_2049_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
lean_inc(v_val_1979_);
v___x_2073_ = l_Lean_LocalDecl_toExpr(v_val_1979_);
v___x_2074_ = l_Lean_Meta_mkAbsurd(v_a_2072_, v___x_2073_, v___x_2070_, v___y_2050_, v___y_2052_, v___y_2055_, v___y_2049_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2074_, 1);
lean_inc(v_mvarId_1948_);
v___x_2076_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1948_, v_a_2075_, v___y_2052_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2076_, 0);
lean_dec(v_unused_2086_);
v___x_2078_ = v___x_2076_;
v_isShared_2079_ = v_isSharedCheck_2085_;
goto v_resetjp_2077_;
}
else
{
lean_dec(v___x_2076_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2085_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_box(v___x_1958_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 1);
lean_ctor_set(v___x_2078_, 0, v___x_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_1983_);
v_a_1965_ = v___x_2083_;
goto v___jp_1964_;
}
}
}
else
{
lean_object* v_a_2087_; 
v_a_2087_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2076_, 1);
v___y_2037_ = v___y_2049_;
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2052_;
v___y_2040_ = v___y_2053_;
v___y_2041_ = v___y_2054_;
v___y_2042_ = v___y_2055_;
v_a_2043_ = v_a_2087_;
goto v___jp_2036_;
}
}
else
{
lean_object* v_a_2088_; 
v_a_2088_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2074_, 1);
v___y_2037_ = v___y_2049_;
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2052_;
v___y_2040_ = v___y_2053_;
v___y_2041_ = v___y_2054_;
v___y_2042_ = v___y_2055_;
v_a_2043_ = v_a_2088_;
goto v___jp_2036_;
}
}
else
{
lean_object* v_a_2089_; 
lean_dec_ref(v___x_2070_);
v_a_2089_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2071_, 1);
v___y_2037_ = v___y_2049_;
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2052_;
v___y_2040_ = v___y_2053_;
v___y_2041_ = v___y_2054_;
v___y_2042_ = v___y_2055_;
v_a_2043_ = v_a_2089_;
goto v___jp_2036_;
}
}
else
{
lean_object* v_a_2090_; 
lean_dec_ref(v___y_2051_);
v_a_2090_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2060_, 1);
v___y_2037_ = v___y_2049_;
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2052_;
v___y_2040_ = v___y_2053_;
v___y_2041_ = v___y_2054_;
v___y_2042_ = v___y_2055_;
v_a_2043_ = v_a_2090_;
goto v___jp_2036_;
}
}
}
else
{
lean_object* v_a_2091_; 
lean_dec_ref(v___y_2051_);
v_a_2091_ = lean_ctor_get(v___y_2056_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___y_2056_, 1);
v___y_2037_ = v___y_2049_;
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2052_;
v___y_2040_ = v___y_2053_;
v___y_2041_ = v___y_2054_;
v___y_2042_ = v___y_2055_;
v_a_2043_ = v_a_2091_;
goto v___jp_2036_;
}
}
v___jp_2092_:
{
uint8_t v_useDecide_2099_; 
v_useDecide_2099_ = lean_ctor_get_uint8(v_config_1947_, sizeof(void*)*1);
if (v_useDecide_2099_ == 0)
{
v___y_2014_ = v_isHEq_2094_;
v___y_2015_ = v___y_2093_;
v___y_2016_ = v___y_2095_;
v___y_2017_ = v___y_2096_;
v___y_2018_ = v___y_2097_;
v___y_2019_ = v___y_2098_;
goto v___jp_2013_;
}
else
{
uint8_t v___x_2100_; 
v___x_2100_ = l_Lean_Expr_hasFVar(v___x_2012_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_inc_ref(v___x_2012_);
v___x_2101_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_2012_, v___y_2096_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; uint8_t v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = l_Lean_Expr_hasMVar(v_a_2102_);
if (v___x_2103_ == 0)
{
uint8_t v___x_2104_; 
v___x_2104_ = l_Lean_Expr_hasFVar(v_a_2102_);
lean_dec(v_a_2102_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
lean_inc_ref(v___x_2012_);
v___x_2105_ = l_Lean_Meta_mkDecide(v___x_2012_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; uint8_t v_transparency_2108_; uint8_t v___x_2109_; uint8_t v___x_2110_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = l_Lean_Meta_Context_config(v___y_2095_);
v_transparency_2108_ = lean_ctor_get_uint8(v___x_2107_, 9);
lean_dec_ref(v___x_2107_);
v___x_2109_ = 1;
v___x_2110_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2108_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_object* v_keyedConfig_2111_; uint8_t v_trackZetaDelta_2112_; lean_object* v_zetaDeltaSet_2113_; lean_object* v_lctx_2114_; lean_object* v_localInstances_2115_; lean_object* v_defEqCtx_x3f_2116_; lean_object* v_synthPendingDepth_2117_; lean_object* v_customCanUnfoldPredicate_x3f_2118_; uint8_t v_univApprox_2119_; uint8_t v_inTypeClassResolution_2120_; uint8_t v_cacheInferType_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_keyedConfig_2111_ = lean_ctor_get(v___y_2095_, 0);
v_trackZetaDelta_2112_ = lean_ctor_get_uint8(v___y_2095_, sizeof(void*)*7);
v_zetaDeltaSet_2113_ = lean_ctor_get(v___y_2095_, 1);
v_lctx_2114_ = lean_ctor_get(v___y_2095_, 2);
v_localInstances_2115_ = lean_ctor_get(v___y_2095_, 3);
v_defEqCtx_x3f_2116_ = lean_ctor_get(v___y_2095_, 4);
v_synthPendingDepth_2117_ = lean_ctor_get(v___y_2095_, 5);
v_customCanUnfoldPredicate_x3f_2118_ = lean_ctor_get(v___y_2095_, 6);
v_univApprox_2119_ = lean_ctor_get_uint8(v___y_2095_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2120_ = lean_ctor_get_uint8(v___y_2095_, sizeof(void*)*7 + 2);
v_cacheInferType_2121_ = lean_ctor_get_uint8(v___y_2095_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2111_);
v___x_2122_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2109_, v_keyedConfig_2111_);
lean_inc(v_customCanUnfoldPredicate_x3f_2118_);
lean_inc(v_synthPendingDepth_2117_);
lean_inc(v_defEqCtx_x3f_2116_);
lean_inc_ref(v_localInstances_2115_);
lean_inc_ref(v_lctx_2114_);
lean_inc(v_zetaDeltaSet_2113_);
v___x_2123_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v_zetaDeltaSet_2113_);
lean_ctor_set(v___x_2123_, 2, v_lctx_2114_);
lean_ctor_set(v___x_2123_, 3, v_localInstances_2115_);
lean_ctor_set(v___x_2123_, 4, v_defEqCtx_x3f_2116_);
lean_ctor_set(v___x_2123_, 5, v_synthPendingDepth_2117_);
lean_ctor_set(v___x_2123_, 6, v_customCanUnfoldPredicate_x3f_2118_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*7, v_trackZetaDelta_2112_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*7 + 1, v_univApprox_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*7 + 3, v_cacheInferType_2121_);
lean_inc(v___y_2098_);
lean_inc_ref(v___y_2097_);
lean_inc(v___y_2096_);
lean_inc(v_a_2106_);
v___x_2124_ = lean_whnf(v_a_2106_, v___x_2123_, v___y_2096_, v___y_2097_, v___y_2098_);
v___y_2049_ = v___y_2098_;
v___y_2050_ = v___y_2095_;
v___y_2051_ = v_a_2106_;
v___y_2052_ = v___y_2096_;
v___y_2053_ = v_isHEq_2094_;
v___y_2054_ = v___y_2093_;
v___y_2055_ = v___y_2097_;
v___y_2056_ = v___x_2124_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2125_; 
lean_inc(v___y_2098_);
lean_inc_ref(v___y_2097_);
lean_inc(v___y_2096_);
lean_inc_ref(v___y_2095_);
lean_inc(v_a_2106_);
v___x_2125_ = lean_whnf(v_a_2106_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
v___y_2049_ = v___y_2098_;
v___y_2050_ = v___y_2095_;
v___y_2051_ = v_a_2106_;
v___y_2052_ = v___y_2096_;
v___y_2053_ = v_isHEq_2094_;
v___y_2054_ = v___y_2093_;
v___y_2055_ = v___y_2097_;
v___y_2056_ = v___x_2125_;
goto v___jp_2048_;
}
}
else
{
lean_object* v_a_2126_; 
v_a_2126_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2105_, 1);
v___y_2037_ = v___y_2098_;
v___y_2038_ = v___y_2095_;
v___y_2039_ = v___y_2096_;
v___y_2040_ = v_isHEq_2094_;
v___y_2041_ = v___y_2093_;
v___y_2042_ = v___y_2097_;
v_a_2043_ = v_a_2126_;
goto v___jp_2036_;
}
}
else
{
v___y_2014_ = v_isHEq_2094_;
v___y_2015_ = v___y_2093_;
v___y_2016_ = v___y_2095_;
v___y_2017_ = v___y_2096_;
v___y_2018_ = v___y_2097_;
v___y_2019_ = v___y_2098_;
goto v___jp_2013_;
}
}
else
{
lean_dec(v_a_2102_);
v___y_2014_ = v_isHEq_2094_;
v___y_2015_ = v___y_2093_;
v___y_2016_ = v___y_2095_;
v___y_2017_ = v___y_2096_;
v___y_2018_ = v___y_2097_;
v___y_2019_ = v___y_2098_;
goto v___jp_2013_;
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2127_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2101_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2101_);
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
v___y_2014_ = v_isHEq_2094_;
v___y_2015_ = v___y_2093_;
v___y_2016_ = v___y_2095_;
v___y_2017_ = v___y_2096_;
v___y_2018_ = v___y_2097_;
v___y_2019_ = v___y_2098_;
goto v___jp_2013_;
}
}
}
v___jp_2135_:
{
lean_object* v___x_2141_; 
lean_inc_ref(v___x_2012_);
v___x_2141_ = l_Lean_Meta_matchHEq_x3f(v___x_2012_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
if (lean_obj_tag(v_a_2142_) == 1)
{
lean_object* v_val_2143_; lean_object* v_snd_2144_; lean_object* v_snd_2145_; lean_object* v_fst_2146_; lean_object* v_fst_2147_; lean_object* v_fst_2148_; lean_object* v_snd_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2242_; 
v_val_2143_ = lean_ctor_get(v_a_2142_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v_a_2142_, 1);
v_snd_2144_ = lean_ctor_get(v_val_2143_, 1);
lean_inc(v_snd_2144_);
v_snd_2145_ = lean_ctor_get(v_snd_2144_, 1);
lean_inc(v_snd_2145_);
v_fst_2146_ = lean_ctor_get(v_val_2143_, 0);
lean_inc(v_fst_2146_);
lean_dec(v_val_2143_);
v_fst_2147_ = lean_ctor_get(v_snd_2144_, 0);
lean_inc(v_fst_2147_);
lean_dec(v_snd_2144_);
v_fst_2148_ = lean_ctor_get(v_snd_2145_, 0);
v_snd_2149_ = lean_ctor_get(v_snd_2145_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_snd_2145_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2151_ = v_snd_2145_;
v_isShared_2152_ = v_isSharedCheck_2242_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_snd_2149_);
lean_inc(v_fst_2148_);
lean_dec(v_snd_2145_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2242_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2147_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
if (lean_obj_tag(v_a_2154_) == 1)
{
lean_object* v_val_2155_; lean_object* v___x_2156_; 
v_val_2155_ = lean_ctor_get(v_a_2154_, 0);
lean_inc(v_val_2155_);
lean_dec_ref_known(v_a_2154_, 1);
v___x_2156_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2149_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
if (lean_obj_tag(v_a_2157_) == 1)
{
lean_object* v_toConstantVal_2158_; lean_object* v_val_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2225_; 
v_toConstantVal_2158_ = lean_ctor_get(v_val_2155_, 0);
lean_inc_ref(v_toConstantVal_2158_);
lean_dec(v_val_2155_);
v_val_2159_ = lean_ctor_get(v_a_2157_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_a_2157_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2161_ = v_a_2157_;
v_isShared_2162_ = v_isSharedCheck_2225_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_val_2159_);
lean_dec(v_a_2157_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2225_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_toConstantVal_2163_; lean_object* v_name_2164_; lean_object* v_name_2165_; uint8_t v___x_2166_; 
v_toConstantVal_2163_ = lean_ctor_get(v_val_2159_, 0);
lean_inc_ref(v_toConstantVal_2163_);
lean_dec(v_val_2159_);
v_name_2164_ = lean_ctor_get(v_toConstantVal_2158_, 0);
lean_inc(v_name_2164_);
lean_dec_ref(v_toConstantVal_2158_);
v_name_2165_ = lean_ctor_get(v_toConstantVal_2163_, 0);
lean_inc(v_name_2165_);
lean_dec_ref(v_toConstantVal_2163_);
v___x_2166_ = lean_name_eq(v_name_2164_, v_name_2165_);
lean_dec(v_name_2165_);
lean_dec(v_name_2164_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_Meta_isExprDefEq(v_fst_2146_, v_fst_2148_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; uint8_t v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = lean_unbox(v_a_2168_);
lean_dec(v_a_2168_);
if (v___x_2169_ == 0)
{
lean_del_object(v___x_2161_);
lean_del_object(v___x_2151_);
v___y_2093_ = v_isEq_2136_;
v_isHEq_2094_ = v___x_1958_;
v___y_2095_ = v___y_2137_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2170_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec_ref(v_config_1947_);
lean_inc(v_mvarId_1948_);
v___x_2170_ = l_Lean_MVarId_getType(v_mvarId_1948_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = l_Lean_LocalDecl_toExpr(v_val_1979_);
v___x_2173_ = l_Lean_Meta_mkEqOfHEq(v___x_2172_, v___x_1958_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v___x_2175_ = l_Lean_Meta_mkNoConfusion(v_a_2171_, v_a_2174_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1948_, v_a_2176_, v___y_2138_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_dec_ref_known(v___x_2177_, 1);
v___x_2178_ = lean_box(v___x_1958_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2178_);
v___x_2180_ = v___x_2161_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2182_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v___x_1983_);
lean_ctor_set(v___x_2151_, 0, v___x_2180_);
v___x_2182_ = v___x_2151_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v___x_1983_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
v_a_1965_ = v___x_2182_;
goto v___jp_1964_;
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_del_object(v___x_2161_);
lean_del_object(v___x_2151_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
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
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_del_object(v___x_2161_);
lean_del_object(v___x_2151_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2193_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2175_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2175_);
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
lean_dec(v_a_2171_);
lean_del_object(v___x_2161_);
lean_del_object(v___x_2151_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2201_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2173_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2173_);
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
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_del_object(v___x_2161_);
lean_del_object(v___x_2151_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2209_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2170_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2170_);
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
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_del_object(v___x_2161_);
lean_del_object(v___x_2151_);
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2217_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2167_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2167_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_del_object(v___x_2161_);
lean_del_object(v___x_2151_);
lean_dec(v_fst_2148_);
lean_dec(v_fst_2146_);
v___y_2093_ = v_isEq_2136_;
v_isHEq_2094_ = v___x_1958_;
v___y_2095_ = v___y_2137_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
goto v___jp_2092_;
}
}
}
else
{
lean_dec(v_a_2157_);
lean_dec(v_val_2155_);
lean_del_object(v___x_2151_);
lean_dec(v_fst_2148_);
lean_dec(v_fst_2146_);
v___y_2093_ = v_isEq_2136_;
v_isHEq_2094_ = v___x_1958_;
v___y_2095_ = v___y_2137_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
goto v___jp_2092_;
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_val_2155_);
lean_del_object(v___x_2151_);
lean_dec(v_fst_2148_);
lean_dec(v_fst_2146_);
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2226_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2156_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2156_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_dec(v_a_2154_);
lean_del_object(v___x_2151_);
lean_dec(v_snd_2149_);
lean_dec(v_fst_2148_);
lean_dec(v_fst_2146_);
v___y_2093_ = v_isEq_2136_;
v_isHEq_2094_ = v___x_1958_;
v___y_2095_ = v___y_2137_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
goto v___jp_2092_;
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_del_object(v___x_2151_);
lean_dec(v_snd_2149_);
lean_dec(v_fst_2148_);
lean_dec(v_fst_2146_);
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2234_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2153_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2153_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
else
{
lean_dec(v_a_2142_);
v___y_2093_ = v_isEq_2136_;
v_isHEq_2094_ = v___x_2011_;
v___y_2095_ = v___y_2137_;
v___y_2096_ = v___y_2138_;
v___y_2097_ = v___y_2139_;
v___y_2098_ = v___y_2140_;
goto v___jp_2092_;
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2243_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2141_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2141_);
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
v___jp_2251_:
{
lean_object* v___x_2256_; 
lean_inc_ref(v___x_2012_);
v___x_2256_ = l_Lean_Meta_matchEq_x3f(v___x_2012_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
if (lean_obj_tag(v_a_2257_) == 1)
{
lean_object* v_val_2258_; lean_object* v_snd_2259_; lean_object* v_fst_2260_; lean_object* v_snd_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2333_; 
v_val_2258_ = lean_ctor_get(v_a_2257_, 0);
lean_inc(v_val_2258_);
lean_dec_ref_known(v_a_2257_, 1);
v_snd_2259_ = lean_ctor_get(v_val_2258_, 1);
lean_inc(v_snd_2259_);
lean_dec(v_val_2258_);
v_fst_2260_ = lean_ctor_get(v_snd_2259_, 0);
v_snd_2261_ = lean_ctor_get(v_snd_2259_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_snd_2259_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2263_ = v_snd_2259_;
v_isShared_2264_ = v_isSharedCheck_2333_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_snd_2261_);
lean_inc(v_fst_2260_);
lean_dec(v_snd_2259_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2333_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2260_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
if (lean_obj_tag(v_a_2266_) == 1)
{
lean_object* v_val_2267_; lean_object* v___x_2268_; 
v_val_2267_ = lean_ctor_get(v_a_2266_, 0);
lean_inc(v_val_2267_);
lean_dec_ref_known(v_a_2266_, 1);
v___x_2268_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2261_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
if (lean_obj_tag(v_a_2269_) == 1)
{
lean_object* v_toConstantVal_2270_; lean_object* v_val_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2316_; 
v_toConstantVal_2270_ = lean_ctor_get(v_val_2267_, 0);
lean_inc_ref(v_toConstantVal_2270_);
lean_dec(v_val_2267_);
v_val_2271_ = lean_ctor_get(v_a_2269_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_a_2269_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2273_ = v_a_2269_;
v_isShared_2274_ = v_isSharedCheck_2316_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_val_2271_);
lean_dec(v_a_2269_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2316_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v_toConstantVal_2275_; lean_object* v_name_2276_; lean_object* v_name_2277_; uint8_t v___x_2278_; 
v_toConstantVal_2275_ = lean_ctor_get(v_val_2271_, 0);
lean_inc_ref(v_toConstantVal_2275_);
lean_dec(v_val_2271_);
v_name_2276_ = lean_ctor_get(v_toConstantVal_2270_, 0);
lean_inc(v_name_2276_);
lean_dec_ref(v_toConstantVal_2270_);
v_name_2277_ = lean_ctor_get(v_toConstantVal_2275_, 0);
lean_inc(v_name_2277_);
lean_dec_ref(v_toConstantVal_2275_);
v___x_2278_ = lean_name_eq(v_name_2276_, v_name_2277_);
lean_dec(v_name_2277_);
lean_dec(v_name_2276_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec_ref(v_config_1947_);
lean_inc(v_mvarId_1948_);
v___x_2279_ = l_Lean_MVarId_getType(v_mvarId_1948_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = l_Lean_LocalDecl_toExpr(v_val_1979_);
v___x_2282_ = l_Lean_Meta_mkNoConfusion(v_a_2280_, v___x_2281_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1948_, v_a_2283_, v___y_2253_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
lean_dec_ref_known(v___x_2284_, 1);
v___x_2285_ = lean_box(v___x_1958_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2285_);
v___x_2287_ = v___x_2273_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2289_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 1, v___x_1983_);
lean_ctor_set(v___x_2263_, 0, v___x_2287_);
v___x_2289_ = v___x_2263_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_1983_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
v_a_1965_ = v___x_2289_;
goto v___jp_1964_;
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_del_object(v___x_2273_);
lean_del_object(v___x_2263_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_2292_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2284_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2284_);
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
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_del_object(v___x_2273_);
lean_del_object(v___x_2263_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2300_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2282_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2282_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_del_object(v___x_2273_);
lean_del_object(v___x_2263_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2308_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2279_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2279_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_del_object(v___x_2273_);
lean_del_object(v___x_2263_);
v_isEq_2136_ = v___x_1958_;
v___y_2137_ = v___y_2252_;
v___y_2138_ = v___y_2253_;
v___y_2139_ = v___y_2254_;
v___y_2140_ = v___y_2255_;
goto v___jp_2135_;
}
}
}
else
{
lean_dec(v_a_2269_);
lean_dec(v_val_2267_);
lean_del_object(v___x_2263_);
v_isEq_2136_ = v___x_1958_;
v___y_2137_ = v___y_2252_;
v___y_2138_ = v___y_2253_;
v___y_2139_ = v___y_2254_;
v___y_2140_ = v___y_2255_;
goto v___jp_2135_;
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_val_2267_);
lean_del_object(v___x_2263_);
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2317_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2268_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2268_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
else
{
lean_dec(v_a_2266_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v_isEq_2136_ = v___x_1958_;
v___y_2137_ = v___y_2252_;
v___y_2138_ = v___y_2253_;
v___y_2139_ = v___y_2254_;
v___y_2140_ = v___y_2255_;
goto v___jp_2135_;
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2325_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2265_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2265_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
else
{
lean_dec(v_a_2257_);
v_isEq_2136_ = v___x_2011_;
v___y_2137_ = v___y_2252_;
v___y_2138_ = v___y_2253_;
v___y_2139_ = v___y_2254_;
v___y_2140_ = v___y_2255_;
goto v___jp_2135_;
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2334_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2256_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2256_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
v___jp_2342_:
{
lean_object* v___x_2347_; 
lean_inc_ref(v___x_2012_);
v___x_2347_ = l_Lean_refutableHasNotBit_x3f(v___x_2012_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
if (lean_obj_tag(v_a_2348_) == 1)
{
lean_object* v_val_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec_ref(v_config_1947_);
v_val_2349_ = lean_ctor_get(v_a_2348_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_a_2348_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2351_ = v_a_2348_;
v_isShared_2352_ = v_isSharedCheck_2388_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_val_2349_);
lean_dec(v_a_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2388_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; 
lean_inc(v_mvarId_1948_);
v___x_2353_ = l_Lean_MVarId_getType(v_mvarId_1948_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = l_Lean_LocalDecl_toExpr(v_val_1979_);
v___x_2356_ = l_Lean_Meta_mkAbsurd(v_a_2354_, v_val_2349_, v___x_2355_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2358_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v___x_2358_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1948_, v_a_2357_, v___y_2344_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2361_; 
lean_dec_ref_known(v___x_2358_, 1);
v___x_2359_ = lean_box(v___x_1958_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2359_);
v___x_2361_ = v___x_2351_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set(v___x_2362_, 1, v___x_1983_);
v_a_1965_ = v___x_2362_;
goto v___jp_1964_;
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_del_object(v___x_2351_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_2364_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2358_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2358_);
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
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_del_object(v___x_2351_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2372_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2356_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2356_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_del_object(v___x_2351_);
lean_dec(v_val_2349_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2380_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2353_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2353_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
else
{
lean_object* v___x_2389_; 
lean_dec(v_a_2348_);
lean_inc_ref(v___x_2012_);
v___x_2389_ = l_Lean_Meta_matchNe_x3f(v___x_2012_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
if (lean_obj_tag(v_a_2390_) == 1)
{
lean_object* v_val_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2460_; 
v_val_2391_ = lean_ctor_get(v_a_2390_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_a_2390_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2393_ = v_a_2390_;
v_isShared_2394_ = v_isSharedCheck_2460_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_val_2391_);
lean_dec(v_a_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2460_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_snd_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2459_; 
v_snd_2395_ = lean_ctor_get(v_val_2391_, 1);
lean_inc(v_snd_2395_);
lean_dec(v_val_2391_);
v_fst_2396_ = lean_ctor_get(v_snd_2395_, 0);
v_snd_2397_ = lean_ctor_get(v_snd_2395_, 1);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_snd_2395_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2399_ = v_snd_2395_;
v_isShared_2400_ = v_isSharedCheck_2459_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_snd_2397_);
lean_inc(v_fst_2396_);
lean_dec(v_snd_2395_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2459_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; 
lean_inc(v_fst_2396_);
v___x_2401_ = l_Lean_Meta_isExprDefEq(v_fst_2396_, v_snd_2397_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; uint8_t v___x_2403_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 1);
v___x_2403_ = lean_unbox(v_a_2402_);
lean_dec(v_a_2402_);
if (v___x_2403_ == 0)
{
lean_del_object(v___x_2399_);
lean_dec(v_fst_2396_);
lean_del_object(v___x_2393_);
v___y_2252_ = v___y_2343_;
v___y_2253_ = v___y_2344_;
v___y_2254_ = v___y_2345_;
v___y_2255_ = v___y_2346_;
goto v___jp_2251_;
}
else
{
lean_object* v___x_2404_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec_ref(v_config_1947_);
lean_inc(v_mvarId_1948_);
v___x_2404_ = l_Lean_MVarId_getType(v_mvarId_1948_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = l_Lean_Meta_mkEqRefl(v_fst_2396_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2408_ = l_Lean_LocalDecl_toExpr(v_val_1979_);
v___x_2409_ = l_Lean_Meta_mkAbsurd(v_a_2405_, v_a_2407_, v___x_2408_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2411_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v___x_2411_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1948_, v_a_2410_, v___y_2344_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
lean_dec_ref_known(v___x_2411_, 1);
v___x_2412_ = lean_box(v___x_1958_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2412_);
v___x_2414_ = v___x_2393_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 1, v___x_1983_);
lean_ctor_set(v___x_2399_, 0, v___x_2414_);
v___x_2416_ = v___x_2399_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_1983_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
v_a_1965_ = v___x_2416_;
goto v___jp_1964_;
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_del_object(v___x_2399_);
lean_del_object(v___x_2393_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_2419_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2411_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2411_);
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
lean_del_object(v___x_2399_);
lean_del_object(v___x_2393_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2427_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2409_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2409_);
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
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_a_2405_);
lean_del_object(v___x_2399_);
lean_del_object(v___x_2393_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2435_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2406_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2406_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_del_object(v___x_2399_);
lean_dec(v_fst_2396_);
lean_del_object(v___x_2393_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
v_a_2443_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2404_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2404_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_del_object(v___x_2399_);
lean_dec(v_fst_2396_);
lean_del_object(v___x_2393_);
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2451_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2401_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2401_);
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
}
else
{
lean_dec(v_a_2390_);
v___y_2252_ = v___y_2343_;
v___y_2253_ = v___y_2344_;
v___y_2254_ = v___y_2345_;
v___y_2255_ = v___y_2346_;
goto v___jp_2251_;
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2461_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2389_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2389_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v___x_2012_);
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2469_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2347_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2347_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
else
{
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_1973_ = v___x_1984_;
goto v___jp_1972_;
}
v___jp_1985_:
{
uint8_t v_emptyType_1992_; 
v_emptyType_1992_ = lean_ctor_get_uint8(v_config_1947_, sizeof(void*)*1 + 1);
if (v_emptyType_1992_ == 0)
{
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_1973_ = v___x_1984_;
goto v___jp_1972_;
}
else
{
if (v___y_1987_ == 0)
{
if (v___y_1986_ == 0)
{
lean_object* v_searchFuel_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_searchFuel_1993_ = lean_ctor_get(v_config_1947_, 0);
v___x_1994_ = l_Lean_LocalDecl_fvarId(v_val_1979_);
lean_dec(v_val_1979_);
lean_inc(v_searchFuel_1993_);
lean_inc(v_mvarId_1948_);
v___x_1995_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_1948_, v___x_1994_, v_searchFuel_1993_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; uint8_t v___x_1997_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = lean_unbox(v_a_1996_);
lean_dec(v_a_1996_);
if (v___x_1997_ == 0)
{
lean_del_object(v___x_1981_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_1973_ = v___x_1984_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v___x_1998_ = lean_box(v___x_1958_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1998_);
v___x_2000_ = v___x_1981_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v___x_1983_);
v_a_1965_ = v___x_2001_;
goto v___jp_1964_;
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_del_object(v___x_1981_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
lean_dec(v_mvarId_1948_);
lean_dec_ref(v_config_1947_);
v_a_2003_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1995_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1995_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_1973_ = v___x_1984_;
goto v___jp_1972_;
}
}
else
{
lean_del_object(v___x_1981_);
lean_dec(v_val_1979_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_1973_ = v___x_1984_;
goto v___jp_1972_;
}
}
}
}
}
v___jp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_a_1965_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1966_);
v___x_1968_ = v___x_1962_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_snd_1960_);
v___x_1968_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
}
v___jp_1972_:
{
lean_object* v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; 
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1971_);
lean_ctor_set(v___x_1974_, 1, v_a_1973_);
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_add(v_i_1951_, v___x_1975_);
v_i_1951_ = v___x_1976_;
v_b_1952_ = v___x_1974_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2543_, lean_object* v_mvarId_2544_, lean_object* v_as_2545_, lean_object* v_sz_2546_, lean_object* v_i_2547_, lean_object* v_b_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
size_t v_sz_boxed_2554_; size_t v_i_boxed_2555_; lean_object* v_res_2556_; 
v_sz_boxed_2554_ = lean_unbox_usize(v_sz_2546_);
lean_dec(v_sz_2546_);
v_i_boxed_2555_ = lean_unbox_usize(v_i_2547_);
lean_dec(v_i_2547_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2543_, v_mvarId_2544_, v_as_2545_, v_sz_boxed_2554_, v_i_boxed_2555_, v_b_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec_ref(v_as_2545_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2557_, lean_object* v_mvarId_2558_, lean_object* v_as_2559_, size_t v_sz_2560_, size_t v_i_2561_, lean_object* v_b_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
uint8_t v___x_2568_; 
v___x_2568_ = lean_usize_dec_lt(v_i_2561_, v_sz_2560_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_b_2562_);
return v___x_2569_;
}
else
{
lean_object* v_snd_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_3151_; 
v_snd_2570_ = lean_ctor_get(v_b_2562_, 1);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_b_2562_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_b_2562_, 0);
lean_dec(v_unused_3152_);
v___x_2572_ = v_b_2562_;
v_isShared_2573_ = v_isSharedCheck_3151_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_snd_2570_);
lean_dec(v_b_2562_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_3151_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_a_2575_; lean_object* v___x_2581_; lean_object* v_a_2583_; lean_object* v_a_2588_; 
v___x_2581_ = lean_box(0);
v_a_2588_ = lean_array_uget(v_as_2559_, v_i_2561_);
if (lean_obj_tag(v_a_2588_) == 0)
{
lean_del_object(v___x_2572_);
v_a_2583_ = v_snd_2570_;
goto v___jp_2582_;
}
else
{
lean_object* v_val_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_3150_; 
v_val_2589_ = lean_ctor_get(v_a_2588_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_a_2588_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_2591_ = v_a_2588_;
v_isShared_2592_ = v_isSharedCheck_3150_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_val_2589_);
lean_dec(v_a_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_3150_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___y_2596_; uint8_t v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; uint8_t v___x_2621_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2621_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2589_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; uint8_t v___y_2624_; uint8_t v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; uint8_t v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v_a_2653_; lean_object* v___y_2659_; uint8_t v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; uint8_t v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; uint8_t v___y_2703_; uint8_t v_isHEq_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; uint8_t v_isEq_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___x_3087_; 
v___x_2622_ = l_Lean_LocalDecl_type(v_val_2589_);
lean_inc_ref(v___x_2622_);
v___x_3087_ = l_Lean_Meta_matchNot_x3f(v___x_2622_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3087_, 1);
if (lean_obj_tag(v_a_3088_) == 1)
{
lean_object* v_val_3089_; lean_object* v___x_3090_; 
v_val_3089_ = lean_ctor_get(v_a_3088_, 0);
lean_inc(v_val_3089_);
lean_dec_ref_known(v_a_3088_, 1);
v___x_3090_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3089_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3090_, 1);
if (lean_obj_tag(v_a_3091_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec_ref(v_config_2557_);
v_val_3092_ = lean_ctor_get(v_a_3091_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_a_3091_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3094_ = v_a_3091_;
v_isShared_3095_ = v_isSharedCheck_3133_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_val_3092_);
lean_dec(v_a_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3133_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; 
lean_inc(v_mvarId_2558_);
v___x_3096_ = l_Lean_MVarId_getType(v_mvarId_2558_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3098_ = l_Lean_LocalDecl_toExpr(v_val_2589_);
v___x_3099_ = l_Lean_mkFVar(v_val_3092_);
v___x_3100_ = l_Lean_Expr_app___override(v___x_3098_, v___x_3099_);
v___x_3101_ = l_Lean_Meta_mkFalseElim(v_a_3097_, v___x_3100_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v___x_3103_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2558_, v_a_3102_, v___y_2564_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_dec_ref_known(v___x_3103_, 1);
v___x_3104_ = lean_box(v___x_2568_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3104_);
v___x_3106_ = v___x_3094_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; 
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v___x_2593_);
v_a_2575_ = v___x_3107_;
goto v___jp_2574_;
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_del_object(v___x_3094_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_3109_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3103_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3103_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_del_object(v___x_3094_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_3117_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3101_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3101_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_del_object(v___x_3094_);
lean_dec(v_val_3092_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_3125_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3096_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3096_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
else
{
lean_dec(v_a_3091_);
v___y_2953_ = v___y_2563_;
v___y_2954_ = v___y_2564_;
v___y_2955_ = v___y_2565_;
v___y_2956_ = v___y_2566_;
goto v___jp_2952_;
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_3134_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3090_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3090_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_dec(v_a_3088_);
v___y_2953_ = v___y_2563_;
v___y_2954_ = v___y_2564_;
v___y_2955_ = v___y_2565_;
v___y_2956_ = v___y_2566_;
goto v___jp_2952_;
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_3142_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3087_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3087_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
v___jp_2623_:
{
uint8_t v_genDiseq_2630_; 
v_genDiseq_2630_ = lean_ctor_get_uint8(v_config_2557_, sizeof(void*)*1 + 2);
if (v_genDiseq_2630_ == 0)
{
lean_dec_ref(v___x_2622_);
v___y_2596_ = v___y_2624_;
v___y_2597_ = v___y_2625_;
v___y_2598_ = v___y_2626_;
v___y_2599_ = v___y_2627_;
v___y_2600_ = v___y_2628_;
v___y_2601_ = v___y_2629_;
goto v___jp_2595_;
}
else
{
uint8_t v___x_2631_; 
v___x_2631_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2622_);
lean_dec_ref(v___x_2622_);
if (v___x_2631_ == 0)
{
v___y_2596_ = v___y_2624_;
v___y_2597_ = v___y_2625_;
v___y_2598_ = v___y_2626_;
v___y_2599_ = v___y_2627_;
v___y_2600_ = v___y_2628_;
v___y_2601_ = v___y_2629_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2632_; 
lean_inc(v_val_2589_);
lean_inc(v_mvarId_2558_);
v___x_2632_ = l_Lean_Meta_processGenDiseq(v_mvarId_2558_, v_val_2589_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; uint8_t v___x_2634_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = lean_unbox(v_a_2633_);
lean_dec(v_a_2633_);
if (v___x_2634_ == 0)
{
v___y_2596_ = v___y_2624_;
v___y_2597_ = v___y_2625_;
v___y_2598_ = v___y_2626_;
v___y_2599_ = v___y_2627_;
v___y_2600_ = v___y_2628_;
v___y_2601_ = v___y_2629_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v___x_2635_ = lean_box(v___x_2568_);
v___x_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
lean_ctor_set(v___x_2637_, 1, v___x_2593_);
v_a_2575_ = v___x_2637_;
goto v___jp_2574_;
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2638_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2632_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2632_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
}
v___jp_2646_:
{
uint8_t v___x_2654_; 
v___x_2654_ = l_Lean_Exception_isInterrupt(v_a_2653_);
if (v___x_2654_ == 0)
{
uint8_t v___x_2655_; 
lean_inc_ref(v_a_2653_);
v___x_2655_ = l_Lean_Exception_isRuntime(v_a_2653_);
if (v___x_2655_ == 0)
{
lean_dec_ref(v_a_2653_);
v___y_2624_ = v___y_2647_;
v___y_2625_ = v___y_2650_;
v___y_2626_ = v___y_2652_;
v___y_2627_ = v___y_2649_;
v___y_2628_ = v___y_2648_;
v___y_2629_ = v___y_2651_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2656_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_a_2653_);
return v___x_2656_;
}
}
else
{
lean_object* v___x_2657_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_a_2653_);
return v___x_2657_;
}
}
v___jp_2658_:
{
if (lean_obj_tag(v___y_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v_a_2667_ = lean_ctor_get(v___y_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___y_2666_, 1);
v___x_2668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2669_ = l_Lean_Expr_isConstOf(v_a_2667_, v___x_2668_);
lean_dec(v_a_2667_);
if (v___x_2669_ == 0)
{
lean_dec_ref(v___y_2659_);
v___y_2624_ = v___y_2660_;
v___y_2625_ = v___y_2663_;
v___y_2626_ = v___y_2665_;
v___y_2627_ = v___y_2662_;
v___y_2628_ = v___y_2661_;
v___y_2629_ = v___y_2664_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2670_; 
lean_inc_ref(v___y_2659_);
v___x_2670_ = l_Lean_Meta_mkEqRefl(v___y_2659_, v___y_2665_, v___y_2662_, v___y_2661_, v___y_2664_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v_dummy_2673_; lean_object* v_nargs_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2673_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2674_ = l_Lean_Expr_getAppNumArgs(v___y_2659_);
lean_inc(v_nargs_2674_);
v___x_2675_ = lean_mk_array(v_nargs_2674_, v_dummy_2673_);
v___x_2676_ = lean_unsigned_to_nat(1u);
v___x_2677_ = lean_nat_sub(v_nargs_2674_, v___x_2676_);
lean_dec(v_nargs_2674_);
v___x_2678_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2659_, v___x_2675_, v___x_2677_);
v___x_2679_ = lean_array_push(v___x_2678_, v_a_2671_);
v___x_2680_ = l_Lean_mkAppN(v___x_2672_, v___x_2679_);
lean_dec_ref(v___x_2679_);
lean_inc(v_mvarId_2558_);
v___x_2681_ = l_Lean_MVarId_getType(v_mvarId_2558_, v___y_2665_, v___y_2662_, v___y_2661_, v___y_2664_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
lean_inc(v_val_2589_);
v___x_2683_ = l_Lean_LocalDecl_toExpr(v_val_2589_);
v___x_2684_ = l_Lean_Meta_mkAbsurd(v_a_2682_, v___x_2683_, v___x_2680_, v___y_2665_, v___y_2662_, v___y_2661_, v___y_2664_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2686_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
lean_inc(v_mvarId_2558_);
v___x_2686_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2558_, v_a_2685_, v___y_2662_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v___x_2686_, 0);
lean_dec(v_unused_2696_);
v___x_2688_ = v___x_2686_;
v_isShared_2689_ = v_isSharedCheck_2695_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v___x_2686_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2695_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = lean_box(v___x_2568_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 1);
lean_ctor_set(v___x_2688_, 0, v___x_2690_);
v___x_2692_ = v___x_2688_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
lean_ctor_set(v___x_2693_, 1, v___x_2593_);
v_a_2575_ = v___x_2693_;
goto v___jp_2574_;
}
}
}
else
{
lean_object* v_a_2697_; 
v_a_2697_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2686_, 1);
v___y_2647_ = v___y_2660_;
v___y_2648_ = v___y_2661_;
v___y_2649_ = v___y_2662_;
v___y_2650_ = v___y_2663_;
v___y_2651_ = v___y_2664_;
v___y_2652_ = v___y_2665_;
v_a_2653_ = v_a_2697_;
goto v___jp_2646_;
}
}
else
{
lean_object* v_a_2698_; 
v_a_2698_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2684_, 1);
v___y_2647_ = v___y_2660_;
v___y_2648_ = v___y_2661_;
v___y_2649_ = v___y_2662_;
v___y_2650_ = v___y_2663_;
v___y_2651_ = v___y_2664_;
v___y_2652_ = v___y_2665_;
v_a_2653_ = v_a_2698_;
goto v___jp_2646_;
}
}
else
{
lean_object* v_a_2699_; 
lean_dec_ref(v___x_2680_);
v_a_2699_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2681_, 1);
v___y_2647_ = v___y_2660_;
v___y_2648_ = v___y_2661_;
v___y_2649_ = v___y_2662_;
v___y_2650_ = v___y_2663_;
v___y_2651_ = v___y_2664_;
v___y_2652_ = v___y_2665_;
v_a_2653_ = v_a_2699_;
goto v___jp_2646_;
}
}
else
{
lean_object* v_a_2700_; 
lean_dec_ref(v___y_2659_);
v_a_2700_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2670_, 1);
v___y_2647_ = v___y_2660_;
v___y_2648_ = v___y_2661_;
v___y_2649_ = v___y_2662_;
v___y_2650_ = v___y_2663_;
v___y_2651_ = v___y_2664_;
v___y_2652_ = v___y_2665_;
v_a_2653_ = v_a_2700_;
goto v___jp_2646_;
}
}
}
else
{
lean_object* v_a_2701_; 
lean_dec_ref(v___y_2659_);
v_a_2701_ = lean_ctor_get(v___y_2666_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___y_2666_, 1);
v___y_2647_ = v___y_2660_;
v___y_2648_ = v___y_2661_;
v___y_2649_ = v___y_2662_;
v___y_2650_ = v___y_2663_;
v___y_2651_ = v___y_2664_;
v___y_2652_ = v___y_2665_;
v_a_2653_ = v_a_2701_;
goto v___jp_2646_;
}
}
v___jp_2702_:
{
uint8_t v_useDecide_2709_; 
v_useDecide_2709_ = lean_ctor_get_uint8(v_config_2557_, sizeof(void*)*1);
if (v_useDecide_2709_ == 0)
{
v___y_2624_ = v_isHEq_2704_;
v___y_2625_ = v___y_2703_;
v___y_2626_ = v___y_2705_;
v___y_2627_ = v___y_2706_;
v___y_2628_ = v___y_2707_;
v___y_2629_ = v___y_2708_;
goto v___jp_2623_;
}
else
{
uint8_t v___x_2710_; 
v___x_2710_ = l_Lean_Expr_hasFVar(v___x_2622_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; 
lean_inc_ref(v___x_2622_);
v___x_2711_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_2622_, v___y_2706_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; uint8_t v___x_2713_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = l_Lean_Expr_hasMVar(v_a_2712_);
if (v___x_2713_ == 0)
{
uint8_t v___x_2714_; 
v___x_2714_ = l_Lean_Expr_hasFVar(v_a_2712_);
lean_dec(v_a_2712_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; 
lean_inc_ref(v___x_2622_);
v___x_2715_ = l_Lean_Meta_mkDecide(v___x_2622_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; uint8_t v_transparency_2718_; uint8_t v___x_2719_; uint8_t v___x_2720_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2717_ = l_Lean_Meta_Context_config(v___y_2705_);
v_transparency_2718_ = lean_ctor_get_uint8(v___x_2717_, 9);
lean_dec_ref(v___x_2717_);
v___x_2719_ = 1;
v___x_2720_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2718_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_object* v_keyedConfig_2721_; uint8_t v_trackZetaDelta_2722_; lean_object* v_zetaDeltaSet_2723_; lean_object* v_lctx_2724_; lean_object* v_localInstances_2725_; lean_object* v_defEqCtx_x3f_2726_; lean_object* v_synthPendingDepth_2727_; lean_object* v_customCanUnfoldPredicate_x3f_2728_; uint8_t v_univApprox_2729_; uint8_t v_inTypeClassResolution_2730_; uint8_t v_cacheInferType_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_keyedConfig_2721_ = lean_ctor_get(v___y_2705_, 0);
v_trackZetaDelta_2722_ = lean_ctor_get_uint8(v___y_2705_, sizeof(void*)*7);
v_zetaDeltaSet_2723_ = lean_ctor_get(v___y_2705_, 1);
v_lctx_2724_ = lean_ctor_get(v___y_2705_, 2);
v_localInstances_2725_ = lean_ctor_get(v___y_2705_, 3);
v_defEqCtx_x3f_2726_ = lean_ctor_get(v___y_2705_, 4);
v_synthPendingDepth_2727_ = lean_ctor_get(v___y_2705_, 5);
v_customCanUnfoldPredicate_x3f_2728_ = lean_ctor_get(v___y_2705_, 6);
v_univApprox_2729_ = lean_ctor_get_uint8(v___y_2705_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2730_ = lean_ctor_get_uint8(v___y_2705_, sizeof(void*)*7 + 2);
v_cacheInferType_2731_ = lean_ctor_get_uint8(v___y_2705_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2721_);
v___x_2732_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2719_, v_keyedConfig_2721_);
lean_inc(v_customCanUnfoldPredicate_x3f_2728_);
lean_inc(v_synthPendingDepth_2727_);
lean_inc(v_defEqCtx_x3f_2726_);
lean_inc_ref(v_localInstances_2725_);
lean_inc_ref(v_lctx_2724_);
lean_inc(v_zetaDeltaSet_2723_);
v___x_2733_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v_zetaDeltaSet_2723_);
lean_ctor_set(v___x_2733_, 2, v_lctx_2724_);
lean_ctor_set(v___x_2733_, 3, v_localInstances_2725_);
lean_ctor_set(v___x_2733_, 4, v_defEqCtx_x3f_2726_);
lean_ctor_set(v___x_2733_, 5, v_synthPendingDepth_2727_);
lean_ctor_set(v___x_2733_, 6, v_customCanUnfoldPredicate_x3f_2728_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*7, v_trackZetaDelta_2722_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*7 + 1, v_univApprox_2729_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2730_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*7 + 3, v_cacheInferType_2731_);
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc(v_a_2716_);
v___x_2734_ = lean_whnf(v_a_2716_, v___x_2733_, v___y_2706_, v___y_2707_, v___y_2708_);
v___y_2659_ = v_a_2716_;
v___y_2660_ = v_isHEq_2704_;
v___y_2661_ = v___y_2707_;
v___y_2662_ = v___y_2706_;
v___y_2663_ = v___y_2703_;
v___y_2664_ = v___y_2708_;
v___y_2665_ = v___y_2705_;
v___y_2666_ = v___x_2734_;
goto v___jp_2658_;
}
else
{
lean_object* v___x_2735_; 
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v_a_2716_);
v___x_2735_ = lean_whnf(v_a_2716_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
v___y_2659_ = v_a_2716_;
v___y_2660_ = v_isHEq_2704_;
v___y_2661_ = v___y_2707_;
v___y_2662_ = v___y_2706_;
v___y_2663_ = v___y_2703_;
v___y_2664_ = v___y_2708_;
v___y_2665_ = v___y_2705_;
v___y_2666_ = v___x_2735_;
goto v___jp_2658_;
}
}
else
{
lean_object* v_a_2736_; 
v_a_2736_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2715_, 1);
v___y_2647_ = v_isHEq_2704_;
v___y_2648_ = v___y_2707_;
v___y_2649_ = v___y_2706_;
v___y_2650_ = v___y_2703_;
v___y_2651_ = v___y_2708_;
v___y_2652_ = v___y_2705_;
v_a_2653_ = v_a_2736_;
goto v___jp_2646_;
}
}
else
{
v___y_2624_ = v_isHEq_2704_;
v___y_2625_ = v___y_2703_;
v___y_2626_ = v___y_2705_;
v___y_2627_ = v___y_2706_;
v___y_2628_ = v___y_2707_;
v___y_2629_ = v___y_2708_;
goto v___jp_2623_;
}
}
else
{
lean_dec(v_a_2712_);
v___y_2624_ = v_isHEq_2704_;
v___y_2625_ = v___y_2703_;
v___y_2626_ = v___y_2705_;
v___y_2627_ = v___y_2706_;
v___y_2628_ = v___y_2707_;
v___y_2629_ = v___y_2708_;
goto v___jp_2623_;
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2737_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2711_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2711_);
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
else
{
v___y_2624_ = v_isHEq_2704_;
v___y_2625_ = v___y_2703_;
v___y_2626_ = v___y_2705_;
v___y_2627_ = v___y_2706_;
v___y_2628_ = v___y_2707_;
v___y_2629_ = v___y_2708_;
goto v___jp_2623_;
}
}
}
v___jp_2745_:
{
lean_object* v___x_2751_; 
lean_inc_ref(v___x_2622_);
v___x_2751_ = l_Lean_Meta_matchHEq_x3f(v___x_2622_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v___x_2751_, 1);
if (lean_obj_tag(v_a_2752_) == 1)
{
lean_object* v_val_2753_; lean_object* v_snd_2754_; lean_object* v_snd_2755_; lean_object* v_fst_2756_; lean_object* v_fst_2757_; lean_object* v_fst_2758_; lean_object* v_snd_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2852_; 
v_val_2753_ = lean_ctor_get(v_a_2752_, 0);
lean_inc(v_val_2753_);
lean_dec_ref_known(v_a_2752_, 1);
v_snd_2754_ = lean_ctor_get(v_val_2753_, 1);
lean_inc(v_snd_2754_);
v_snd_2755_ = lean_ctor_get(v_snd_2754_, 1);
lean_inc(v_snd_2755_);
v_fst_2756_ = lean_ctor_get(v_val_2753_, 0);
lean_inc(v_fst_2756_);
lean_dec(v_val_2753_);
v_fst_2757_ = lean_ctor_get(v_snd_2754_, 0);
lean_inc(v_fst_2757_);
lean_dec(v_snd_2754_);
v_fst_2758_ = lean_ctor_get(v_snd_2755_, 0);
v_snd_2759_ = lean_ctor_get(v_snd_2755_, 1);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_snd_2755_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2761_ = v_snd_2755_;
v_isShared_2762_ = v_isSharedCheck_2852_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_snd_2759_);
lean_inc(v_fst_2758_);
lean_dec(v_snd_2755_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2852_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2757_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
if (lean_obj_tag(v_a_2764_) == 1)
{
lean_object* v_val_2765_; lean_object* v___x_2766_; 
v_val_2765_ = lean_ctor_get(v_a_2764_, 0);
lean_inc(v_val_2765_);
lean_dec_ref_known(v_a_2764_, 1);
v___x_2766_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2759_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
if (lean_obj_tag(v_a_2767_) == 1)
{
lean_object* v_toConstantVal_2768_; lean_object* v_val_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2835_; 
v_toConstantVal_2768_ = lean_ctor_get(v_val_2765_, 0);
lean_inc_ref(v_toConstantVal_2768_);
lean_dec(v_val_2765_);
v_val_2769_ = lean_ctor_get(v_a_2767_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_a_2767_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2771_ = v_a_2767_;
v_isShared_2772_ = v_isSharedCheck_2835_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_val_2769_);
lean_dec(v_a_2767_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2835_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v_toConstantVal_2773_; lean_object* v_name_2774_; lean_object* v_name_2775_; uint8_t v___x_2776_; 
v_toConstantVal_2773_ = lean_ctor_get(v_val_2769_, 0);
lean_inc_ref(v_toConstantVal_2773_);
lean_dec(v_val_2769_);
v_name_2774_ = lean_ctor_get(v_toConstantVal_2768_, 0);
lean_inc(v_name_2774_);
lean_dec_ref(v_toConstantVal_2768_);
v_name_2775_ = lean_ctor_get(v_toConstantVal_2773_, 0);
lean_inc(v_name_2775_);
lean_dec_ref(v_toConstantVal_2773_);
v___x_2776_ = lean_name_eq(v_name_2774_, v_name_2775_);
lean_dec(v_name_2775_);
lean_dec(v_name_2774_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_Meta_isExprDefEq(v_fst_2756_, v_fst_2758_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; uint8_t v___x_2779_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2779_ = lean_unbox(v_a_2778_);
lean_dec(v_a_2778_);
if (v___x_2779_ == 0)
{
lean_del_object(v___x_2771_);
lean_del_object(v___x_2761_);
v___y_2703_ = v_isEq_2746_;
v_isHEq_2704_ = v___x_2568_;
v___y_2705_ = v___y_2747_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
goto v___jp_2702_;
}
else
{
lean_object* v___x_2780_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec_ref(v_config_2557_);
lean_inc(v_mvarId_2558_);
v___x_2780_ = l_Lean_MVarId_getType(v_mvarId_2558_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = l_Lean_LocalDecl_toExpr(v_val_2589_);
v___x_2783_ = l_Lean_Meta_mkEqOfHEq(v___x_2782_, v___x_2568_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = l_Lean_Meta_mkNoConfusion(v_a_2781_, v_a_2784_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2787_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2787_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2558_, v_a_2786_, v___y_2748_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
lean_dec_ref_known(v___x_2787_, 1);
v___x_2788_ = lean_box(v___x_2568_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2788_);
v___x_2790_ = v___x_2771_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2792_; 
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2593_);
lean_ctor_set(v___x_2761_, 0, v___x_2790_);
v___x_2792_ = v___x_2761_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v___x_2593_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
v_a_2575_ = v___x_2792_;
goto v___jp_2574_;
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_del_object(v___x_2771_);
lean_del_object(v___x_2761_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_2795_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2787_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2787_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_del_object(v___x_2771_);
lean_del_object(v___x_2761_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_2803_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2785_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2785_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_a_2781_);
lean_del_object(v___x_2771_);
lean_del_object(v___x_2761_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_2811_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2783_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2783_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_del_object(v___x_2771_);
lean_del_object(v___x_2761_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_2819_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2780_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2780_);
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
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_del_object(v___x_2771_);
lean_del_object(v___x_2761_);
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2827_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2777_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2777_);
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
lean_del_object(v___x_2771_);
lean_del_object(v___x_2761_);
lean_dec(v_fst_2758_);
lean_dec(v_fst_2756_);
v___y_2703_ = v_isEq_2746_;
v_isHEq_2704_ = v___x_2568_;
v___y_2705_ = v___y_2747_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
goto v___jp_2702_;
}
}
}
else
{
lean_dec(v_a_2767_);
lean_dec(v_val_2765_);
lean_del_object(v___x_2761_);
lean_dec(v_fst_2758_);
lean_dec(v_fst_2756_);
v___y_2703_ = v_isEq_2746_;
v_isHEq_2704_ = v___x_2568_;
v___y_2705_ = v___y_2747_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
goto v___jp_2702_;
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_val_2765_);
lean_del_object(v___x_2761_);
lean_dec(v_fst_2758_);
lean_dec(v_fst_2756_);
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2836_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2766_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2766_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
else
{
lean_dec(v_a_2764_);
lean_del_object(v___x_2761_);
lean_dec(v_snd_2759_);
lean_dec(v_fst_2758_);
lean_dec(v_fst_2756_);
v___y_2703_ = v_isEq_2746_;
v_isHEq_2704_ = v___x_2568_;
v___y_2705_ = v___y_2747_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
goto v___jp_2702_;
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_del_object(v___x_2761_);
lean_dec(v_snd_2759_);
lean_dec(v_fst_2758_);
lean_dec(v_fst_2756_);
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2844_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2763_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2763_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
else
{
lean_dec(v_a_2752_);
v___y_2703_ = v_isEq_2746_;
v_isHEq_2704_ = v___x_2621_;
v___y_2705_ = v___y_2747_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
v___y_2708_ = v___y_2750_;
goto v___jp_2702_;
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2853_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2751_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2751_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
v___jp_2861_:
{
lean_object* v___x_2866_; 
lean_inc_ref(v___x_2622_);
v___x_2866_ = l_Lean_Meta_matchEq_x3f(v___x_2622_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
if (lean_obj_tag(v_a_2867_) == 1)
{
lean_object* v_val_2868_; lean_object* v_snd_2869_; lean_object* v_fst_2870_; lean_object* v_snd_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2943_; 
v_val_2868_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_val_2868_);
lean_dec_ref_known(v_a_2867_, 1);
v_snd_2869_ = lean_ctor_get(v_val_2868_, 1);
lean_inc(v_snd_2869_);
lean_dec(v_val_2868_);
v_fst_2870_ = lean_ctor_get(v_snd_2869_, 0);
v_snd_2871_ = lean_ctor_get(v_snd_2869_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_snd_2869_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2873_ = v_snd_2869_;
v_isShared_2874_ = v_isSharedCheck_2943_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_snd_2871_);
lean_inc(v_fst_2870_);
lean_dec(v_snd_2869_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2943_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2870_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
if (lean_obj_tag(v_a_2876_) == 1)
{
lean_object* v_val_2877_; lean_object* v___x_2878_; 
v_val_2877_ = lean_ctor_get(v_a_2876_, 0);
lean_inc(v_val_2877_);
lean_dec_ref_known(v_a_2876_, 1);
v___x_2878_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2871_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
if (lean_obj_tag(v_a_2879_) == 1)
{
lean_object* v_toConstantVal_2880_; lean_object* v_val_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2926_; 
v_toConstantVal_2880_ = lean_ctor_get(v_val_2877_, 0);
lean_inc_ref(v_toConstantVal_2880_);
lean_dec(v_val_2877_);
v_val_2881_ = lean_ctor_get(v_a_2879_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2879_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2883_ = v_a_2879_;
v_isShared_2884_ = v_isSharedCheck_2926_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_val_2881_);
lean_dec(v_a_2879_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2926_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v_toConstantVal_2885_; lean_object* v_name_2886_; lean_object* v_name_2887_; uint8_t v___x_2888_; 
v_toConstantVal_2885_ = lean_ctor_get(v_val_2881_, 0);
lean_inc_ref(v_toConstantVal_2885_);
lean_dec(v_val_2881_);
v_name_2886_ = lean_ctor_get(v_toConstantVal_2880_, 0);
lean_inc(v_name_2886_);
lean_dec_ref(v_toConstantVal_2880_);
v_name_2887_ = lean_ctor_get(v_toConstantVal_2885_, 0);
lean_inc(v_name_2887_);
lean_dec_ref(v_toConstantVal_2885_);
v___x_2888_ = lean_name_eq(v_name_2886_, v_name_2887_);
lean_dec(v_name_2887_);
lean_dec(v_name_2886_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec_ref(v_config_2557_);
lean_inc(v_mvarId_2558_);
v___x_2889_ = l_Lean_MVarId_getType(v_mvarId_2558_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = l_Lean_LocalDecl_toExpr(v_val_2589_);
v___x_2892_ = l_Lean_Meta_mkNoConfusion(v_a_2890_, v___x_2891_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2558_, v_a_2893_, v___y_2863_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
lean_dec_ref_known(v___x_2894_, 1);
v___x_2895_ = lean_box(v___x_2568_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 0, v___x_2895_);
v___x_2897_ = v___x_2883_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2899_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 1, v___x_2593_);
lean_ctor_set(v___x_2873_, 0, v___x_2897_);
v___x_2899_ = v___x_2873_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2593_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
v_a_2575_ = v___x_2899_;
goto v___jp_2574_;
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_del_object(v___x_2883_);
lean_del_object(v___x_2873_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_2902_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2894_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2894_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_del_object(v___x_2883_);
lean_del_object(v___x_2873_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_2910_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2892_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2892_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_del_object(v___x_2883_);
lean_del_object(v___x_2873_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_2918_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2889_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2889_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_del_object(v___x_2883_);
lean_del_object(v___x_2873_);
v_isEq_2746_ = v___x_2568_;
v___y_2747_ = v___y_2862_;
v___y_2748_ = v___y_2863_;
v___y_2749_ = v___y_2864_;
v___y_2750_ = v___y_2865_;
goto v___jp_2745_;
}
}
}
else
{
lean_dec(v_a_2879_);
lean_dec(v_val_2877_);
lean_del_object(v___x_2873_);
v_isEq_2746_ = v___x_2568_;
v___y_2747_ = v___y_2862_;
v___y_2748_ = v___y_2863_;
v___y_2749_ = v___y_2864_;
v___y_2750_ = v___y_2865_;
goto v___jp_2745_;
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v_val_2877_);
lean_del_object(v___x_2873_);
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2927_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2878_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2878_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
lean_dec(v_a_2876_);
lean_del_object(v___x_2873_);
lean_dec(v_snd_2871_);
v_isEq_2746_ = v___x_2568_;
v___y_2747_ = v___y_2862_;
v___y_2748_ = v___y_2863_;
v___y_2749_ = v___y_2864_;
v___y_2750_ = v___y_2865_;
goto v___jp_2745_;
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_del_object(v___x_2873_);
lean_dec(v_snd_2871_);
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2935_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2875_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2875_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
else
{
lean_dec(v_a_2867_);
v_isEq_2746_ = v___x_2621_;
v___y_2747_ = v___y_2862_;
v___y_2748_ = v___y_2863_;
v___y_2749_ = v___y_2864_;
v___y_2750_ = v___y_2865_;
goto v___jp_2745_;
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2944_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2866_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2866_);
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
v___jp_2952_:
{
lean_object* v___x_2957_; 
lean_inc_ref(v___x_2622_);
v___x_2957_ = l_Lean_refutableHasNotBit_x3f(v___x_2622_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
if (lean_obj_tag(v_a_2958_) == 1)
{
lean_object* v_val_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec_ref(v_config_2557_);
v_val_2959_ = lean_ctor_get(v_a_2958_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_a_2958_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2961_ = v_a_2958_;
v_isShared_2962_ = v_isSharedCheck_2998_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_val_2959_);
lean_dec(v_a_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2998_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; 
lean_inc(v_mvarId_2558_);
v___x_2963_ = l_Lean_MVarId_getType(v_mvarId_2558_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = l_Lean_LocalDecl_toExpr(v_val_2589_);
v___x_2966_ = l_Lean_Meta_mkAbsurd(v_a_2964_, v_val_2959_, v___x_2965_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2968_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2558_, v_a_2967_, v___y_2954_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
lean_dec_ref_known(v___x_2968_, 1);
v___x_2969_ = lean_box(v___x_2568_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2969_);
v___x_2971_ = v___x_2961_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v___x_2593_);
v_a_2575_ = v___x_2972_;
goto v___jp_2574_;
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_del_object(v___x_2961_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_2974_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2968_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2968_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_del_object(v___x_2961_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_2982_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2966_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2966_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_del_object(v___x_2961_);
lean_dec(v_val_2959_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_2990_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2963_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2963_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
else
{
lean_object* v___x_2999_; 
lean_dec(v_a_2958_);
lean_inc_ref(v___x_2622_);
v___x_2999_ = l_Lean_Meta_matchNe_x3f(v___x_2622_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
if (lean_obj_tag(v_a_3000_) == 1)
{
lean_object* v_val_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3070_; 
v_val_3001_ = lean_ctor_get(v_a_3000_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v_a_3000_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3003_ = v_a_3000_;
v_isShared_3004_ = v_isSharedCheck_3070_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_val_3001_);
lean_dec(v_a_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3070_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v_snd_3005_; lean_object* v_fst_3006_; lean_object* v_snd_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3069_; 
v_snd_3005_ = lean_ctor_get(v_val_3001_, 1);
lean_inc(v_snd_3005_);
lean_dec(v_val_3001_);
v_fst_3006_ = lean_ctor_get(v_snd_3005_, 0);
v_snd_3007_ = lean_ctor_get(v_snd_3005_, 1);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_snd_3005_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3009_ = v_snd_3005_;
v_isShared_3010_ = v_isSharedCheck_3069_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_snd_3007_);
lean_inc(v_fst_3006_);
lean_dec(v_snd_3005_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3069_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; 
lean_inc(v_fst_3006_);
v___x_3011_ = l_Lean_Meta_isExprDefEq(v_fst_3006_, v_snd_3007_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; uint8_t v___x_3013_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = lean_unbox(v_a_3012_);
lean_dec(v_a_3012_);
if (v___x_3013_ == 0)
{
lean_del_object(v___x_3009_);
lean_dec(v_fst_3006_);
lean_del_object(v___x_3003_);
v___y_2862_ = v___y_2953_;
v___y_2863_ = v___y_2954_;
v___y_2864_ = v___y_2955_;
v___y_2865_ = v___y_2956_;
goto v___jp_2861_;
}
else
{
lean_object* v___x_3014_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec_ref(v_config_2557_);
lean_inc(v_mvarId_2558_);
v___x_3014_ = l_Lean_MVarId_getType(v_mvarId_2558_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = l_Lean_Meta_mkEqRefl(v_fst_3006_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = l_Lean_LocalDecl_toExpr(v_val_2589_);
v___x_3019_ = l_Lean_Meta_mkAbsurd(v_a_3015_, v_a_3017_, v___x_3018_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2558_, v_a_3020_, v___y_2954_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_dec_ref_known(v___x_3021_, 1);
v___x_3022_ = lean_box(v___x_2568_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3022_);
v___x_3024_ = v___x_3003_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v___x_2593_);
lean_ctor_set(v___x_3009_, 0, v___x_3024_);
v___x_3026_ = v___x_3009_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_2593_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
v_a_2575_ = v___x_3026_;
goto v___jp_2574_;
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_del_object(v___x_3009_);
lean_del_object(v___x_3003_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_3029_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3021_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3021_);
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
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_del_object(v___x_3009_);
lean_del_object(v___x_3003_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_3037_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3019_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3019_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec(v_a_3015_);
lean_del_object(v___x_3009_);
lean_del_object(v___x_3003_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_3045_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3016_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3016_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_del_object(v___x_3009_);
lean_dec(v_fst_3006_);
lean_del_object(v___x_3003_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
v_a_3053_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3014_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3014_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_del_object(v___x_3009_);
lean_dec(v_fst_3006_);
lean_del_object(v___x_3003_);
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_3061_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3011_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3011_);
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
}
else
{
lean_dec(v_a_3000_);
v___y_2862_ = v___y_2953_;
v___y_2863_ = v___y_2954_;
v___y_2864_ = v___y_2955_;
v___y_2865_ = v___y_2956_;
goto v___jp_2861_;
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_3071_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_2999_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_2999_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref(v___x_2622_);
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_3079_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_2957_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_2957_);
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
}
else
{
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_2583_ = v___x_2594_;
goto v___jp_2582_;
}
v___jp_2595_:
{
uint8_t v_emptyType_2602_; 
v_emptyType_2602_ = lean_ctor_get_uint8(v_config_2557_, sizeof(void*)*1 + 1);
if (v_emptyType_2602_ == 0)
{
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_2583_ = v___x_2594_;
goto v___jp_2582_;
}
else
{
if (v___y_2597_ == 0)
{
if (v___y_2596_ == 0)
{
lean_object* v_searchFuel_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_searchFuel_2603_ = lean_ctor_get(v_config_2557_, 0);
v___x_2604_ = l_Lean_LocalDecl_fvarId(v_val_2589_);
lean_dec(v_val_2589_);
lean_inc(v_searchFuel_2603_);
lean_inc(v_mvarId_2558_);
v___x_2605_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_2558_, v___x_2604_, v_searchFuel_2603_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
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
lean_del_object(v___x_2591_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_2583_ = v___x_2594_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v___x_2608_ = lean_box(v___x_2568_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2608_);
v___x_2610_ = v___x_2591_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2593_);
v_a_2575_ = v___x_2611_;
goto v___jp_2574_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_del_object(v___x_2591_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
lean_dec(v_mvarId_2558_);
lean_dec_ref(v_config_2557_);
v_a_2613_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2605_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2605_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_2583_ = v___x_2594_;
goto v___jp_2582_;
}
}
else
{
lean_del_object(v___x_2591_);
lean_dec(v_val_2589_);
lean_del_object(v___x_2572_);
lean_dec(v_snd_2570_);
v_a_2583_ = v___x_2594_;
goto v___jp_2582_;
}
}
}
}
}
v___jp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2576_, 0, v_a_2575_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2576_);
v___x_2578_ = v___x_2572_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_snd_2570_);
v___x_2578_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
return v___x_2579_;
}
}
v___jp_2582_:
{
lean_object* v___x_2584_; size_t v___x_2585_; size_t v___x_2586_; lean_object* v___x_2587_; 
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2581_);
lean_ctor_set(v___x_2584_, 1, v_a_2583_);
v___x_2585_ = ((size_t)1ULL);
v___x_2586_ = lean_usize_add(v_i_2561_, v___x_2585_);
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2557_, v_mvarId_2558_, v_as_2559_, v_sz_2560_, v___x_2586_, v___x_2584_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
return v___x_2587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3153_, lean_object* v_mvarId_3154_, lean_object* v_as_3155_, lean_object* v_sz_3156_, lean_object* v_i_3157_, lean_object* v_b_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
size_t v_sz_boxed_3164_; size_t v_i_boxed_3165_; lean_object* v_res_3166_; 
v_sz_boxed_3164_ = lean_unbox_usize(v_sz_3156_);
lean_dec(v_sz_3156_);
v_i_boxed_3165_ = lean_unbox_usize(v_i_3157_);
lean_dec(v_i_3157_);
v_res_3166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3153_, v_mvarId_3154_, v_as_3155_, v_sz_boxed_3164_, v_i_boxed_3165_, v_b_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec_ref(v_as_3155_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3170_, lean_object* v_mvarId_3171_, lean_object* v_as_3172_, size_t v_sz_3173_, size_t v_i_3174_, lean_object* v_b_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_usize_dec_lt(v_i_3174_, v_sz_3173_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; 
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_b_3175_);
return v___x_3182_;
}
else
{
lean_object* v_snd_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3796_; 
v_snd_3183_ = lean_ctor_get(v_b_3175_, 1);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_b_3175_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; 
v_unused_3797_ = lean_ctor_get(v_b_3175_, 0);
lean_dec(v_unused_3797_);
v___x_3185_ = v_b_3175_;
v_isShared_3186_ = v_isSharedCheck_3796_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_snd_3183_);
lean_dec(v_b_3175_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3796_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_a_3188_; lean_object* v___x_3194_; lean_object* v_a_3196_; lean_object* v_a_3201_; 
v___x_3194_ = lean_box(0);
v_a_3201_ = lean_array_uget(v_as_3172_, v_i_3174_);
if (lean_obj_tag(v_a_3201_) == 0)
{
lean_del_object(v___x_3185_);
v_a_3196_ = v_snd_3183_;
goto v___jp_3195_;
}
else
{
lean_object* v_val_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3795_; 
v_val_3202_ = lean_ctor_get(v_a_3201_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_a_3201_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3204_ = v_a_3201_;
v_isShared_3205_ = v_isSharedCheck_3795_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_val_3202_);
lean_dec(v_a_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3795_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; uint8_t v___y_3209_; uint8_t v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; uint8_t v___x_3235_; 
v___x_3206_ = lean_box(0);
v___x_3207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3235_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3202_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; uint8_t v___y_3238_; uint8_t v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; uint8_t v___y_3265_; uint8_t v___y_3266_; lean_object* v___y_3267_; lean_object* v_a_3268_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; uint8_t v___y_3278_; uint8_t v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; uint8_t v___y_3325_; uint8_t v_isHEq_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; uint8_t v_isEq_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___x_3725_; 
v___x_3236_ = l_Lean_LocalDecl_type(v_val_3202_);
lean_inc_ref(v___x_3236_);
v___x_3725_ = l_Lean_Meta_matchNot_x3f(v___x_3236_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
if (lean_obj_tag(v_a_3726_) == 1)
{
lean_object* v_val_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3786_; 
v_val_3727_ = lean_ctor_get(v_a_3726_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_a_3726_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3729_ = v_a_3726_;
v_isShared_3730_ = v_isSharedCheck_3786_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_val_3727_);
lean_dec(v_a_3726_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3786_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3727_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
if (lean_obj_tag(v_a_3732_) == 1)
{
lean_object* v_val_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
v_val_3733_ = lean_ctor_get(v_a_3732_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_a_3732_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3735_ = v_a_3732_;
v_isShared_3736_ = v_isSharedCheck_3777_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_val_3733_);
lean_dec(v_a_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3777_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3737_; 
lean_inc(v_mvarId_3171_);
v___x_3737_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3737_, 1);
v___x_3739_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3740_ = l_Lean_mkFVar(v_val_3733_);
v___x_3741_ = l_Lean_Expr_app___override(v___x_3739_, v___x_3740_);
v___x_3742_ = l_Lean_Meta_mkFalseElim(v_a_3738_, v___x_3741_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3744_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3743_, v___y_3177_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_dec_ref_known(v___x_3744_, 1);
v___x_3745_ = lean_box(v___x_3181_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3745_);
v___x_3747_ = v___x_3735_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3748_; lean_object* v___x_3750_; 
v___x_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
lean_ctor_set(v___x_3748_, 1, v___x_3206_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set_tag(v___x_3729_, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3748_);
v___x_3750_ = v___x_3729_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
v_a_3188_ = v___x_3750_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_del_object(v___x_3735_);
lean_del_object(v___x_3729_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3753_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3744_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3744_);
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
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_del_object(v___x_3735_);
lean_del_object(v___x_3729_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3761_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3742_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3742_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_del_object(v___x_3735_);
lean_dec(v_val_3733_);
lean_del_object(v___x_3729_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3769_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3737_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3737_);
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
lean_dec(v_a_3732_);
lean_del_object(v___x_3729_);
v___y_3589_ = v___y_3176_;
v___y_3590_ = v___y_3177_;
v___y_3591_ = v___y_3178_;
v___y_3592_ = v___y_3179_;
goto v___jp_3588_;
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_del_object(v___x_3729_);
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3778_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3731_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3731_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
}
else
{
lean_dec(v_a_3726_);
v___y_3589_ = v___y_3176_;
v___y_3590_ = v___y_3177_;
v___y_3591_ = v___y_3178_;
v___y_3592_ = v___y_3179_;
goto v___jp_3588_;
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3787_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3725_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3725_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
v___jp_3237_:
{
uint8_t v_genDiseq_3244_; 
v_genDiseq_3244_ = lean_ctor_get_uint8(v_config_3170_, sizeof(void*)*1 + 2);
if (v_genDiseq_3244_ == 0)
{
lean_dec_ref(v___x_3236_);
v___y_3209_ = v___y_3238_;
v___y_3210_ = v___y_3239_;
v___y_3211_ = v___y_3240_;
v___y_3212_ = v___y_3241_;
v___y_3213_ = v___y_3242_;
v___y_3214_ = v___y_3243_;
goto v___jp_3208_;
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3236_);
lean_dec_ref(v___x_3236_);
if (v___x_3245_ == 0)
{
v___y_3209_ = v___y_3238_;
v___y_3210_ = v___y_3239_;
v___y_3211_ = v___y_3240_;
v___y_3212_ = v___y_3241_;
v___y_3213_ = v___y_3242_;
v___y_3214_ = v___y_3243_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3246_; 
lean_inc(v_val_3202_);
lean_inc(v_mvarId_3171_);
v___x_3246_ = l_Lean_Meta_processGenDiseq(v_mvarId_3171_, v_val_3202_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; uint8_t v___x_3248_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v___x_3248_ = lean_unbox(v_a_3247_);
lean_dec(v_a_3247_);
if (v___x_3248_ == 0)
{
v___y_3209_ = v___y_3238_;
v___y_3210_ = v___y_3239_;
v___y_3211_ = v___y_3240_;
v___y_3212_ = v___y_3241_;
v___y_3213_ = v___y_3242_;
v___y_3214_ = v___y_3243_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3249_ = lean_box(v___x_3181_);
v___x_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
v___x_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
lean_ctor_set(v___x_3251_, 1, v___x_3206_);
v___x_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
v_a_3188_ = v___x_3252_;
goto v___jp_3187_;
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3253_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3246_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3246_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
}
v___jp_3261_:
{
uint8_t v___x_3269_; 
v___x_3269_ = l_Lean_Exception_isInterrupt(v_a_3268_);
if (v___x_3269_ == 0)
{
uint8_t v___x_3270_; 
lean_inc_ref(v_a_3268_);
v___x_3270_ = l_Lean_Exception_isRuntime(v_a_3268_);
if (v___x_3270_ == 0)
{
lean_dec_ref(v_a_3268_);
v___y_3238_ = v___y_3265_;
v___y_3239_ = v___y_3266_;
v___y_3240_ = v___y_3264_;
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___y_3267_;
v___y_3243_ = v___y_3263_;
goto v___jp_3237_;
}
else
{
lean_object* v___x_3271_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_a_3268_);
return v___x_3271_;
}
}
else
{
lean_object* v___x_3272_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_a_3268_);
return v___x_3272_;
}
}
v___jp_3273_:
{
if (lean_obj_tag(v___y_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v_a_3282_ = lean_ctor_get(v___y_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___y_3281_, 1);
v___x_3283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3284_ = l_Lean_Expr_isConstOf(v_a_3282_, v___x_3283_);
lean_dec(v_a_3282_);
if (v___x_3284_ == 0)
{
lean_dec_ref(v___y_3274_);
v___y_3238_ = v___y_3278_;
v___y_3239_ = v___y_3279_;
v___y_3240_ = v___y_3277_;
v___y_3241_ = v___y_3275_;
v___y_3242_ = v___y_3280_;
v___y_3243_ = v___y_3276_;
goto v___jp_3237_;
}
else
{
lean_object* v___x_3285_; 
lean_inc_ref(v___y_3274_);
v___x_3285_ = l_Lean_Meta_mkEqRefl(v___y_3274_, v___y_3277_, v___y_3275_, v___y_3280_, v___y_3276_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; lean_object* v_dummy_3288_; lean_object* v_nargs_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref_known(v___x_3285_, 1);
v___x_3287_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3288_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3289_ = l_Lean_Expr_getAppNumArgs(v___y_3274_);
lean_inc(v_nargs_3289_);
v___x_3290_ = lean_mk_array(v_nargs_3289_, v_dummy_3288_);
v___x_3291_ = lean_unsigned_to_nat(1u);
v___x_3292_ = lean_nat_sub(v_nargs_3289_, v___x_3291_);
lean_dec(v_nargs_3289_);
v___x_3293_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3274_, v___x_3290_, v___x_3292_);
v___x_3294_ = lean_array_push(v___x_3293_, v_a_3286_);
v___x_3295_ = l_Lean_mkAppN(v___x_3287_, v___x_3294_);
lean_dec_ref(v___x_3294_);
lean_inc(v_mvarId_3171_);
v___x_3296_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3277_, v___y_3275_, v___y_3280_, v___y_3276_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
lean_inc(v_val_3202_);
v___x_3298_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3299_ = l_Lean_Meta_mkAbsurd(v_a_3297_, v___x_3298_, v___x_3295_, v___y_3277_, v___y_3275_, v___y_3280_, v___y_3276_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3319_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3302_ = v___x_3299_;
v_isShared_3303_ = v_isSharedCheck_3319_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3299_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3319_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; 
lean_inc(v_mvarId_3171_);
v___x_3304_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3300_, v___y_3275_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; 
v_unused_3317_ = lean_ctor_get(v___x_3304_, 0);
lean_dec(v_unused_3317_);
v___x_3306_ = v___x_3304_;
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
else
{
lean_dec(v___x_3304_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3310_; 
v___x_3308_ = lean_box(v___x_3181_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set_tag(v___x_3306_, 1);
lean_ctor_set(v___x_3306_, 0, v___x_3308_);
v___x_3310_ = v___x_3306_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v___x_3206_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 0, v___x_3311_);
v___x_3313_ = v___x_3302_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
v_a_3188_ = v___x_3313_;
goto v___jp_3187_;
}
}
}
}
else
{
lean_object* v_a_3318_; 
lean_del_object(v___x_3302_);
v_a_3318_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3304_, 1);
v___y_3262_ = v___y_3275_;
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3278_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v_a_3268_ = v_a_3318_;
goto v___jp_3261_;
}
}
}
else
{
lean_object* v_a_3320_; 
v_a_3320_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3299_, 1);
v___y_3262_ = v___y_3275_;
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3278_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v_a_3268_ = v_a_3320_;
goto v___jp_3261_;
}
}
else
{
lean_object* v_a_3321_; 
lean_dec_ref(v___x_3295_);
v_a_3321_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3321_);
lean_dec_ref_known(v___x_3296_, 1);
v___y_3262_ = v___y_3275_;
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3278_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v_a_3268_ = v_a_3321_;
goto v___jp_3261_;
}
}
else
{
lean_object* v_a_3322_; 
lean_dec_ref(v___y_3274_);
v_a_3322_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3285_, 1);
v___y_3262_ = v___y_3275_;
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3278_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v_a_3268_ = v_a_3322_;
goto v___jp_3261_;
}
}
}
else
{
lean_object* v_a_3323_; 
lean_dec_ref(v___y_3274_);
v_a_3323_ = lean_ctor_get(v___y_3281_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___y_3281_, 1);
v___y_3262_ = v___y_3275_;
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3278_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3280_;
v_a_3268_ = v_a_3323_;
goto v___jp_3261_;
}
}
v___jp_3324_:
{
uint8_t v_useDecide_3331_; 
v_useDecide_3331_ = lean_ctor_get_uint8(v_config_3170_, sizeof(void*)*1);
if (v_useDecide_3331_ == 0)
{
v___y_3238_ = v___y_3325_;
v___y_3239_ = v_isHEq_3326_;
v___y_3240_ = v___y_3327_;
v___y_3241_ = v___y_3328_;
v___y_3242_ = v___y_3329_;
v___y_3243_ = v___y_3330_;
goto v___jp_3237_;
}
else
{
uint8_t v___x_3332_; 
v___x_3332_ = l_Lean_Expr_hasFVar(v___x_3236_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; 
lean_inc_ref(v___x_3236_);
v___x_3333_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_3236_, v___y_3328_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; uint8_t v___x_3335_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3333_, 1);
v___x_3335_ = l_Lean_Expr_hasMVar(v_a_3334_);
if (v___x_3335_ == 0)
{
uint8_t v___x_3336_; 
v___x_3336_ = l_Lean_Expr_hasFVar(v_a_3334_);
lean_dec(v_a_3334_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; 
lean_inc_ref(v___x_3236_);
v___x_3337_ = l_Lean_Meta_mkDecide(v___x_3236_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; uint8_t v_transparency_3340_; uint8_t v___x_3341_; uint8_t v___x_3342_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = l_Lean_Meta_Context_config(v___y_3327_);
v_transparency_3340_ = lean_ctor_get_uint8(v___x_3339_, 9);
lean_dec_ref(v___x_3339_);
v___x_3341_ = 1;
v___x_3342_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3340_, v___x_3341_);
if (v___x_3342_ == 0)
{
lean_object* v_keyedConfig_3343_; uint8_t v_trackZetaDelta_3344_; lean_object* v_zetaDeltaSet_3345_; lean_object* v_lctx_3346_; lean_object* v_localInstances_3347_; lean_object* v_defEqCtx_x3f_3348_; lean_object* v_synthPendingDepth_3349_; lean_object* v_customCanUnfoldPredicate_x3f_3350_; uint8_t v_univApprox_3351_; uint8_t v_inTypeClassResolution_3352_; uint8_t v_cacheInferType_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_keyedConfig_3343_ = lean_ctor_get(v___y_3327_, 0);
v_trackZetaDelta_3344_ = lean_ctor_get_uint8(v___y_3327_, sizeof(void*)*7);
v_zetaDeltaSet_3345_ = lean_ctor_get(v___y_3327_, 1);
v_lctx_3346_ = lean_ctor_get(v___y_3327_, 2);
v_localInstances_3347_ = lean_ctor_get(v___y_3327_, 3);
v_defEqCtx_x3f_3348_ = lean_ctor_get(v___y_3327_, 4);
v_synthPendingDepth_3349_ = lean_ctor_get(v___y_3327_, 5);
v_customCanUnfoldPredicate_x3f_3350_ = lean_ctor_get(v___y_3327_, 6);
v_univApprox_3351_ = lean_ctor_get_uint8(v___y_3327_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3352_ = lean_ctor_get_uint8(v___y_3327_, sizeof(void*)*7 + 2);
v_cacheInferType_3353_ = lean_ctor_get_uint8(v___y_3327_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3343_);
v___x_3354_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3341_, v_keyedConfig_3343_);
lean_inc(v_customCanUnfoldPredicate_x3f_3350_);
lean_inc(v_synthPendingDepth_3349_);
lean_inc(v_defEqCtx_x3f_3348_);
lean_inc_ref(v_localInstances_3347_);
lean_inc_ref(v_lctx_3346_);
lean_inc(v_zetaDeltaSet_3345_);
v___x_3355_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set(v___x_3355_, 1, v_zetaDeltaSet_3345_);
lean_ctor_set(v___x_3355_, 2, v_lctx_3346_);
lean_ctor_set(v___x_3355_, 3, v_localInstances_3347_);
lean_ctor_set(v___x_3355_, 4, v_defEqCtx_x3f_3348_);
lean_ctor_set(v___x_3355_, 5, v_synthPendingDepth_3349_);
lean_ctor_set(v___x_3355_, 6, v_customCanUnfoldPredicate_x3f_3350_);
lean_ctor_set_uint8(v___x_3355_, sizeof(void*)*7, v_trackZetaDelta_3344_);
lean_ctor_set_uint8(v___x_3355_, sizeof(void*)*7 + 1, v_univApprox_3351_);
lean_ctor_set_uint8(v___x_3355_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3352_);
lean_ctor_set_uint8(v___x_3355_, sizeof(void*)*7 + 3, v_cacheInferType_3353_);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3329_);
lean_inc(v___y_3328_);
lean_inc(v_a_3338_);
v___x_3356_ = lean_whnf(v_a_3338_, v___x_3355_, v___y_3328_, v___y_3329_, v___y_3330_);
v___y_3274_ = v_a_3338_;
v___y_3275_ = v___y_3328_;
v___y_3276_ = v___y_3330_;
v___y_3277_ = v___y_3327_;
v___y_3278_ = v___y_3325_;
v___y_3279_ = v_isHEq_3326_;
v___y_3280_ = v___y_3329_;
v___y_3281_ = v___x_3356_;
goto v___jp_3273_;
}
else
{
lean_object* v___x_3357_; 
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3329_);
lean_inc(v___y_3328_);
lean_inc_ref(v___y_3327_);
lean_inc(v_a_3338_);
v___x_3357_ = lean_whnf(v_a_3338_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
v___y_3274_ = v_a_3338_;
v___y_3275_ = v___y_3328_;
v___y_3276_ = v___y_3330_;
v___y_3277_ = v___y_3327_;
v___y_3278_ = v___y_3325_;
v___y_3279_ = v_isHEq_3326_;
v___y_3280_ = v___y_3329_;
v___y_3281_ = v___x_3357_;
goto v___jp_3273_;
}
}
else
{
lean_object* v_a_3358_; 
v_a_3358_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3337_, 1);
v___y_3262_ = v___y_3328_;
v___y_3263_ = v___y_3330_;
v___y_3264_ = v___y_3327_;
v___y_3265_ = v___y_3325_;
v___y_3266_ = v_isHEq_3326_;
v___y_3267_ = v___y_3329_;
v_a_3268_ = v_a_3358_;
goto v___jp_3261_;
}
}
else
{
v___y_3238_ = v___y_3325_;
v___y_3239_ = v_isHEq_3326_;
v___y_3240_ = v___y_3327_;
v___y_3241_ = v___y_3328_;
v___y_3242_ = v___y_3329_;
v___y_3243_ = v___y_3330_;
goto v___jp_3237_;
}
}
else
{
lean_dec(v_a_3334_);
v___y_3238_ = v___y_3325_;
v___y_3239_ = v_isHEq_3326_;
v___y_3240_ = v___y_3327_;
v___y_3241_ = v___y_3328_;
v___y_3242_ = v___y_3329_;
v___y_3243_ = v___y_3330_;
goto v___jp_3237_;
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3359_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3333_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3333_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
v___y_3238_ = v___y_3325_;
v___y_3239_ = v_isHEq_3326_;
v___y_3240_ = v___y_3327_;
v___y_3241_ = v___y_3328_;
v___y_3242_ = v___y_3329_;
v___y_3243_ = v___y_3330_;
goto v___jp_3237_;
}
}
}
v___jp_3367_:
{
lean_object* v___x_3373_; 
lean_inc_ref(v___x_3236_);
v___x_3373_ = l_Lean_Meta_matchHEq_x3f(v___x_3236_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3373_, 1);
if (lean_obj_tag(v_a_3374_) == 1)
{
lean_object* v_val_3375_; lean_object* v_snd_3376_; lean_object* v_snd_3377_; lean_object* v_fst_3378_; lean_object* v_fst_3379_; lean_object* v_fst_3380_; lean_object* v_snd_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3481_; 
v_val_3375_ = lean_ctor_get(v_a_3374_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v_a_3374_, 1);
v_snd_3376_ = lean_ctor_get(v_val_3375_, 1);
lean_inc(v_snd_3376_);
v_snd_3377_ = lean_ctor_get(v_snd_3376_, 1);
lean_inc(v_snd_3377_);
v_fst_3378_ = lean_ctor_get(v_val_3375_, 0);
lean_inc(v_fst_3378_);
lean_dec(v_val_3375_);
v_fst_3379_ = lean_ctor_get(v_snd_3376_, 0);
lean_inc(v_fst_3379_);
lean_dec(v_snd_3376_);
v_fst_3380_ = lean_ctor_get(v_snd_3377_, 0);
v_snd_3381_ = lean_ctor_get(v_snd_3377_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_snd_3377_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3383_ = v_snd_3377_;
v_isShared_3384_ = v_isSharedCheck_3481_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_snd_3381_);
lean_inc(v_fst_3380_);
lean_dec(v_snd_3377_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3481_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3379_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
if (lean_obj_tag(v_a_3386_) == 1)
{
lean_object* v_val_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3472_; 
v_val_3387_ = lean_ctor_get(v_a_3386_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_a_3386_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3389_ = v_a_3386_;
v_isShared_3390_ = v_isSharedCheck_3472_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_val_3387_);
lean_dec(v_a_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3472_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3381_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
if (lean_obj_tag(v_a_3392_) == 1)
{
lean_object* v_toConstantVal_3393_; lean_object* v_val_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3463_; 
v_toConstantVal_3393_ = lean_ctor_get(v_val_3387_, 0);
lean_inc_ref(v_toConstantVal_3393_);
lean_dec(v_val_3387_);
v_val_3394_ = lean_ctor_get(v_a_3392_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_a_3392_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3396_ = v_a_3392_;
v_isShared_3397_ = v_isSharedCheck_3463_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_val_3394_);
lean_dec(v_a_3392_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3463_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_toConstantVal_3398_; lean_object* v_name_3399_; lean_object* v_name_3400_; uint8_t v___x_3401_; 
v_toConstantVal_3398_ = lean_ctor_get(v_val_3394_, 0);
lean_inc_ref(v_toConstantVal_3398_);
lean_dec(v_val_3394_);
v_name_3399_ = lean_ctor_get(v_toConstantVal_3393_, 0);
lean_inc(v_name_3399_);
lean_dec_ref(v_toConstantVal_3393_);
v_name_3400_ = lean_ctor_get(v_toConstantVal_3398_, 0);
lean_inc(v_name_3400_);
lean_dec_ref(v_toConstantVal_3398_);
v___x_3401_ = lean_name_eq(v_name_3399_, v_name_3400_);
lean_dec(v_name_3400_);
lean_dec(v_name_3399_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Meta_isExprDefEq(v_fst_3378_, v_fst_3380_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; uint8_t v___x_3404_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3402_, 1);
v___x_3404_ = lean_unbox(v_a_3403_);
lean_dec(v_a_3403_);
if (v___x_3404_ == 0)
{
lean_del_object(v___x_3396_);
lean_del_object(v___x_3389_);
lean_del_object(v___x_3383_);
v___y_3325_ = v_isEq_3368_;
v_isHEq_3326_ = v___x_3181_;
v___y_3327_ = v___y_3369_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
goto v___jp_3324_;
}
else
{
lean_object* v___x_3405_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
lean_inc(v_mvarId_3171_);
v___x_3405_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3408_ = l_Lean_Meta_mkEqOfHEq(v___x_3407_, v___x_3181_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v___x_3410_ = l_Lean_Meta_mkNoConfusion(v_a_3406_, v_a_3409_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3412_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v___x_3412_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3411_, v___y_3370_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
lean_dec_ref_known(v___x_3412_, 1);
v___x_3413_ = lean_box(v___x_3181_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3413_);
v___x_3415_ = v___x_3396_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3417_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 1, v___x_3206_);
lean_ctor_set(v___x_3383_, 0, v___x_3415_);
v___x_3417_ = v___x_3383_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v___x_3206_);
v___x_3417_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set_tag(v___x_3389_, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3417_);
v___x_3419_ = v___x_3389_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
v_a_3188_ = v___x_3419_;
goto v___jp_3187_;
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_del_object(v___x_3396_);
lean_del_object(v___x_3389_);
lean_del_object(v___x_3383_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3423_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3412_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3412_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_del_object(v___x_3396_);
lean_del_object(v___x_3389_);
lean_del_object(v___x_3383_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3431_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3410_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3410_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec(v_a_3406_);
lean_del_object(v___x_3396_);
lean_del_object(v___x_3389_);
lean_del_object(v___x_3383_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3439_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3408_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3408_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_del_object(v___x_3396_);
lean_del_object(v___x_3389_);
lean_del_object(v___x_3383_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3447_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3405_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3405_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_del_object(v___x_3396_);
lean_del_object(v___x_3389_);
lean_del_object(v___x_3383_);
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3455_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3402_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3402_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
else
{
lean_del_object(v___x_3396_);
lean_del_object(v___x_3389_);
lean_del_object(v___x_3383_);
lean_dec(v_fst_3380_);
lean_dec(v_fst_3378_);
v___y_3325_ = v_isEq_3368_;
v_isHEq_3326_ = v___x_3181_;
v___y_3327_ = v___y_3369_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
goto v___jp_3324_;
}
}
}
else
{
lean_dec(v_a_3392_);
lean_del_object(v___x_3389_);
lean_dec(v_val_3387_);
lean_del_object(v___x_3383_);
lean_dec(v_fst_3380_);
lean_dec(v_fst_3378_);
v___y_3325_ = v_isEq_3368_;
v_isHEq_3326_ = v___x_3181_;
v___y_3327_ = v___y_3369_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
goto v___jp_3324_;
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_del_object(v___x_3389_);
lean_dec(v_val_3387_);
lean_del_object(v___x_3383_);
lean_dec(v_fst_3380_);
lean_dec(v_fst_3378_);
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3464_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3391_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3391_);
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
}
else
{
lean_dec(v_a_3386_);
lean_del_object(v___x_3383_);
lean_dec(v_snd_3381_);
lean_dec(v_fst_3380_);
lean_dec(v_fst_3378_);
v___y_3325_ = v_isEq_3368_;
v_isHEq_3326_ = v___x_3181_;
v___y_3327_ = v___y_3369_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
goto v___jp_3324_;
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_del_object(v___x_3383_);
lean_dec(v_snd_3381_);
lean_dec(v_fst_3380_);
lean_dec(v_fst_3378_);
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3473_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3385_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3385_);
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
}
else
{
lean_dec(v_a_3374_);
v___y_3325_ = v_isEq_3368_;
v_isHEq_3326_ = v___x_3235_;
v___y_3327_ = v___y_3369_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___y_3371_;
v___y_3330_ = v___y_3372_;
goto v___jp_3324_;
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3482_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3373_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3373_);
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
v___jp_3490_:
{
lean_object* v___x_3495_; 
lean_inc_ref(v___x_3236_);
v___x_3495_ = l_Lean_Meta_matchEq_x3f(v___x_3236_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
if (lean_obj_tag(v_a_3496_) == 1)
{
lean_object* v_val_3497_; lean_object* v_snd_3498_; lean_object* v_fst_3499_; lean_object* v_snd_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3579_; 
v_val_3497_ = lean_ctor_get(v_a_3496_, 0);
lean_inc(v_val_3497_);
lean_dec_ref_known(v_a_3496_, 1);
v_snd_3498_ = lean_ctor_get(v_val_3497_, 1);
lean_inc(v_snd_3498_);
lean_dec(v_val_3497_);
v_fst_3499_ = lean_ctor_get(v_snd_3498_, 0);
v_snd_3500_ = lean_ctor_get(v_snd_3498_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_snd_3498_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3502_ = v_snd_3498_;
v_isShared_3503_ = v_isSharedCheck_3579_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_snd_3500_);
lean_inc(v_fst_3499_);
lean_dec(v_snd_3498_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3579_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3499_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3504_, 1);
if (lean_obj_tag(v_a_3505_) == 1)
{
lean_object* v_val_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3570_; 
v_val_3506_ = lean_ctor_get(v_a_3505_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_a_3505_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3508_ = v_a_3505_;
v_isShared_3509_ = v_isSharedCheck_3570_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_val_3506_);
lean_dec(v_a_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3570_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3500_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
if (lean_obj_tag(v_a_3511_) == 1)
{
lean_object* v_toConstantVal_3512_; lean_object* v_val_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3561_; 
v_toConstantVal_3512_ = lean_ctor_get(v_val_3506_, 0);
lean_inc_ref(v_toConstantVal_3512_);
lean_dec(v_val_3506_);
v_val_3513_ = lean_ctor_get(v_a_3511_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_a_3511_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3515_ = v_a_3511_;
v_isShared_3516_ = v_isSharedCheck_3561_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_val_3513_);
lean_dec(v_a_3511_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3561_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v_toConstantVal_3517_; lean_object* v_name_3518_; lean_object* v_name_3519_; uint8_t v___x_3520_; 
v_toConstantVal_3517_ = lean_ctor_get(v_val_3513_, 0);
lean_inc_ref(v_toConstantVal_3517_);
lean_dec(v_val_3513_);
v_name_3518_ = lean_ctor_get(v_toConstantVal_3512_, 0);
lean_inc(v_name_3518_);
lean_dec_ref(v_toConstantVal_3512_);
v_name_3519_ = lean_ctor_get(v_toConstantVal_3517_, 0);
lean_inc(v_name_3519_);
lean_dec_ref(v_toConstantVal_3517_);
v___x_3520_ = lean_name_eq(v_name_3518_, v_name_3519_);
lean_dec(v_name_3519_);
lean_dec(v_name_3518_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
lean_inc(v_mvarId_3171_);
v___x_3521_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3524_ = l_Lean_Meta_mkNoConfusion(v_a_3522_, v___x_3523_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3526_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
v___x_3526_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3525_, v___y_3492_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
lean_dec_ref_known(v___x_3526_, 1);
v___x_3527_ = lean_box(v___x_3181_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3527_);
v___x_3529_ = v___x_3515_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3531_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v___x_3206_);
lean_ctor_set(v___x_3502_, 0, v___x_3529_);
v___x_3531_ = v___x_3502_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3206_);
v___x_3531_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3533_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set_tag(v___x_3508_, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3531_);
v___x_3533_ = v___x_3508_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
v_a_3188_ = v___x_3533_;
goto v___jp_3187_;
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_del_object(v___x_3515_);
lean_del_object(v___x_3508_);
lean_del_object(v___x_3502_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3537_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3526_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3526_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_del_object(v___x_3515_);
lean_del_object(v___x_3508_);
lean_del_object(v___x_3502_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3545_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3524_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3524_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_del_object(v___x_3515_);
lean_del_object(v___x_3508_);
lean_del_object(v___x_3502_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3553_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3521_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3521_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_del_object(v___x_3515_);
lean_del_object(v___x_3508_);
lean_del_object(v___x_3502_);
v_isEq_3368_ = v___x_3181_;
v___y_3369_ = v___y_3491_;
v___y_3370_ = v___y_3492_;
v___y_3371_ = v___y_3493_;
v___y_3372_ = v___y_3494_;
goto v___jp_3367_;
}
}
}
else
{
lean_dec(v_a_3511_);
lean_del_object(v___x_3508_);
lean_dec(v_val_3506_);
lean_del_object(v___x_3502_);
v_isEq_3368_ = v___x_3181_;
v___y_3369_ = v___y_3491_;
v___y_3370_ = v___y_3492_;
v___y_3371_ = v___y_3493_;
v___y_3372_ = v___y_3494_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_del_object(v___x_3508_);
lean_dec(v_val_3506_);
lean_del_object(v___x_3502_);
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3562_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3510_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3510_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
else
{
lean_dec(v_a_3505_);
lean_del_object(v___x_3502_);
lean_dec(v_snd_3500_);
v_isEq_3368_ = v___x_3181_;
v___y_3369_ = v___y_3491_;
v___y_3370_ = v___y_3492_;
v___y_3371_ = v___y_3493_;
v___y_3372_ = v___y_3494_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_del_object(v___x_3502_);
lean_dec(v_snd_3500_);
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3571_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3504_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3504_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
else
{
lean_dec(v_a_3496_);
v_isEq_3368_ = v___x_3235_;
v___y_3369_ = v___y_3491_;
v___y_3370_ = v___y_3492_;
v___y_3371_ = v___y_3493_;
v___y_3372_ = v___y_3494_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3580_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3495_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3495_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
v___jp_3588_:
{
lean_object* v___x_3593_; 
lean_inc_ref(v___x_3236_);
v___x_3593_ = l_Lean_refutableHasNotBit_x3f(v___x_3236_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___x_3593_, 1);
if (lean_obj_tag(v_a_3594_) == 1)
{
lean_object* v_val_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
v_val_3595_ = lean_ctor_get(v_a_3594_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_a_3594_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3597_ = v_a_3594_;
v_isShared_3598_ = v_isSharedCheck_3635_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_val_3595_);
lean_dec(v_a_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3635_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; 
lean_inc(v_mvarId_3171_);
v___x_3599_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3602_ = l_Lean_Meta_mkAbsurd(v_a_3600_, v_val_3595_, v___x_3601_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3604_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v___x_3604_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3603_, v___y_3590_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
lean_dec_ref_known(v___x_3604_, 1);
v___x_3605_ = lean_box(v___x_3181_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3605_);
v___x_3607_ = v___x_3597_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v___x_3206_);
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
v_a_3188_ = v___x_3609_;
goto v___jp_3187_;
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_del_object(v___x_3597_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3611_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3604_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3604_);
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
lean_del_object(v___x_3597_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3619_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3602_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3602_);
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
lean_del_object(v___x_3597_);
lean_dec(v_val_3595_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3627_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3599_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3599_);
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
lean_object* v___x_3636_; 
lean_dec(v_a_3594_);
lean_inc_ref(v___x_3236_);
v___x_3636_ = l_Lean_Meta_matchNe_x3f(v___x_3236_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
if (lean_obj_tag(v_a_3637_) == 1)
{
lean_object* v_val_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3708_; 
v_val_3638_ = lean_ctor_get(v_a_3637_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_a_3637_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3640_ = v_a_3637_;
v_isShared_3641_ = v_isSharedCheck_3708_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_val_3638_);
lean_dec(v_a_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3708_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v_snd_3642_; lean_object* v_fst_3643_; lean_object* v_snd_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3707_; 
v_snd_3642_ = lean_ctor_get(v_val_3638_, 1);
lean_inc(v_snd_3642_);
lean_dec(v_val_3638_);
v_fst_3643_ = lean_ctor_get(v_snd_3642_, 0);
v_snd_3644_ = lean_ctor_get(v_snd_3642_, 1);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_snd_3642_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3646_ = v_snd_3642_;
v_isShared_3647_ = v_isSharedCheck_3707_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_snd_3644_);
lean_inc(v_fst_3643_);
lean_dec(v_snd_3642_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3707_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; 
lean_inc(v_fst_3643_);
v___x_3648_ = l_Lean_Meta_isExprDefEq(v_fst_3643_, v_snd_3644_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; uint8_t v___x_3650_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref_known(v___x_3648_, 1);
v___x_3650_ = lean_unbox(v_a_3649_);
lean_dec(v_a_3649_);
if (v___x_3650_ == 0)
{
lean_del_object(v___x_3646_);
lean_dec(v_fst_3643_);
lean_del_object(v___x_3640_);
v___y_3491_ = v___y_3589_;
v___y_3492_ = v___y_3590_;
v___y_3493_ = v___y_3591_;
v___y_3494_ = v___y_3592_;
goto v___jp_3490_;
}
else
{
lean_object* v___x_3651_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
lean_inc(v_mvarId_3171_);
v___x_3651_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3653_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v___x_3653_ = l_Lean_Meta_mkEqRefl(v_fst_3643_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v___x_3655_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3656_ = l_Lean_Meta_mkAbsurd(v_a_3652_, v_a_3654_, v___x_3655_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3658_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___x_3656_, 1);
v___x_3658_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3657_, v___y_3590_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
lean_dec_ref_known(v___x_3658_, 1);
v___x_3659_ = lean_box(v___x_3181_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3659_);
v___x_3661_ = v___x_3640_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 1, v___x_3206_);
lean_ctor_set(v___x_3646_, 0, v___x_3661_);
v___x_3663_ = v___x_3646_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v___x_3206_);
v___x_3663_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
v_a_3188_ = v___x_3664_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_del_object(v___x_3646_);
lean_del_object(v___x_3640_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3667_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3658_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3658_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_del_object(v___x_3646_);
lean_del_object(v___x_3640_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3675_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3656_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3656_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v_a_3652_);
lean_del_object(v___x_3646_);
lean_del_object(v___x_3640_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3683_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3653_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3653_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_del_object(v___x_3646_);
lean_dec(v_fst_3643_);
lean_del_object(v___x_3640_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3691_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3651_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3651_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_del_object(v___x_3646_);
lean_dec(v_fst_3643_);
lean_del_object(v___x_3640_);
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3699_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3648_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3648_);
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
}
else
{
lean_dec(v_a_3637_);
v___y_3491_ = v___y_3589_;
v___y_3492_ = v___y_3590_;
v___y_3493_ = v___y_3591_;
v___y_3494_ = v___y_3592_;
goto v___jp_3490_;
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3709_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3636_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3636_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v___x_3236_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3717_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3593_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3593_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
else
{
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3196_ = v___x_3207_;
goto v___jp_3195_;
}
v___jp_3208_:
{
uint8_t v_emptyType_3215_; 
v_emptyType_3215_ = lean_ctor_get_uint8(v_config_3170_, sizeof(void*)*1 + 1);
if (v_emptyType_3215_ == 0)
{
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3196_ = v___x_3207_;
goto v___jp_3195_;
}
else
{
if (v___y_3209_ == 0)
{
if (v___y_3210_ == 0)
{
lean_object* v_searchFuel_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_searchFuel_3216_ = lean_ctor_get(v_config_3170_, 0);
v___x_3217_ = l_Lean_LocalDecl_fvarId(v_val_3202_);
lean_dec(v_val_3202_);
lean_inc(v_searchFuel_3216_);
lean_inc(v_mvarId_3171_);
v___x_3218_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_3171_, v___x_3217_, v_searchFuel_3216_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; uint8_t v___x_3220_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = lean_unbox(v_a_3219_);
lean_dec(v_a_3219_);
if (v___x_3220_ == 0)
{
lean_del_object(v___x_3204_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3196_ = v___x_3207_;
goto v___jp_3195_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3221_ = lean_box(v___x_3181_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3221_);
v___x_3223_ = v___x_3204_;
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
lean_ctor_set(v___x_3224_, 1, v___x_3206_);
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
v_a_3188_ = v___x_3225_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_del_object(v___x_3204_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3227_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3218_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3218_);
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
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3196_ = v___x_3207_;
goto v___jp_3195_;
}
}
else
{
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3196_ = v___x_3207_;
goto v___jp_3195_;
}
}
}
}
}
v___jp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_a_3188_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3189_);
v___x_3191_ = v___x_3185_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_snd_3183_);
v___x_3191_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
return v___x_3192_;
}
}
v___jp_3195_:
{
lean_object* v___x_3197_; size_t v___x_3198_; size_t v___x_3199_; 
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3194_);
lean_ctor_set(v___x_3197_, 1, v_a_3196_);
v___x_3198_ = ((size_t)1ULL);
v___x_3199_ = lean_usize_add(v_i_3174_, v___x_3198_);
v_i_3174_ = v___x_3199_;
v_b_3175_ = v___x_3197_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3798_, lean_object* v_mvarId_3799_, lean_object* v_as_3800_, lean_object* v_sz_3801_, lean_object* v_i_3802_, lean_object* v_b_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
size_t v_sz_boxed_3809_; size_t v_i_boxed_3810_; lean_object* v_res_3811_; 
v_sz_boxed_3809_ = lean_unbox_usize(v_sz_3801_);
lean_dec(v_sz_3801_);
v_i_boxed_3810_ = lean_unbox_usize(v_i_3802_);
lean_dec(v_i_3802_);
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3798_, v_mvarId_3799_, v_as_3800_, v_sz_boxed_3809_, v_i_boxed_3810_, v_b_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v_as_3800_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3812_, lean_object* v_mvarId_3813_, lean_object* v_as_3814_, size_t v_sz_3815_, size_t v_i_3816_, lean_object* v_b_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
uint8_t v___x_3823_; 
v___x_3823_ = lean_usize_dec_lt(v_i_3816_, v_sz_3815_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; 
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_b_3817_);
return v___x_3824_;
}
else
{
lean_object* v_snd_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_4438_; 
v_snd_3825_ = lean_ctor_get(v_b_3817_, 1);
v_isSharedCheck_4438_ = !lean_is_exclusive(v_b_3817_);
if (v_isSharedCheck_4438_ == 0)
{
lean_object* v_unused_4439_; 
v_unused_4439_ = lean_ctor_get(v_b_3817_, 0);
lean_dec(v_unused_4439_);
v___x_3827_ = v_b_3817_;
v_isShared_3828_ = v_isSharedCheck_4438_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_snd_3825_);
lean_dec(v_b_3817_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_4438_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v_a_3830_; lean_object* v___x_3836_; lean_object* v_a_3838_; lean_object* v_a_3843_; 
v___x_3836_ = lean_box(0);
v_a_3843_ = lean_array_uget(v_as_3814_, v_i_3816_);
if (lean_obj_tag(v_a_3843_) == 0)
{
lean_del_object(v___x_3827_);
v_a_3838_ = v_snd_3825_;
goto v___jp_3837_;
}
else
{
lean_object* v_val_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_4437_; 
v_val_3844_ = lean_ctor_get(v_a_3843_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v_a_3843_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_3846_ = v_a_3843_;
v_isShared_3847_ = v_isSharedCheck_4437_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_val_3844_);
lean_dec(v_a_3843_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_4437_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; uint8_t v___y_3851_; uint8_t v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; uint8_t v___x_3877_; 
v___x_3848_ = lean_box(0);
v___x_3849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3877_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3844_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; uint8_t v___y_3880_; uint8_t v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; uint8_t v___y_3904_; uint8_t v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v_a_3910_; lean_object* v___y_3916_; uint8_t v___y_3917_; uint8_t v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; uint8_t v___y_3967_; uint8_t v_isHEq_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; uint8_t v_isEq_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___x_4367_; 
v___x_3878_ = l_Lean_LocalDecl_type(v_val_3844_);
lean_inc_ref(v___x_3878_);
v___x_4367_ = l_Lean_Meta_matchNot_x3f(v___x_3878_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4368_);
lean_dec_ref_known(v___x_4367_, 1);
if (lean_obj_tag(v_a_4368_) == 1)
{
lean_object* v_val_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4428_; 
v_val_4369_ = lean_ctor_get(v_a_4368_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_a_4368_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4371_ = v_a_4368_;
v_isShared_4372_ = v_isSharedCheck_4428_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_val_4369_);
lean_dec(v_a_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4428_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4373_; 
v___x_4373_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4369_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_a_4374_);
lean_dec_ref_known(v___x_4373_, 1);
if (lean_obj_tag(v_a_4374_) == 1)
{
lean_object* v_val_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4419_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec_ref(v_config_3812_);
v_val_4375_ = lean_ctor_get(v_a_4374_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v_a_4374_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4377_ = v_a_4374_;
v_isShared_4378_ = v_isSharedCheck_4419_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_val_4375_);
lean_dec(v_a_4374_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4419_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4379_; 
lean_inc(v_mvarId_3813_);
v___x_4379_ = l_Lean_MVarId_getType(v_mvarId_3813_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
v___x_4381_ = l_Lean_LocalDecl_toExpr(v_val_3844_);
v___x_4382_ = l_Lean_mkFVar(v_val_4375_);
v___x_4383_ = l_Lean_Expr_app___override(v___x_4381_, v___x_4382_);
v___x_4384_ = l_Lean_Meta_mkFalseElim(v_a_4380_, v___x_4383_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3813_, v_a_4385_, v___y_3819_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v___x_4387_; lean_object* v___x_4389_; 
lean_dec_ref_known(v___x_4386_, 1);
v___x_4387_ = lean_box(v___x_3823_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 0, v___x_4387_);
v___x_4389_ = v___x_4377_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4390_; lean_object* v___x_4392_; 
v___x_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
lean_ctor_set(v___x_4390_, 1, v___x_3848_);
if (v_isShared_4372_ == 0)
{
lean_ctor_set_tag(v___x_4371_, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4390_);
v___x_4392_ = v___x_4371_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4390_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
v_a_3830_ = v___x_4392_;
goto v___jp_3829_;
}
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
lean_del_object(v___x_4377_);
lean_del_object(v___x_4371_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_4395_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4386_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4386_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_del_object(v___x_4377_);
lean_del_object(v___x_4371_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4403_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4384_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4384_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_del_object(v___x_4377_);
lean_dec(v_val_4375_);
lean_del_object(v___x_4371_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4411_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4379_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4379_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
else
{
lean_dec(v_a_4374_);
lean_del_object(v___x_4371_);
v___y_4231_ = v___y_3818_;
v___y_4232_ = v___y_3819_;
v___y_4233_ = v___y_3820_;
v___y_4234_ = v___y_3821_;
goto v___jp_4230_;
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_del_object(v___x_4371_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4420_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4373_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4373_);
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
else
{
lean_dec(v_a_4368_);
v___y_4231_ = v___y_3818_;
v___y_4232_ = v___y_3819_;
v___y_4233_ = v___y_3820_;
v___y_4234_ = v___y_3821_;
goto v___jp_4230_;
}
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4429_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4367_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4367_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
v___jp_3879_:
{
uint8_t v_genDiseq_3886_; 
v_genDiseq_3886_ = lean_ctor_get_uint8(v_config_3812_, sizeof(void*)*1 + 2);
if (v_genDiseq_3886_ == 0)
{
lean_dec_ref(v___x_3878_);
v___y_3851_ = v___y_3880_;
v___y_3852_ = v___y_3881_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3884_;
v___y_3856_ = v___y_3885_;
goto v___jp_3850_;
}
else
{
uint8_t v___x_3887_; 
v___x_3887_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3878_);
lean_dec_ref(v___x_3878_);
if (v___x_3887_ == 0)
{
v___y_3851_ = v___y_3880_;
v___y_3852_ = v___y_3881_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3884_;
v___y_3856_ = v___y_3885_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3888_; 
lean_inc(v_val_3844_);
lean_inc(v_mvarId_3813_);
v___x_3888_ = l_Lean_Meta_processGenDiseq(v_mvarId_3813_, v_val_3844_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; uint8_t v___x_3890_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3888_, 1);
v___x_3890_ = lean_unbox(v_a_3889_);
lean_dec(v_a_3889_);
if (v___x_3890_ == 0)
{
v___y_3851_ = v___y_3880_;
v___y_3852_ = v___y_3881_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3884_;
v___y_3856_ = v___y_3885_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v___x_3891_ = lean_box(v___x_3823_);
v___x_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v___x_3848_);
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
v_a_3830_ = v___x_3894_;
goto v___jp_3829_;
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_3895_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3888_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3888_);
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
}
}
v___jp_3903_:
{
uint8_t v___x_3911_; 
v___x_3911_ = l_Lean_Exception_isInterrupt(v_a_3910_);
if (v___x_3911_ == 0)
{
uint8_t v___x_3912_; 
lean_inc_ref(v_a_3910_);
v___x_3912_ = l_Lean_Exception_isRuntime(v_a_3910_);
if (v___x_3912_ == 0)
{
lean_dec_ref(v_a_3910_);
v___y_3880_ = v___y_3904_;
v___y_3881_ = v___y_3905_;
v___y_3882_ = v___y_3907_;
v___y_3883_ = v___y_3908_;
v___y_3884_ = v___y_3909_;
v___y_3885_ = v___y_3906_;
goto v___jp_3879_;
}
else
{
lean_object* v___x_3913_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v___x_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3913_, 0, v_a_3910_);
return v___x_3913_;
}
}
else
{
lean_object* v___x_3914_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v___x_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3914_, 0, v_a_3910_);
return v___x_3914_;
}
}
v___jp_3915_:
{
if (lean_obj_tag(v___y_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; 
v_a_3924_ = lean_ctor_get(v___y_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___y_3923_, 1);
v___x_3925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3926_ = l_Lean_Expr_isConstOf(v_a_3924_, v___x_3925_);
lean_dec(v_a_3924_);
if (v___x_3926_ == 0)
{
lean_dec_ref(v___y_3916_);
v___y_3880_ = v___y_3917_;
v___y_3881_ = v___y_3918_;
v___y_3882_ = v___y_3920_;
v___y_3883_ = v___y_3921_;
v___y_3884_ = v___y_3922_;
v___y_3885_ = v___y_3919_;
goto v___jp_3879_;
}
else
{
lean_object* v___x_3927_; 
lean_inc_ref(v___y_3916_);
v___x_3927_ = l_Lean_Meta_mkEqRefl(v___y_3916_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3919_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3929_; lean_object* v_dummy_3930_; lean_object* v_nargs_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___x_3927_, 1);
v___x_3929_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3930_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3931_ = l_Lean_Expr_getAppNumArgs(v___y_3916_);
lean_inc(v_nargs_3931_);
v___x_3932_ = lean_mk_array(v_nargs_3931_, v_dummy_3930_);
v___x_3933_ = lean_unsigned_to_nat(1u);
v___x_3934_ = lean_nat_sub(v_nargs_3931_, v___x_3933_);
lean_dec(v_nargs_3931_);
v___x_3935_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3916_, v___x_3932_, v___x_3934_);
v___x_3936_ = lean_array_push(v___x_3935_, v_a_3928_);
v___x_3937_ = l_Lean_mkAppN(v___x_3929_, v___x_3936_);
lean_dec_ref(v___x_3936_);
lean_inc(v_mvarId_3813_);
v___x_3938_ = l_Lean_MVarId_getType(v_mvarId_3813_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3919_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3939_);
lean_dec_ref_known(v___x_3938_, 1);
lean_inc(v_val_3844_);
v___x_3940_ = l_Lean_LocalDecl_toExpr(v_val_3844_);
v___x_3941_ = l_Lean_Meta_mkAbsurd(v_a_3939_, v___x_3940_, v___x_3937_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3919_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3961_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3944_ = v___x_3941_;
v_isShared_3945_ = v_isSharedCheck_3961_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3941_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3961_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; 
lean_inc(v_mvarId_3813_);
v___x_3946_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3813_, v_a_3942_, v___y_3921_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3958_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3958_ == 0)
{
lean_object* v_unused_3959_; 
v_unused_3959_ = lean_ctor_get(v___x_3946_, 0);
lean_dec(v_unused_3959_);
v___x_3948_ = v___x_3946_;
v_isShared_3949_ = v_isSharedCheck_3958_;
goto v_resetjp_3947_;
}
else
{
lean_dec(v___x_3946_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3958_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; lean_object* v___x_3952_; 
v___x_3950_ = lean_box(v___x_3823_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set_tag(v___x_3948_, 1);
lean_ctor_set(v___x_3948_, 0, v___x_3950_);
v___x_3952_ = v___x_3948_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
lean_ctor_set(v___x_3953_, 1, v___x_3848_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 0, v___x_3953_);
v___x_3955_ = v___x_3944_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
v_a_3830_ = v___x_3955_;
goto v___jp_3829_;
}
}
}
}
else
{
lean_object* v_a_3960_; 
lean_del_object(v___x_3944_);
v_a_3960_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v___x_3946_, 1);
v___y_3904_ = v___y_3917_;
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v_a_3910_ = v_a_3960_;
goto v___jp_3903_;
}
}
}
else
{
lean_object* v_a_3962_; 
v_a_3962_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3941_, 1);
v___y_3904_ = v___y_3917_;
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v_a_3910_ = v_a_3962_;
goto v___jp_3903_;
}
}
else
{
lean_object* v_a_3963_; 
lean_dec_ref(v___x_3937_);
v_a_3963_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3938_, 1);
v___y_3904_ = v___y_3917_;
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v_a_3910_ = v_a_3963_;
goto v___jp_3903_;
}
}
else
{
lean_object* v_a_3964_; 
lean_dec_ref(v___y_3916_);
v_a_3964_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3927_, 1);
v___y_3904_ = v___y_3917_;
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v_a_3910_ = v_a_3964_;
goto v___jp_3903_;
}
}
}
else
{
lean_object* v_a_3965_; 
lean_dec_ref(v___y_3916_);
v_a_3965_ = lean_ctor_get(v___y_3923_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___y_3923_, 1);
v___y_3904_ = v___y_3917_;
v___y_3905_ = v___y_3918_;
v___y_3906_ = v___y_3919_;
v___y_3907_ = v___y_3920_;
v___y_3908_ = v___y_3921_;
v___y_3909_ = v___y_3922_;
v_a_3910_ = v_a_3965_;
goto v___jp_3903_;
}
}
v___jp_3966_:
{
uint8_t v_useDecide_3973_; 
v_useDecide_3973_ = lean_ctor_get_uint8(v_config_3812_, sizeof(void*)*1);
if (v_useDecide_3973_ == 0)
{
v___y_3880_ = v___y_3967_;
v___y_3881_ = v_isHEq_3968_;
v___y_3882_ = v___y_3969_;
v___y_3883_ = v___y_3970_;
v___y_3884_ = v___y_3971_;
v___y_3885_ = v___y_3972_;
goto v___jp_3879_;
}
else
{
uint8_t v___x_3974_; 
v___x_3974_ = l_Lean_Expr_hasFVar(v___x_3878_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; 
lean_inc_ref(v___x_3878_);
v___x_3975_ = l_Lean_instantiateMVars___at___00Lean_Meta_mkGenDiseqFalseProof_x3f_spec__2___redArg(v___x_3878_, v___y_3970_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; uint8_t v___x_3977_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3976_);
lean_dec_ref_known(v___x_3975_, 1);
v___x_3977_ = l_Lean_Expr_hasMVar(v_a_3976_);
if (v___x_3977_ == 0)
{
uint8_t v___x_3978_; 
v___x_3978_ = l_Lean_Expr_hasFVar(v_a_3976_);
lean_dec(v_a_3976_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; 
lean_inc_ref(v___x_3878_);
v___x_3979_ = l_Lean_Meta_mkDecide(v___x_3878_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3981_; uint8_t v_transparency_3982_; uint8_t v___x_3983_; uint8_t v___x_3984_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3981_ = l_Lean_Meta_Context_config(v___y_3969_);
v_transparency_3982_ = lean_ctor_get_uint8(v___x_3981_, 9);
lean_dec_ref(v___x_3981_);
v___x_3983_ = 1;
v___x_3984_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3982_, v___x_3983_);
if (v___x_3984_ == 0)
{
lean_object* v_keyedConfig_3985_; uint8_t v_trackZetaDelta_3986_; lean_object* v_zetaDeltaSet_3987_; lean_object* v_lctx_3988_; lean_object* v_localInstances_3989_; lean_object* v_defEqCtx_x3f_3990_; lean_object* v_synthPendingDepth_3991_; lean_object* v_customCanUnfoldPredicate_x3f_3992_; uint8_t v_univApprox_3993_; uint8_t v_inTypeClassResolution_3994_; uint8_t v_cacheInferType_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v_keyedConfig_3985_ = lean_ctor_get(v___y_3969_, 0);
v_trackZetaDelta_3986_ = lean_ctor_get_uint8(v___y_3969_, sizeof(void*)*7);
v_zetaDeltaSet_3987_ = lean_ctor_get(v___y_3969_, 1);
v_lctx_3988_ = lean_ctor_get(v___y_3969_, 2);
v_localInstances_3989_ = lean_ctor_get(v___y_3969_, 3);
v_defEqCtx_x3f_3990_ = lean_ctor_get(v___y_3969_, 4);
v_synthPendingDepth_3991_ = lean_ctor_get(v___y_3969_, 5);
v_customCanUnfoldPredicate_x3f_3992_ = lean_ctor_get(v___y_3969_, 6);
v_univApprox_3993_ = lean_ctor_get_uint8(v___y_3969_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3994_ = lean_ctor_get_uint8(v___y_3969_, sizeof(void*)*7 + 2);
v_cacheInferType_3995_ = lean_ctor_get_uint8(v___y_3969_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3985_);
v___x_3996_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3983_, v_keyedConfig_3985_);
lean_inc(v_customCanUnfoldPredicate_x3f_3992_);
lean_inc(v_synthPendingDepth_3991_);
lean_inc(v_defEqCtx_x3f_3990_);
lean_inc_ref(v_localInstances_3989_);
lean_inc_ref(v_lctx_3988_);
lean_inc(v_zetaDeltaSet_3987_);
v___x_3997_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
lean_ctor_set(v___x_3997_, 1, v_zetaDeltaSet_3987_);
lean_ctor_set(v___x_3997_, 2, v_lctx_3988_);
lean_ctor_set(v___x_3997_, 3, v_localInstances_3989_);
lean_ctor_set(v___x_3997_, 4, v_defEqCtx_x3f_3990_);
lean_ctor_set(v___x_3997_, 5, v_synthPendingDepth_3991_);
lean_ctor_set(v___x_3997_, 6, v_customCanUnfoldPredicate_x3f_3992_);
lean_ctor_set_uint8(v___x_3997_, sizeof(void*)*7, v_trackZetaDelta_3986_);
lean_ctor_set_uint8(v___x_3997_, sizeof(void*)*7 + 1, v_univApprox_3993_);
lean_ctor_set_uint8(v___x_3997_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3994_);
lean_ctor_set_uint8(v___x_3997_, sizeof(void*)*7 + 3, v_cacheInferType_3995_);
lean_inc(v___y_3972_);
lean_inc_ref(v___y_3971_);
lean_inc(v___y_3970_);
lean_inc(v_a_3980_);
v___x_3998_ = lean_whnf(v_a_3980_, v___x_3997_, v___y_3970_, v___y_3971_, v___y_3972_);
v___y_3916_ = v_a_3980_;
v___y_3917_ = v___y_3967_;
v___y_3918_ = v_isHEq_3968_;
v___y_3919_ = v___y_3972_;
v___y_3920_ = v___y_3969_;
v___y_3921_ = v___y_3970_;
v___y_3922_ = v___y_3971_;
v___y_3923_ = v___x_3998_;
goto v___jp_3915_;
}
else
{
lean_object* v___x_3999_; 
lean_inc(v___y_3972_);
lean_inc_ref(v___y_3971_);
lean_inc(v___y_3970_);
lean_inc_ref(v___y_3969_);
lean_inc(v_a_3980_);
v___x_3999_ = lean_whnf(v_a_3980_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
v___y_3916_ = v_a_3980_;
v___y_3917_ = v___y_3967_;
v___y_3918_ = v_isHEq_3968_;
v___y_3919_ = v___y_3972_;
v___y_3920_ = v___y_3969_;
v___y_3921_ = v___y_3970_;
v___y_3922_ = v___y_3971_;
v___y_3923_ = v___x_3999_;
goto v___jp_3915_;
}
}
else
{
lean_object* v_a_4000_; 
v_a_4000_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3979_, 1);
v___y_3904_ = v___y_3967_;
v___y_3905_ = v_isHEq_3968_;
v___y_3906_ = v___y_3972_;
v___y_3907_ = v___y_3969_;
v___y_3908_ = v___y_3970_;
v___y_3909_ = v___y_3971_;
v_a_3910_ = v_a_4000_;
goto v___jp_3903_;
}
}
else
{
v___y_3880_ = v___y_3967_;
v___y_3881_ = v_isHEq_3968_;
v___y_3882_ = v___y_3969_;
v___y_3883_ = v___y_3970_;
v___y_3884_ = v___y_3971_;
v___y_3885_ = v___y_3972_;
goto v___jp_3879_;
}
}
else
{
lean_dec(v_a_3976_);
v___y_3880_ = v___y_3967_;
v___y_3881_ = v_isHEq_3968_;
v___y_3882_ = v___y_3969_;
v___y_3883_ = v___y_3970_;
v___y_3884_ = v___y_3971_;
v___y_3885_ = v___y_3972_;
goto v___jp_3879_;
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4001_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3975_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3975_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
v___y_3880_ = v___y_3967_;
v___y_3881_ = v_isHEq_3968_;
v___y_3882_ = v___y_3969_;
v___y_3883_ = v___y_3970_;
v___y_3884_ = v___y_3971_;
v___y_3885_ = v___y_3972_;
goto v___jp_3879_;
}
}
}
v___jp_4009_:
{
lean_object* v___x_4015_; 
lean_inc_ref(v___x_3878_);
v___x_4015_ = l_Lean_Meta_matchHEq_x3f(v___x_3878_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
if (lean_obj_tag(v_a_4016_) == 1)
{
lean_object* v_val_4017_; lean_object* v_snd_4018_; lean_object* v_snd_4019_; lean_object* v_fst_4020_; lean_object* v_fst_4021_; lean_object* v_fst_4022_; lean_object* v_snd_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4123_; 
v_val_4017_ = lean_ctor_get(v_a_4016_, 0);
lean_inc(v_val_4017_);
lean_dec_ref_known(v_a_4016_, 1);
v_snd_4018_ = lean_ctor_get(v_val_4017_, 1);
lean_inc(v_snd_4018_);
v_snd_4019_ = lean_ctor_get(v_snd_4018_, 1);
lean_inc(v_snd_4019_);
v_fst_4020_ = lean_ctor_get(v_val_4017_, 0);
lean_inc(v_fst_4020_);
lean_dec(v_val_4017_);
v_fst_4021_ = lean_ctor_get(v_snd_4018_, 0);
lean_inc(v_fst_4021_);
lean_dec(v_snd_4018_);
v_fst_4022_ = lean_ctor_get(v_snd_4019_, 0);
v_snd_4023_ = lean_ctor_get(v_snd_4019_, 1);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_snd_4019_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4025_ = v_snd_4019_;
v_isShared_4026_ = v_isSharedCheck_4123_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_snd_4023_);
lean_inc(v_fst_4022_);
lean_dec(v_snd_4019_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4123_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4021_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v___x_4027_, 1);
if (lean_obj_tag(v_a_4028_) == 1)
{
lean_object* v_val_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4114_; 
v_val_4029_ = lean_ctor_get(v_a_4028_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_a_4028_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4031_ = v_a_4028_;
v_isShared_4032_ = v_isSharedCheck_4114_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_val_4029_);
lean_dec(v_a_4028_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4114_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4023_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
if (lean_obj_tag(v_a_4034_) == 1)
{
lean_object* v_toConstantVal_4035_; lean_object* v_val_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4105_; 
v_toConstantVal_4035_ = lean_ctor_get(v_val_4029_, 0);
lean_inc_ref(v_toConstantVal_4035_);
lean_dec(v_val_4029_);
v_val_4036_ = lean_ctor_get(v_a_4034_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_a_4034_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4038_ = v_a_4034_;
v_isShared_4039_ = v_isSharedCheck_4105_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_val_4036_);
lean_dec(v_a_4034_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4105_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v_toConstantVal_4040_; lean_object* v_name_4041_; lean_object* v_name_4042_; uint8_t v___x_4043_; 
v_toConstantVal_4040_ = lean_ctor_get(v_val_4036_, 0);
lean_inc_ref(v_toConstantVal_4040_);
lean_dec(v_val_4036_);
v_name_4041_ = lean_ctor_get(v_toConstantVal_4035_, 0);
lean_inc(v_name_4041_);
lean_dec_ref(v_toConstantVal_4035_);
v_name_4042_ = lean_ctor_get(v_toConstantVal_4040_, 0);
lean_inc(v_name_4042_);
lean_dec_ref(v_toConstantVal_4040_);
v___x_4043_ = lean_name_eq(v_name_4041_, v_name_4042_);
lean_dec(v_name_4042_);
lean_dec(v_name_4041_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Lean_Meta_isExprDefEq(v_fst_4020_, v_fst_4022_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; uint8_t v___x_4046_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
lean_inc(v_a_4045_);
lean_dec_ref_known(v___x_4044_, 1);
v___x_4046_ = lean_unbox(v_a_4045_);
lean_dec(v_a_4045_);
if (v___x_4046_ == 0)
{
lean_del_object(v___x_4038_);
lean_del_object(v___x_4031_);
lean_del_object(v___x_4025_);
v___y_3967_ = v_isEq_4010_;
v_isHEq_3968_ = v___x_3823_;
v___y_3969_ = v___y_4011_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
goto v___jp_3966_;
}
else
{
lean_object* v___x_4047_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec_ref(v_config_3812_);
lean_inc(v_mvarId_3813_);
v___x_4047_ = l_Lean_MVarId_getType(v_mvarId_3813_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___x_4047_, 1);
v___x_4049_ = l_Lean_LocalDecl_toExpr(v_val_3844_);
v___x_4050_ = l_Lean_Meta_mkEqOfHEq(v___x_4049_, v___x_3823_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4052_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref_known(v___x_4050_, 1);
v___x_4052_ = l_Lean_Meta_mkNoConfusion(v_a_4048_, v_a_4051_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v___x_4054_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref_known(v___x_4052_, 1);
v___x_4054_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3813_, v_a_4053_, v___y_4012_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v___x_4055_; lean_object* v___x_4057_; 
lean_dec_ref_known(v___x_4054_, 1);
v___x_4055_ = lean_box(v___x_3823_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v___x_4055_);
v___x_4057_ = v___x_4038_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4059_; 
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 1, v___x_3848_);
lean_ctor_set(v___x_4025_, 0, v___x_4057_);
v___x_4059_ = v___x_4025_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4057_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___x_3848_);
v___x_4059_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4061_; 
if (v_isShared_4032_ == 0)
{
lean_ctor_set_tag(v___x_4031_, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4059_);
v___x_4061_ = v___x_4031_;
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
v_a_3830_ = v___x_4061_;
goto v___jp_3829_;
}
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_del_object(v___x_4038_);
lean_del_object(v___x_4031_);
lean_del_object(v___x_4025_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_4065_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4054_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4054_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_del_object(v___x_4038_);
lean_del_object(v___x_4031_);
lean_del_object(v___x_4025_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4073_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4052_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4052_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_a_4048_);
lean_del_object(v___x_4038_);
lean_del_object(v___x_4031_);
lean_del_object(v___x_4025_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4081_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4050_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4050_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_del_object(v___x_4038_);
lean_del_object(v___x_4031_);
lean_del_object(v___x_4025_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4089_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4047_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4047_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_del_object(v___x_4038_);
lean_del_object(v___x_4031_);
lean_del_object(v___x_4025_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4097_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4044_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4044_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
else
{
lean_del_object(v___x_4038_);
lean_del_object(v___x_4031_);
lean_del_object(v___x_4025_);
lean_dec(v_fst_4022_);
lean_dec(v_fst_4020_);
v___y_3967_ = v_isEq_4010_;
v_isHEq_3968_ = v___x_3823_;
v___y_3969_ = v___y_4011_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
goto v___jp_3966_;
}
}
}
else
{
lean_dec(v_a_4034_);
lean_del_object(v___x_4031_);
lean_dec(v_val_4029_);
lean_del_object(v___x_4025_);
lean_dec(v_fst_4022_);
lean_dec(v_fst_4020_);
v___y_3967_ = v_isEq_4010_;
v_isHEq_3968_ = v___x_3823_;
v___y_3969_ = v___y_4011_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
goto v___jp_3966_;
}
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
lean_del_object(v___x_4031_);
lean_dec(v_val_4029_);
lean_del_object(v___x_4025_);
lean_dec(v_fst_4022_);
lean_dec(v_fst_4020_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4106_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4033_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4033_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
}
else
{
lean_dec(v_a_4028_);
lean_del_object(v___x_4025_);
lean_dec(v_snd_4023_);
lean_dec(v_fst_4022_);
lean_dec(v_fst_4020_);
v___y_3967_ = v_isEq_4010_;
v_isHEq_3968_ = v___x_3823_;
v___y_3969_ = v___y_4011_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
goto v___jp_3966_;
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_del_object(v___x_4025_);
lean_dec(v_snd_4023_);
lean_dec(v_fst_4022_);
lean_dec(v_fst_4020_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4115_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4027_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4027_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
}
else
{
lean_dec(v_a_4016_);
v___y_3967_ = v_isEq_4010_;
v_isHEq_3968_ = v___x_3877_;
v___y_3969_ = v___y_4011_;
v___y_3970_ = v___y_4012_;
v___y_3971_ = v___y_4013_;
v___y_3972_ = v___y_4014_;
goto v___jp_3966_;
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4124_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4015_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4015_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
v___jp_4132_:
{
lean_object* v___x_4137_; 
lean_inc_ref(v___x_3878_);
v___x_4137_ = l_Lean_Meta_matchEq_x3f(v___x_3878_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref_known(v___x_4137_, 1);
if (lean_obj_tag(v_a_4138_) == 1)
{
lean_object* v_val_4139_; lean_object* v_snd_4140_; lean_object* v_fst_4141_; lean_object* v_snd_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4221_; 
v_val_4139_ = lean_ctor_get(v_a_4138_, 0);
lean_inc(v_val_4139_);
lean_dec_ref_known(v_a_4138_, 1);
v_snd_4140_ = lean_ctor_get(v_val_4139_, 1);
lean_inc(v_snd_4140_);
lean_dec(v_val_4139_);
v_fst_4141_ = lean_ctor_get(v_snd_4140_, 0);
v_snd_4142_ = lean_ctor_get(v_snd_4140_, 1);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_snd_4140_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4144_ = v_snd_4140_;
v_isShared_4145_ = v_isSharedCheck_4221_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_snd_4142_);
lean_inc(v_fst_4141_);
lean_dec(v_snd_4140_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4221_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4141_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4146_, 1);
if (lean_obj_tag(v_a_4147_) == 1)
{
lean_object* v_val_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4212_; 
v_val_4148_ = lean_ctor_get(v_a_4147_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_a_4147_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4150_ = v_a_4147_;
v_isShared_4151_ = v_isSharedCheck_4212_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_val_4148_);
lean_dec(v_a_4147_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4212_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4142_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
if (lean_obj_tag(v_a_4153_) == 1)
{
lean_object* v_toConstantVal_4154_; lean_object* v_val_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4203_; 
v_toConstantVal_4154_ = lean_ctor_get(v_val_4148_, 0);
lean_inc_ref(v_toConstantVal_4154_);
lean_dec(v_val_4148_);
v_val_4155_ = lean_ctor_get(v_a_4153_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v_a_4153_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4157_ = v_a_4153_;
v_isShared_4158_ = v_isSharedCheck_4203_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_val_4155_);
lean_dec(v_a_4153_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4203_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v_toConstantVal_4159_; lean_object* v_name_4160_; lean_object* v_name_4161_; uint8_t v___x_4162_; 
v_toConstantVal_4159_ = lean_ctor_get(v_val_4155_, 0);
lean_inc_ref(v_toConstantVal_4159_);
lean_dec(v_val_4155_);
v_name_4160_ = lean_ctor_get(v_toConstantVal_4154_, 0);
lean_inc(v_name_4160_);
lean_dec_ref(v_toConstantVal_4154_);
v_name_4161_ = lean_ctor_get(v_toConstantVal_4159_, 0);
lean_inc(v_name_4161_);
lean_dec_ref(v_toConstantVal_4159_);
v___x_4162_ = lean_name_eq(v_name_4160_, v_name_4161_);
lean_dec(v_name_4161_);
lean_dec(v_name_4160_);
if (v___x_4162_ == 0)
{
lean_object* v___x_4163_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec_ref(v_config_3812_);
lean_inc(v_mvarId_3813_);
v___x_4163_ = l_Lean_MVarId_getType(v_mvarId_3813_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4163_, 1);
v___x_4165_ = l_Lean_LocalDecl_toExpr(v_val_3844_);
v___x_4166_ = l_Lean_Meta_mkNoConfusion(v_a_4164_, v___x_4165_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4168_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___x_4168_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3813_, v_a_4167_, v___y_4134_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v___x_4169_; lean_object* v___x_4171_; 
lean_dec_ref_known(v___x_4168_, 1);
v___x_4169_ = lean_box(v___x_3823_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 0, v___x_4169_);
v___x_4171_ = v___x_4157_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4169_);
v___x_4171_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
lean_object* v___x_4173_; 
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 1, v___x_3848_);
lean_ctor_set(v___x_4144_, 0, v___x_4171_);
v___x_4173_ = v___x_4144_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4171_);
lean_ctor_set(v_reuseFailAlloc_4177_, 1, v___x_3848_);
v___x_4173_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4175_; 
if (v_isShared_4151_ == 0)
{
lean_ctor_set_tag(v___x_4150_, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4173_);
v___x_4175_ = v___x_4150_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
v_a_3830_ = v___x_4175_;
goto v___jp_3829_;
}
}
}
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_del_object(v___x_4157_);
lean_del_object(v___x_4150_);
lean_del_object(v___x_4144_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_4179_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4168_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4168_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_del_object(v___x_4157_);
lean_del_object(v___x_4150_);
lean_del_object(v___x_4144_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4187_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4166_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4166_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_del_object(v___x_4157_);
lean_del_object(v___x_4150_);
lean_del_object(v___x_4144_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4195_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4163_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4163_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_del_object(v___x_4157_);
lean_del_object(v___x_4150_);
lean_del_object(v___x_4144_);
v_isEq_4010_ = v___x_3823_;
v___y_4011_ = v___y_4133_;
v___y_4012_ = v___y_4134_;
v___y_4013_ = v___y_4135_;
v___y_4014_ = v___y_4136_;
goto v___jp_4009_;
}
}
}
else
{
lean_dec(v_a_4153_);
lean_del_object(v___x_4150_);
lean_dec(v_val_4148_);
lean_del_object(v___x_4144_);
v_isEq_4010_ = v___x_3823_;
v___y_4011_ = v___y_4133_;
v___y_4012_ = v___y_4134_;
v___y_4013_ = v___y_4135_;
v___y_4014_ = v___y_4136_;
goto v___jp_4009_;
}
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
lean_del_object(v___x_4150_);
lean_dec(v_val_4148_);
lean_del_object(v___x_4144_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4204_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4152_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4152_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
}
else
{
lean_dec(v_a_4147_);
lean_del_object(v___x_4144_);
lean_dec(v_snd_4142_);
v_isEq_4010_ = v___x_3823_;
v___y_4011_ = v___y_4133_;
v___y_4012_ = v___y_4134_;
v___y_4013_ = v___y_4135_;
v___y_4014_ = v___y_4136_;
goto v___jp_4009_;
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_del_object(v___x_4144_);
lean_dec(v_snd_4142_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4213_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4146_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4146_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
else
{
lean_dec(v_a_4138_);
v_isEq_4010_ = v___x_3877_;
v___y_4011_ = v___y_4133_;
v___y_4012_ = v___y_4134_;
v___y_4013_ = v___y_4135_;
v___y_4014_ = v___y_4136_;
goto v___jp_4009_;
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4222_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4137_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4137_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
v___jp_4230_:
{
lean_object* v___x_4235_; 
lean_inc_ref(v___x_3878_);
v___x_4235_ = l_Lean_refutableHasNotBit_x3f(v___x_3878_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4235_, 1);
if (lean_obj_tag(v_a_4236_) == 1)
{
lean_object* v_val_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4277_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec_ref(v_config_3812_);
v_val_4237_ = lean_ctor_get(v_a_4236_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v_a_4236_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4239_ = v_a_4236_;
v_isShared_4240_ = v_isSharedCheck_4277_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_val_4237_);
lean_dec(v_a_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4277_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; 
lean_inc(v_mvarId_3813_);
v___x_4241_ = l_Lean_MVarId_getType(v_mvarId_3813_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
v___x_4243_ = l_Lean_LocalDecl_toExpr(v_val_3844_);
v___x_4244_ = l_Lean_Meta_mkAbsurd(v_a_4242_, v_val_4237_, v___x_4243_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4246_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
v___x_4246_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3813_, v_a_4245_, v___y_4232_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v___x_4247_; lean_object* v___x_4249_; 
lean_dec_ref_known(v___x_4246_, 1);
v___x_4247_ = lean_box(v___x_3823_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4247_);
v___x_4249_ = v___x_4239_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4249_);
lean_ctor_set(v___x_4250_, 1, v___x_3848_);
v___x_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
v_a_3830_ = v___x_4251_;
goto v___jp_3829_;
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_del_object(v___x_4239_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_4253_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4246_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4246_);
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
lean_del_object(v___x_4239_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4261_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4244_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4244_);
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
lean_del_object(v___x_4239_);
lean_dec(v_val_4237_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4269_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4241_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4241_);
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
lean_object* v___x_4278_; 
lean_dec(v_a_4236_);
lean_inc_ref(v___x_3878_);
v___x_4278_ = l_Lean_Meta_matchNe_x3f(v___x_3878_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4279_);
lean_dec_ref_known(v___x_4278_, 1);
if (lean_obj_tag(v_a_4279_) == 1)
{
lean_object* v_val_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4350_; 
v_val_4280_ = lean_ctor_get(v_a_4279_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_a_4279_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4282_ = v_a_4279_;
v_isShared_4283_ = v_isSharedCheck_4350_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_val_4280_);
lean_dec(v_a_4279_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4350_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v_snd_4284_; lean_object* v_fst_4285_; lean_object* v_snd_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4349_; 
v_snd_4284_ = lean_ctor_get(v_val_4280_, 1);
lean_inc(v_snd_4284_);
lean_dec(v_val_4280_);
v_fst_4285_ = lean_ctor_get(v_snd_4284_, 0);
v_snd_4286_ = lean_ctor_get(v_snd_4284_, 1);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_snd_4284_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4288_ = v_snd_4284_;
v_isShared_4289_ = v_isSharedCheck_4349_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_snd_4286_);
lean_inc(v_fst_4285_);
lean_dec(v_snd_4284_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4349_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4290_; 
lean_inc(v_fst_4285_);
v___x_4290_ = l_Lean_Meta_isExprDefEq(v_fst_4285_, v_snd_4286_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; uint8_t v___x_4292_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v___x_4290_, 1);
v___x_4292_ = lean_unbox(v_a_4291_);
lean_dec(v_a_4291_);
if (v___x_4292_ == 0)
{
lean_del_object(v___x_4288_);
lean_dec(v_fst_4285_);
lean_del_object(v___x_4282_);
v___y_4133_ = v___y_4231_;
v___y_4134_ = v___y_4232_;
v___y_4135_ = v___y_4233_;
v___y_4136_ = v___y_4234_;
goto v___jp_4132_;
}
else
{
lean_object* v___x_4293_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec_ref(v_config_3812_);
lean_inc(v_mvarId_3813_);
v___x_4293_ = l_Lean_MVarId_getType(v_mvarId_3813_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4295_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v___x_4293_, 1);
v___x_4295_ = l_Lean_Meta_mkEqRefl(v_fst_4285_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
v___x_4297_ = l_Lean_LocalDecl_toExpr(v_val_3844_);
v___x_4298_ = l_Lean_Meta_mkAbsurd(v_a_4294_, v_a_4296_, v___x_4297_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4300_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v___x_4298_, 1);
v___x_4300_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3813_, v_a_4299_, v___y_4232_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v___x_4301_; lean_object* v___x_4303_; 
lean_dec_ref_known(v___x_4300_, 1);
v___x_4301_ = lean_box(v___x_3823_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v___x_4301_);
v___x_4303_ = v___x_4282_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4301_);
v___x_4303_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
lean_object* v___x_4305_; 
if (v_isShared_4289_ == 0)
{
lean_ctor_set(v___x_4288_, 1, v___x_3848_);
lean_ctor_set(v___x_4288_, 0, v___x_4303_);
v___x_4305_ = v___x_4288_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4303_);
lean_ctor_set(v_reuseFailAlloc_4307_, 1, v___x_3848_);
v___x_4305_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
v_a_3830_ = v___x_4306_;
goto v___jp_3829_;
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_del_object(v___x_4288_);
lean_del_object(v___x_4282_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_4309_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4300_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4300_);
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
lean_del_object(v___x_4288_);
lean_del_object(v___x_4282_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4317_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4319_ = v___x_4298_;
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4298_);
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
lean_dec(v_a_4294_);
lean_del_object(v___x_4288_);
lean_del_object(v___x_4282_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4325_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4295_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4295_);
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
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_del_object(v___x_4288_);
lean_dec(v_fst_4285_);
lean_del_object(v___x_4282_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
v_a_4333_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4293_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4293_);
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
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
lean_del_object(v___x_4288_);
lean_dec(v_fst_4285_);
lean_del_object(v___x_4282_);
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4341_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4290_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4290_);
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
}
else
{
lean_dec(v_a_4279_);
v___y_4133_ = v___y_4231_;
v___y_4134_ = v___y_4232_;
v___y_4135_ = v___y_4233_;
v___y_4136_ = v___y_4234_;
goto v___jp_4132_;
}
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4351_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4278_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4278_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec_ref(v___x_3878_);
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_4359_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4235_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4235_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
}
else
{
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_3838_ = v___x_3849_;
goto v___jp_3837_;
}
v___jp_3850_:
{
uint8_t v_emptyType_3857_; 
v_emptyType_3857_ = lean_ctor_get_uint8(v_config_3812_, sizeof(void*)*1 + 1);
if (v_emptyType_3857_ == 0)
{
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_3838_ = v___x_3849_;
goto v___jp_3837_;
}
else
{
if (v___y_3851_ == 0)
{
if (v___y_3852_ == 0)
{
lean_object* v_searchFuel_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_searchFuel_3858_ = lean_ctor_get(v_config_3812_, 0);
v___x_3859_ = l_Lean_LocalDecl_fvarId(v_val_3844_);
lean_dec(v_val_3844_);
lean_inc(v_searchFuel_3858_);
lean_inc(v_mvarId_3813_);
v___x_3860_ = l_Lean_Meta_elimEmptyInductive(v_mvarId_3813_, v___x_3859_, v_searchFuel_3858_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; uint8_t v___x_3862_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3862_ = lean_unbox(v_a_3861_);
lean_dec(v_a_3861_);
if (v___x_3862_ == 0)
{
lean_del_object(v___x_3846_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_3838_ = v___x_3849_;
goto v___jp_3837_;
}
else
{
lean_object* v___x_3863_; lean_object* v___x_3865_; 
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v___x_3863_ = lean_box(v___x_3823_);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 0, v___x_3863_);
v___x_3865_ = v___x_3846_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
lean_ctor_set(v___x_3866_, 1, v___x_3848_);
v___x_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
v_a_3830_ = v___x_3867_;
goto v___jp_3829_;
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_del_object(v___x_3846_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_dec(v_mvarId_3813_);
lean_dec_ref(v_config_3812_);
v_a_3869_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3860_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3860_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
else
{
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_3838_ = v___x_3849_;
goto v___jp_3837_;
}
}
else
{
lean_del_object(v___x_3846_);
lean_dec(v_val_3844_);
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
v_a_3838_ = v___x_3849_;
goto v___jp_3837_;
}
}
}
}
}
v___jp_3829_:
{
lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3831_, 0, v_a_3830_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3831_);
v___x_3833_ = v___x_3827_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_snd_3825_);
v___x_3833_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
return v___x_3834_;
}
}
v___jp_3837_:
{
lean_object* v___x_3839_; size_t v___x_3840_; size_t v___x_3841_; lean_object* v___x_3842_; 
v___x_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3836_);
lean_ctor_set(v___x_3839_, 1, v_a_3838_);
v___x_3840_ = ((size_t)1ULL);
v___x_3841_ = lean_usize_add(v_i_3816_, v___x_3840_);
v___x_3842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3812_, v_mvarId_3813_, v_as_3814_, v_sz_3815_, v___x_3841_, v___x_3839_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4440_, lean_object* v_mvarId_4441_, lean_object* v_as_4442_, lean_object* v_sz_4443_, lean_object* v_i_4444_, lean_object* v_b_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
size_t v_sz_boxed_4451_; size_t v_i_boxed_4452_; lean_object* v_res_4453_; 
v_sz_boxed_4451_ = lean_unbox_usize(v_sz_4443_);
lean_dec(v_sz_4443_);
v_i_boxed_4452_ = lean_unbox_usize(v_i_4444_);
lean_dec(v_i_4444_);
v_res_4453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4440_, v_mvarId_4441_, v_as_4442_, v_sz_boxed_4451_, v_i_boxed_4452_, v_b_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec_ref(v_as_4442_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4454_, lean_object* v_config_4455_, lean_object* v_mvarId_4456_, lean_object* v_n_4457_, lean_object* v_b_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
if (lean_obj_tag(v_n_4457_) == 0)
{
lean_object* v_cs_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; size_t v_sz_4467_; size_t v___x_4468_; lean_object* v___x_4469_; 
v_cs_4464_ = lean_ctor_get(v_n_4457_, 0);
v___x_4465_ = lean_box(0);
v___x_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
lean_ctor_set(v___x_4466_, 1, v_b_4458_);
v_sz_4467_ = lean_array_size(v_cs_4464_);
v___x_4468_ = ((size_t)0ULL);
v___x_4469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4454_, v_config_4455_, v_mvarId_4456_, v_cs_4464_, v_sz_4467_, v___x_4468_, v___x_4466_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4484_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4472_ = v___x_4469_;
v_isShared_4473_ = v_isSharedCheck_4484_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4469_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4484_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v_fst_4474_; 
v_fst_4474_ = lean_ctor_get(v_a_4470_, 0);
if (lean_obj_tag(v_fst_4474_) == 0)
{
lean_object* v_snd_4475_; lean_object* v___x_4476_; lean_object* v___x_4478_; 
v_snd_4475_ = lean_ctor_get(v_a_4470_, 1);
lean_inc(v_snd_4475_);
lean_dec(v_a_4470_);
v___x_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4476_, 0, v_snd_4475_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 0, v___x_4476_);
v___x_4478_ = v___x_4472_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4476_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
else
{
lean_object* v_val_4480_; lean_object* v___x_4482_; 
lean_inc_ref(v_fst_4474_);
lean_dec(v_a_4470_);
v_val_4480_ = lean_ctor_get(v_fst_4474_, 0);
lean_inc(v_val_4480_);
lean_dec_ref_known(v_fst_4474_, 1);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 0, v_val_4480_);
v___x_4482_ = v___x_4472_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_val_4480_);
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
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
v_a_4485_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4469_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4469_);
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
}
else
{
lean_object* v_vs_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; size_t v_sz_4496_; size_t v___x_4497_; lean_object* v___x_4498_; 
v_vs_4493_ = lean_ctor_get(v_n_4457_, 0);
v___x_4494_ = lean_box(0);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
lean_ctor_set(v___x_4495_, 1, v_b_4458_);
v_sz_4496_ = lean_array_size(v_vs_4493_);
v___x_4497_ = ((size_t)0ULL);
v___x_4498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4455_, v_mvarId_4456_, v_vs_4493_, v_sz_4496_, v___x_4497_, v___x_4495_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4513_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4501_ = v___x_4498_;
v_isShared_4502_ = v_isSharedCheck_4513_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4498_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4513_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v_fst_4503_; 
v_fst_4503_ = lean_ctor_get(v_a_4499_, 0);
if (lean_obj_tag(v_fst_4503_) == 0)
{
lean_object* v_snd_4504_; lean_object* v___x_4505_; lean_object* v___x_4507_; 
v_snd_4504_ = lean_ctor_get(v_a_4499_, 1);
lean_inc(v_snd_4504_);
lean_dec(v_a_4499_);
v___x_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4505_, 0, v_snd_4504_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v___x_4505_);
v___x_4507_ = v___x_4501_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
else
{
lean_object* v_val_4509_; lean_object* v___x_4511_; 
lean_inc_ref(v_fst_4503_);
lean_dec(v_a_4499_);
v_val_4509_ = lean_ctor_get(v_fst_4503_, 0);
lean_inc(v_val_4509_);
lean_dec_ref_known(v_fst_4503_, 1);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v_val_4509_);
v___x_4511_ = v___x_4501_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_val_4509_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
v_a_4514_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4498_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4498_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4522_, lean_object* v_config_4523_, lean_object* v_mvarId_4524_, lean_object* v_as_4525_, size_t v_sz_4526_, size_t v_i_4527_, lean_object* v_b_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
uint8_t v___x_4534_; 
v___x_4534_ = lean_usize_dec_lt(v_i_4527_, v_sz_4526_);
if (v___x_4534_ == 0)
{
lean_object* v___x_4535_; 
lean_dec(v_mvarId_4524_);
lean_dec_ref(v_config_4523_);
v___x_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4535_, 0, v_b_4528_);
return v___x_4535_;
}
else
{
lean_object* v_snd_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4570_; 
v_snd_4536_ = lean_ctor_get(v_b_4528_, 1);
v_isSharedCheck_4570_ = !lean_is_exclusive(v_b_4528_);
if (v_isSharedCheck_4570_ == 0)
{
lean_object* v_unused_4571_; 
v_unused_4571_ = lean_ctor_get(v_b_4528_, 0);
lean_dec(v_unused_4571_);
v___x_4538_ = v_b_4528_;
v_isShared_4539_ = v_isSharedCheck_4570_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_snd_4536_);
lean_dec(v_b_4528_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4570_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4540_; lean_object* v_a_4541_; lean_object* v___x_4542_; 
v___x_4540_ = lean_box(0);
v_a_4541_ = lean_array_uget_borrowed(v_as_4525_, v_i_4527_);
lean_inc(v_snd_4536_);
lean_inc(v_mvarId_4524_);
lean_inc_ref(v_config_4523_);
v___x_4542_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4522_, v_config_4523_, v_mvarId_4524_, v_a_4541_, v_snd_4536_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4561_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4545_ = v___x_4542_;
v_isShared_4546_ = v_isSharedCheck_4561_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4542_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4561_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
if (lean_obj_tag(v_a_4543_) == 0)
{
lean_object* v___x_4547_; lean_object* v___x_4549_; 
lean_dec(v_mvarId_4524_);
lean_dec_ref(v_config_4523_);
v___x_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4547_, 0, v_a_4543_);
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 0, v___x_4547_);
v___x_4549_ = v___x_4538_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_snd_4536_);
v___x_4549_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
lean_object* v___x_4551_; 
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 0, v___x_4549_);
v___x_4551_ = v___x_4545_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; 
lean_del_object(v___x_4545_);
lean_dec(v_snd_4536_);
v_a_4554_ = lean_ctor_get(v_a_4543_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v_a_4543_, 1);
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 1, v_a_4554_);
lean_ctor_set(v___x_4538_, 0, v___x_4540_);
v___x_4556_ = v___x_4538_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4540_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_a_4554_);
v___x_4556_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
size_t v___x_4557_; size_t v___x_4558_; 
v___x_4557_ = ((size_t)1ULL);
v___x_4558_ = lean_usize_add(v_i_4527_, v___x_4557_);
v_i_4527_ = v___x_4558_;
v_b_4528_ = v___x_4556_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_del_object(v___x_4538_);
lean_dec(v_snd_4536_);
lean_dec(v_mvarId_4524_);
lean_dec_ref(v_config_4523_);
v_a_4562_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4542_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4542_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4572_, lean_object* v_config_4573_, lean_object* v_mvarId_4574_, lean_object* v_as_4575_, lean_object* v_sz_4576_, lean_object* v_i_4577_, lean_object* v_b_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
size_t v_sz_boxed_4584_; size_t v_i_boxed_4585_; lean_object* v_res_4586_; 
v_sz_boxed_4584_ = lean_unbox_usize(v_sz_4576_);
lean_dec(v_sz_4576_);
v_i_boxed_4585_ = lean_unbox_usize(v_i_4577_);
lean_dec(v_i_4577_);
v_res_4586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4572_, v_config_4573_, v_mvarId_4574_, v_as_4575_, v_sz_boxed_4584_, v_i_boxed_4585_, v_b_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec_ref(v_as_4575_);
lean_dec_ref(v_init_4572_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4587_, lean_object* v_config_4588_, lean_object* v_mvarId_4589_, lean_object* v_n_4590_, lean_object* v_b_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4587_, v_config_4588_, v_mvarId_4589_, v_n_4590_, v_b_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec_ref(v_n_4590_);
lean_dec_ref(v_init_4587_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4598_, lean_object* v_mvarId_4599_, lean_object* v_t_4600_, lean_object* v_init_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v_root_4607_; lean_object* v_tail_4608_; lean_object* v___x_4609_; 
v_root_4607_ = lean_ctor_get(v_t_4600_, 0);
v_tail_4608_ = lean_ctor_get(v_t_4600_, 1);
lean_inc(v_mvarId_4599_);
lean_inc_ref(v_config_4598_);
lean_inc_ref(v_init_4601_);
v___x_4609_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4601_, v_config_4598_, v_mvarId_4599_, v_root_4607_, v_init_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
lean_dec_ref(v_init_4601_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4646_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4646_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4646_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
if (lean_obj_tag(v_a_4610_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; 
lean_dec(v_mvarId_4599_);
lean_dec_ref(v_config_4598_);
v_a_4614_ = lean_ctor_get(v_a_4610_, 0);
lean_inc(v_a_4614_);
lean_dec_ref_known(v_a_4610_, 1);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v_a_4614_);
v___x_4616_ = v___x_4612_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4614_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; size_t v_sz_4621_; size_t v___x_4622_; lean_object* v___x_4623_; 
lean_del_object(v___x_4612_);
v_a_4618_ = lean_ctor_get(v_a_4610_, 0);
lean_inc(v_a_4618_);
lean_dec_ref_known(v_a_4610_, 1);
v___x_4619_ = lean_box(0);
v___x_4620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
lean_ctor_set(v___x_4620_, 1, v_a_4618_);
v_sz_4621_ = lean_array_size(v_tail_4608_);
v___x_4622_ = ((size_t)0ULL);
v___x_4623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4598_, v_mvarId_4599_, v_tail_4608_, v_sz_4621_, v___x_4622_, v___x_4620_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4637_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4637_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4637_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v_fst_4628_; 
v_fst_4628_ = lean_ctor_get(v_a_4624_, 0);
if (lean_obj_tag(v_fst_4628_) == 0)
{
lean_object* v_snd_4629_; lean_object* v___x_4631_; 
v_snd_4629_ = lean_ctor_get(v_a_4624_, 1);
lean_inc(v_snd_4629_);
lean_dec(v_a_4624_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v_snd_4629_);
v___x_4631_ = v___x_4626_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_snd_4629_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
else
{
lean_object* v_val_4633_; lean_object* v___x_4635_; 
lean_inc_ref(v_fst_4628_);
lean_dec(v_a_4624_);
v_val_4633_ = lean_ctor_get(v_fst_4628_, 0);
lean_inc(v_val_4633_);
lean_dec_ref_known(v_fst_4628_, 1);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v_val_4633_);
v___x_4635_ = v___x_4626_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_val_4633_);
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
else
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
v_a_4638_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4623_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4623_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
}
}
}
else
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
lean_dec(v_mvarId_4599_);
lean_dec_ref(v_config_4598_);
v_a_4647_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4649_ = v___x_4609_;
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4609_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4655_, lean_object* v_mvarId_4656_, lean_object* v_t_4657_, lean_object* v_init_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4655_, v_mvarId_4656_, v_t_4657_, v_init_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec_ref(v_t_4657_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4665_, lean_object* v___x_4666_, lean_object* v_config_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v___x_4673_; 
lean_inc(v_mvarId_4665_);
v___x_4673_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4665_, v___x_4666_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v___x_4674_; 
lean_dec_ref_known(v___x_4673_, 1);
lean_inc(v_mvarId_4665_);
v___x_4674_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4665_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4708_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4677_ = v___x_4674_;
v_isShared_4678_ = v_isSharedCheck_4708_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4674_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4708_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
uint8_t v___x_4679_; 
v___x_4679_ = lean_unbox(v_a_4675_);
if (v___x_4679_ == 0)
{
lean_object* v_lctx_4680_; lean_object* v_decls_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
lean_del_object(v___x_4677_);
v_lctx_4680_ = lean_ctor_get(v___y_4668_, 2);
v_decls_4681_ = lean_ctor_get(v_lctx_4680_, 1);
v___x_4682_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4683_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4667_, v_mvarId_4665_, v_decls_4681_, v___x_4682_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4696_; 
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4686_ = v___x_4683_;
v_isShared_4687_ = v_isSharedCheck_4696_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4683_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4696_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v_fst_4688_; 
v_fst_4688_ = lean_ctor_get(v_a_4684_, 0);
lean_inc(v_fst_4688_);
lean_dec(v_a_4684_);
if (lean_obj_tag(v_fst_4688_) == 0)
{
lean_object* v___x_4690_; 
if (v_isShared_4687_ == 0)
{
lean_ctor_set(v___x_4686_, 0, v_a_4675_);
v___x_4690_ = v___x_4686_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4675_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
else
{
lean_object* v_val_4692_; lean_object* v___x_4694_; 
lean_dec(v_a_4675_);
v_val_4692_ = lean_ctor_get(v_fst_4688_, 0);
lean_inc(v_val_4692_);
lean_dec_ref_known(v_fst_4688_, 1);
if (v_isShared_4687_ == 0)
{
lean_ctor_set(v___x_4686_, 0, v_val_4692_);
v___x_4694_ = v___x_4686_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_val_4692_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec(v_a_4675_);
v_a_4697_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4683_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4683_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
else
{
lean_object* v___x_4706_; 
lean_dec_ref(v_config_4667_);
lean_dec(v_mvarId_4665_);
if (v_isShared_4678_ == 0)
{
v___x_4706_ = v___x_4677_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4675_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
else
{
lean_dec_ref(v_config_4667_);
lean_dec(v_mvarId_4665_);
return v___x_4674_;
}
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
lean_dec_ref(v_config_4667_);
lean_dec(v_mvarId_4665_);
v_a_4709_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4673_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4673_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4717_, lean_object* v___x_4718_, lean_object* v_config_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4717_, v___x_4718_, v_config_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4728_, lean_object* v_config_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v___x_4735_; lean_object* v___f_4736_; lean_object* v___x_4737_; 
v___x_4735_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4728_);
v___f_4736_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4736_, 0, v_mvarId_4728_);
lean_closure_set(v___f_4736_, 1, v___x_4735_);
lean_closure_set(v___f_4736_, 2, v_config_4729_);
v___x_4737_ = l_Lean_MVarId_withContext___at___00Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4728_, v___f_4736_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4738_, lean_object* v_config_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Lean_MVarId_contradictionCore(v_mvarId_4738_, v_config_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_);
lean_dec(v_a_4743_);
lean_dec_ref(v_a_4742_);
lean_dec(v_a_4741_);
lean_dec_ref(v_a_4740_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4746_, lean_object* v_config_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_){
_start:
{
lean_object* v___x_4753_; 
lean_inc(v_mvarId_4746_);
v___x_4753_ = l_Lean_MVarId_contradictionCore(v_mvarId_4746_, v_config_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4766_; 
v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4756_ = v___x_4753_;
v_isShared_4757_ = v_isSharedCheck_4766_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4753_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4766_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
uint8_t v___x_4758_; 
v___x_4758_ = lean_unbox(v_a_4754_);
lean_dec(v_a_4754_);
if (v___x_4758_ == 0)
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
lean_del_object(v___x_4756_);
v___x_4759_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4760_ = lean_box(0);
v___x_4761_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4759_, v_mvarId_4746_, v___x_4760_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
return v___x_4761_;
}
else
{
lean_object* v___x_4762_; lean_object* v___x_4764_; 
lean_dec(v_mvarId_4746_);
v___x_4762_ = lean_box(0);
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v___x_4762_);
v___x_4764_ = v___x_4756_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
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
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
lean_dec(v_mvarId_4746_);
v_a_4767_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4753_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4753_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4775_, lean_object* v_config_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Lean_MVarId_contradiction(v_mvarId_4775_, v_config_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_);
lean_dec(v_a_4780_);
lean_dec_ref(v_a_4779_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4845_; uint8_t v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4845_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4846_ = 0;
v___x_4847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4848_ = l_Lean_registerTraceClass(v___x_4845_, v___x_4846_, v___x_4847_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4850_;
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
