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
lean_object* v___x_570_; lean_object* v_env_571_; lean_object* v___x_572_; lean_object* v_toCold_573_; lean_object* v_mctx_574_; lean_object* v_lctx_575_; lean_object* v_options_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_570_ = lean_st_ref_get(v___y_568_);
v_env_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_env_571_);
lean_dec(v___x_570_);
v___x_572_ = lean_st_ref_get(v___y_566_);
v_toCold_573_ = lean_ctor_get(v___y_567_, 0);
v_mctx_574_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_mctx_574_);
lean_dec(v___x_572_);
v_lctx_575_ = lean_ctor_get(v___y_565_, 2);
v_options_576_ = lean_ctor_get(v_toCold_573_, 2);
lean_inc_ref(v_options_576_);
lean_inc_ref(v_lctx_575_);
v___x_577_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_577_, 0, v_env_571_);
lean_ctor_set(v___x_577_, 1, v_mctx_574_);
lean_ctor_set(v___x_577_, 2, v_lctx_575_);
lean_ctor_set(v___x_577_, 3, v_options_576_);
v___x_578_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_msgData_564_);
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
v_ref_599_ = lean_ctor_get(v___y_596_, 2);
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
lean_object* v___x_623_; lean_object* v___x_624_; double v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_623_ = lean_box(0);
v___x_624_ = lean_box(0);
v___x_625_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_626_ = 0;
v___x_627_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_628_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_628_, 0, v_cls_592_);
lean_ctor_set(v___x_628_, 1, v___x_624_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_ctor_set_float(v___x_628_, sizeof(void*)*3, v___x_625_);
lean_ctor_set_float(v___x_628_, sizeof(void*)*3 + 8, v___x_625_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*3 + 16, v___x_626_);
v___x_629_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_630_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v_a_601_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_inc(v_ref_599_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v_ref_599_);
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
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_env_607_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_nextMacroScope_608_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_ngen_609_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_auxDeclNGen_610_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_641_, 5, v_cache_611_);
lean_ctor_set(v_reuseFailAlloc_641_, 6, v_messages_612_);
lean_ctor_set(v_reuseFailAlloc_641_, 7, v_infoState_613_);
lean_ctor_set(v_reuseFailAlloc_641_, 8, v_snapshotTasks_614_);
v___x_636_ = v_reuseFailAlloc_641_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_st_ref_put(v___y_597_, v___x_636_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_623_);
v___x_639_ = v___x_603_;
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
size_t v_sz_boxed_674_; size_t v___x_15944__boxed_675_; uint8_t v___x_15946__boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v___x_15944__boxed_675_ = lean_unbox_usize(v___x_665_);
lean_dec(v___x_665_);
v___x_15946__boxed_676_ = lean_unbox(v___x_667_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_661_, v_mvarId_662_, v_fields_663_, v_sz_boxed_674_, v___x_15944__boxed_675_, v___x_666_, v___x_15946__boxed_676_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
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
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_865_; 
v_a_820_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_865_ == 0)
{
v___x_822_ = v___x_764_;
v_isShared_823_ = v_isSharedCheck_865_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_764_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_865_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v___y_825_; uint8_t v___x_863_; 
v___x_863_ = l_Lean_Exception_isInterrupt(v_a_820_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; 
lean_inc(v_a_820_);
v___x_864_ = l_Lean_Exception_isRuntime(v_a_820_);
v___y_825_ = v___x_864_;
goto v___jp_824_;
}
else
{
v___y_825_ = v___x_863_;
goto v___jp_824_;
}
v___jp_824_:
{
if (v___y_825_ == 0)
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_866_, lean_object* v_fvarId_867_, lean_object* v___x_868_, lean_object* v___x_869_, lean_object* v___x_870_, lean_object* v_val_871_, lean_object* v___x_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v___x_16066__boxed_879_; uint8_t v___x_16069__boxed_880_; lean_object* v_res_881_; 
v___x_16066__boxed_879_ = lean_unbox(v___x_869_);
v___x_16069__boxed_880_ = lean_unbox(v___x_872_);
v_res_881_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_866_, v_fvarId_867_, v___x_868_, v___x_16066__boxed_879_, v___x_870_, v_val_871_, v___x_16069__boxed_880_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
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
lean_object* v_a_1085_; lean_object* v___y_1087_; lean_object* v___y_1088_; uint8_t v___y_1089_; lean_object* v___y_1108_; lean_object* v_a_1109_; lean_object* v___x_1112_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
v___x_1112_ = lean_apply_5(v_x_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, lean_box(0));
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; uint8_t v___x_1114_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
v___x_1114_ = lean_unbox(v_a_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec_ref_known(v___x_1112_, 1);
v___x_1115_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1085_, v___y_1080_, v___y_1082_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v_a_1085_);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v___x_1115_, 0);
lean_dec(v_unused_1123_);
v___x_1117_ = v___x_1115_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_dec(v___x_1115_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v_a_1113_);
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1113_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec(v_a_1113_);
v_a_1124_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1115_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1115_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
lean_inc(v_a_1124_);
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
v___y_1108_ = v___x_1129_;
v_a_1109_ = v_a_1124_;
goto v___jp_1107_;
}
}
}
}
else
{
lean_dec(v_a_1113_);
lean_dec(v_a_1085_);
return v___x_1112_;
}
}
else
{
lean_object* v_a_1132_; 
v_a_1132_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1132_);
v___y_1108_ = v___x_1112_;
v_a_1109_ = v_a_1132_;
goto v___jp_1107_;
}
v___jp_1086_:
{
if (v___y_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec_ref(v___y_1088_);
v___x_1090_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1085_, v___y_1080_, v___y_1082_);
lean_dec(v_a_1085_);
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
lean_ctor_set(v___x_1092_, 0, v___y_1087_);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___y_1087_);
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
lean_dec_ref(v___y_1087_);
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
lean_dec_ref(v___y_1087_);
lean_dec(v_a_1085_);
return v___y_1088_;
}
}
v___jp_1107_:
{
uint8_t v___x_1110_; 
v___x_1110_ = l_Lean_Exception_isInterrupt(v_a_1109_);
if (v___x_1110_ == 0)
{
uint8_t v___x_1111_; 
lean_inc_ref(v_a_1109_);
v___x_1111_ = l_Lean_Exception_isRuntime(v_a_1109_);
v___y_1087_ = v_a_1109_;
v___y_1088_ = v___y_1108_;
v___y_1089_ = v___x_1111_;
goto v___jp_1086_;
}
else
{
v___y_1087_ = v_a_1109_;
v___y_1088_ = v___y_1108_;
v___y_1089_ = v___x_1110_;
goto v___jp_1086_;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_x_1078_);
v_a_1133_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1084_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1084_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1148_, lean_object* v_x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1148_, v_x_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_a_1164_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1155_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1155_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1172_, lean_object* v_x_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1172_, v_x_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1180_, lean_object* v_mvarId_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1181_, v_x_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1189_, lean_object* v_mvarId_1190_, lean_object* v_x_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1189_, v_mvarId_1190_, v_x_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1198_, lean_object* v_fuel_1199_, lean_object* v_fvarId_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_MVarId_exfalso(v_mvarId_1198_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1208_ = lean_st_mk_ref(v_fuel_1199_);
v___x_1209_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1207_, v_fvarId_1200_, v___x_1208_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_st_ref_get(v___x_1208_);
lean_dec(v___x_1208_);
lean_dec(v___x_1214_);
if (v_isShared_1213_ == 0)
{
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1210_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
else
{
lean_dec(v___x_1208_);
return v___x_1209_;
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_fvarId_1200_);
lean_dec(v_fuel_1199_);
v_a_1219_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1206_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1206_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1227_, lean_object* v_fuel_1228_, lean_object* v_fvarId_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1227_, v_fuel_1228_, v_fvarId_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1236_, lean_object* v___f_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1236_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; uint8_t v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
v___x_1245_ = lean_unbox(v_a_1244_);
lean_dec(v_a_1244_);
if (v___x_1245_ == 0)
{
lean_dec_ref(v___f_1237_);
return v___x_1243_;
}
else
{
lean_object* v___x_1246_; 
lean_dec_ref_known(v___x_1243_, 1);
v___x_1246_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1246_;
}
}
else
{
lean_dec_ref(v___f_1237_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1247_, lean_object* v___f_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1247_, v___f_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1255_, lean_object* v_fvarId_1256_, lean_object* v_fuel_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___x_1265_; 
lean_inc(v_fvarId_1256_);
lean_inc(v_mvarId_1255_);
v___f_1263_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1263_, 0, v_mvarId_1255_);
lean_closure_set(v___f_1263_, 1, v_fuel_1257_);
lean_closure_set(v___f_1263_, 2, v_fvarId_1256_);
v___f_1264_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1264_, 0, v_fvarId_1256_);
lean_closure_set(v___f_1264_, 1, v___f_1263_);
v___x_1265_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1255_, v___f_1264_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1266_, lean_object* v_fvarId_1267_, lean_object* v_fuel_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1266_, v_fvarId_1267_, v_fuel_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1275_){
_start:
{
uint8_t v___x_1276_; 
v___x_1276_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1277_){
_start:
{
uint8_t v_res_1278_; lean_object* v_r_1279_; 
v_res_1278_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1277_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1280_, lean_object* v_acc_1281_){
_start:
{
if (lean_obj_tag(v_e_1280_) == 7)
{
lean_object* v_binderType_1282_; lean_object* v_body_1283_; uint8_t v___y_1285_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_binderType_1282_ = lean_ctor_get(v_e_1280_, 1);
v_body_1283_ = lean_ctor_get(v_e_1280_, 2);
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_expr_has_loose_bvar(v_body_1283_, v___x_1289_);
if (v___x_1290_ == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Lean_Expr_isEq(v_binderType_1282_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = l_Lean_Expr_isHEq(v_binderType_1282_);
v___y_1285_ = v___x_1292_;
goto v___jp_1284_;
}
else
{
v___y_1285_ = v___x_1291_;
goto v___jp_1284_;
}
}
else
{
uint8_t v___x_1293_; 
v___x_1293_ = 0;
v___y_1285_ = v___x_1293_;
goto v___jp_1284_;
}
v___jp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_box(v___y_1285_);
v___x_1287_ = lean_array_push(v_acc_1281_, v___x_1286_);
v_e_1280_ = v_body_1283_;
v_acc_1281_ = v___x_1287_;
goto _start;
}
}
else
{
return v_acc_1281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1294_, lean_object* v_acc_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1294_, v_acc_1295_);
lean_dec_ref(v_e_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1299_){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1301_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1299_, v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Meta_mkGenDiseqMask(v_e_1302_);
lean_dec_ref(v_e_1302_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___f_1311_; lean_object* v___x_4344__overap_1312_; lean_object* v___x_1313_; 
v___f_1311_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1312_ = lean_panic_fn_borrowed(v___f_1311_, v_msg_1305_);
lean_inc(v___y_1309_);
lean_inc_ref(v___y_1308_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
v___x_1313_ = lean_apply_5(v___x_4344__overap_1312_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, lean_box(0));
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = l_Lean_Expr_hasMVar(v_e_1321_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_e_1321_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; lean_object* v_mctx_1327_; lean_object* v___x_1328_; lean_object* v_fst_1329_; lean_object* v_snd_1330_; lean_object* v___x_1331_; lean_object* v_cache_1332_; lean_object* v_zetaDeltaFVarIds_1333_; lean_object* v_postponed_1334_; lean_object* v_diag_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1344_; 
v___x_1326_ = lean_st_ref_get(v___y_1322_);
v_mctx_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc_ref(v_mctx_1327_);
lean_dec(v___x_1326_);
v___x_1328_ = l_Lean_instantiateMVarsCore(v_mctx_1327_, v_e_1321_);
v_fst_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_fst_1329_);
v_snd_1330_ = lean_ctor_get(v___x_1328_, 1);
lean_inc(v_snd_1330_);
lean_dec_ref(v___x_1328_);
v___x_1331_ = lean_st_ref_take(v___y_1322_);
v_cache_1332_ = lean_ctor_get(v___x_1331_, 1);
v_zetaDeltaFVarIds_1333_ = lean_ctor_get(v___x_1331_, 2);
v_postponed_1334_ = lean_ctor_get(v___x_1331_, 3);
v_diag_1335_ = lean_ctor_get(v___x_1331_, 4);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v___x_1331_, 0);
lean_dec(v_unused_1345_);
v___x_1337_ = v___x_1331_;
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_diag_1335_);
lean_inc(v_postponed_1334_);
lean_inc(v_zetaDeltaFVarIds_1333_);
lean_inc(v_cache_1332_);
lean_dec(v___x_1331_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v_snd_1330_);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_snd_1330_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_cache_1332_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_zetaDeltaFVarIds_1333_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_postponed_1334_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_diag_1335_);
v___x_1340_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_st_ref_put(v___y_1322_, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_fst_1329_);
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1346_, v___y_1347_);
lean_dec(v___y_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1350_, v___y_1352_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1364_, uint8_t v_allowLevelAssignments_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1365_, v_k_1364_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1380_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1371_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1371_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1388_, lean_object* v_allowLevelAssignments_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1395_; lean_object* v_res_1396_; 
v_allowLevelAssignments_boxed_1395_ = lean_unbox(v_allowLevelAssignments_1389_);
v_res_1396_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1388_, v_allowLevelAssignments_boxed_1395_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1397_, lean_object* v_k_1398_, uint8_t v_allowLevelAssignments_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1398_, v_allowLevelAssignments_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1406_, lean_object* v_k_1407_, lean_object* v_allowLevelAssignments_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1414_; lean_object* v_res_1415_; 
v_allowLevelAssignments_boxed_1414_ = lean_unbox(v_allowLevelAssignments_1408_);
v_res_1415_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1406_, v_k_1407_, v_allowLevelAssignments_boxed_1414_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1418_, size_t v_sz_1419_, size_t v_i_1420_, lean_object* v_b_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_a_1428_; uint8_t v___x_1432_; 
v___x_1432_ = lean_usize_dec_lt(v_i_1420_, v_sz_1419_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_b_1421_);
return v___x_1433_;
}
else
{
lean_object* v_snd_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1596_; 
v_snd_1434_ = lean_ctor_get(v_b_1421_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_b_1421_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v_b_1421_, 0);
lean_dec(v_unused_1597_);
v___x_1436_ = v_b_1421_;
v_isShared_1437_ = v_isSharedCheck_1596_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_snd_1434_);
lean_dec(v_b_1421_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1596_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_array_1438_; lean_object* v_start_1439_; lean_object* v_stop_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_array_1438_ = lean_ctor_get(v_snd_1434_, 0);
v_start_1439_ = lean_ctor_get(v_snd_1434_, 1);
v_stop_1440_ = lean_ctor_get(v_snd_1434_, 2);
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_nat_dec_lt(v_start_1439_, v_stop_1440_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1444_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1441_);
v___x_1444_ = v___x_1436_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_snd_1434_);
v___x_1444_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
else
{
lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1592_; 
lean_inc(v_stop_1440_);
lean_inc(v_start_1439_);
lean_inc_ref(v_array_1438_);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_snd_1434_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1593_ = lean_ctor_get(v_snd_1434_, 2);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_snd_1434_, 1);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_snd_1434_, 0);
lean_dec(v_unused_1595_);
v___x_1448_ = v_snd_1434_;
v_isShared_1449_ = v_isSharedCheck_1592_;
goto v_resetjp_1447_;
}
else
{
lean_dec(v_snd_1434_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1592_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1450_ = lean_array_fget(v_array_1438_, v_start_1439_);
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = lean_nat_add(v_start_1439_, v___x_1451_);
lean_dec(v_start_1439_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v___x_1452_);
v___x_1454_ = v___x_1448_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_array_1438_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_stop_1440_);
v___x_1454_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
uint8_t v___x_1455_; 
v___x_1455_ = lean_unbox(v___x_1450_);
lean_dec(v___x_1450_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1457_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1454_);
lean_ctor_set(v___x_1436_, 0, v___x_1441_);
v___x_1457_ = v___x_1436_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1454_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
v_a_1428_ = v___x_1457_;
goto v___jp_1427_;
}
}
else
{
lean_object* v_a_1459_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___x_1531_; 
v_a_1459_ = lean_array_uget_borrowed(v_as_1418_, v_i_1420_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
lean_inc(v___y_1423_);
lean_inc_ref(v___y_1422_);
lean_inc(v_a_1459_);
v___x_1531_ = lean_infer_type(v_a_1459_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = l_Lean_Meta_matchEq_x3f(v_a_1532_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
if (lean_obj_tag(v_a_1534_) == 1)
{
lean_object* v_val_1535_; lean_object* v_snd_1536_; lean_object* v_fst_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1573_; 
v_val_1535_ = lean_ctor_get(v_a_1534_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v_a_1534_, 1);
v_snd_1536_ = lean_ctor_get(v_val_1535_, 1);
lean_inc(v_snd_1536_);
lean_dec(v_val_1535_);
v_fst_1537_ = lean_ctor_get(v_snd_1536_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_snd_1536_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v_snd_1536_, 1);
lean_dec(v_unused_1574_);
v___x_1539_ = v_snd_1536_;
v_isShared_1540_ = v_isSharedCheck_1573_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_fst_1537_);
lean_dec(v_snd_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1573_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Meta_mkEqRefl(v_fst_1537_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
lean_inc(v_a_1459_);
v___x_1543_ = l_Lean_Meta_isExprDefEq(v_a_1459_, v_a_1542_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1556_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1556_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1556_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_unbox(v_a_1544_);
lean_dec(v_a_1544_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_del_object(v___x_1436_);
v___x_1549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 1, v___x_1454_);
lean_ctor_set(v___x_1539_, 0, v___x_1549_);
v___x_1551_ = v___x_1539_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1454_);
v___x_1551_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1553_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1551_);
v___x_1553_ = v___x_1546_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
else
{
lean_del_object(v___x_1546_);
lean_del_object(v___x_1539_);
v___y_1461_ = v___y_1422_;
v___y_1462_ = v___y_1423_;
v___y_1463_ = v___y_1424_;
v___y_1464_ = v___y_1425_;
goto v___jp_1460_;
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_del_object(v___x_1539_);
lean_dec_ref(v___x_1454_);
lean_del_object(v___x_1436_);
v_a_1557_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1543_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1543_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_del_object(v___x_1539_);
lean_dec_ref(v___x_1454_);
lean_del_object(v___x_1436_);
v_a_1565_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1541_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1541_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
else
{
lean_dec(v_a_1534_);
v___y_1461_ = v___y_1422_;
v___y_1462_ = v___y_1423_;
v___y_1463_ = v___y_1424_;
v___y_1464_ = v___y_1425_;
goto v___jp_1460_;
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v___x_1454_);
lean_del_object(v___x_1436_);
v_a_1575_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1533_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1533_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref(v___x_1454_);
lean_del_object(v___x_1436_);
v_a_1583_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1531_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1531_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
v___jp_1460_:
{
lean_object* v___x_1465_; 
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
lean_inc(v_a_1459_);
v___x_1465_ = lean_infer_type(v_a_1459_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1467_ = l_Lean_Meta_matchHEq_x3f(v_a_1466_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1467_, 1);
if (lean_obj_tag(v_a_1468_) == 1)
{
lean_object* v_val_1469_; lean_object* v_snd_1470_; lean_object* v_fst_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1510_; 
lean_del_object(v___x_1436_);
v_val_1469_ = lean_ctor_get(v_a_1468_, 0);
lean_inc(v_val_1469_);
lean_dec_ref_known(v_a_1468_, 1);
v_snd_1470_ = lean_ctor_get(v_val_1469_, 1);
lean_inc(v_snd_1470_);
lean_dec(v_val_1469_);
v_fst_1471_ = lean_ctor_get(v_snd_1470_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_snd_1470_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_snd_1470_, 1);
lean_dec(v_unused_1511_);
v___x_1473_ = v_snd_1470_;
v_isShared_1474_ = v_isSharedCheck_1510_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_fst_1471_);
lean_dec(v_snd_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1510_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Meta_mkHEqRefl(v_fst_1471_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
lean_inc(v_a_1459_);
v___x_1477_ = l_Lean_Meta_isExprDefEq(v_a_1459_, v_a_1476_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1493_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1493_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1493_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
uint8_t v___x_1482_; 
v___x_1482_ = lean_unbox(v_a_1478_);
lean_dec(v_a_1478_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1454_);
lean_ctor_set(v___x_1473_, 0, v___x_1483_);
v___x_1485_ = v___x_1473_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v___x_1454_);
v___x_1485_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1487_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1485_);
v___x_1487_ = v___x_1480_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v___x_1491_; 
lean_del_object(v___x_1480_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1454_);
lean_ctor_set(v___x_1473_, 0, v___x_1441_);
v___x_1491_ = v___x_1473_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1454_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
v_a_1428_ = v___x_1491_;
goto v___jp_1427_;
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_del_object(v___x_1473_);
lean_dec_ref(v___x_1454_);
v_a_1494_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1477_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1477_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_del_object(v___x_1473_);
lean_dec_ref(v___x_1454_);
v_a_1502_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1475_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1475_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v___x_1513_; 
lean_dec(v_a_1468_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1454_);
lean_ctor_set(v___x_1436_, 0, v___x_1441_);
v___x_1513_ = v___x_1436_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1454_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
v_a_1428_ = v___x_1513_;
goto v___jp_1427_;
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v___x_1454_);
lean_del_object(v___x_1436_);
v_a_1515_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1467_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1467_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec_ref(v___x_1454_);
lean_del_object(v___x_1436_);
v_a_1523_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1465_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1465_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
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
v___jp_1427_:
{
size_t v___x_1429_; size_t v___x_1430_; 
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_add(v_i_1420_, v___x_1429_);
v_i_1420_ = v___x_1430_;
v_b_1421_ = v_a_1428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1598_, lean_object* v_sz_1599_, lean_object* v_i_1600_, lean_object* v_b_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
size_t v_sz_boxed_1607_; size_t v_i_boxed_1608_; lean_object* v_res_1609_; 
v_sz_boxed_1607_ = lean_unbox_usize(v_sz_1599_);
lean_dec(v_sz_1599_);
v_i_boxed_1608_ = lean_unbox_usize(v_i_1600_);
lean_dec(v_i_1600_);
v_res_1609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1598_, v_sz_boxed_1607_, v_i_boxed_1608_, v_b_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec_ref(v_as_1598_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1610_, uint8_t v___x_1611_, lean_object* v_localDecl_1612_, lean_object* v_mvarId_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
lean_inc_ref(v___x_1610_);
v___x_1619_ = l_Lean_Meta_forallMetaTelescope(v___x_1610_, v___x_1611_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v_fst_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1710_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v_fst_1621_ = lean_ctor_get(v_a_1620_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_a_1620_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v_a_1620_, 1);
lean_dec(v_unused_1711_);
v___x_1623_ = v_a_1620_;
v_isShared_1624_ = v_isSharedCheck_1710_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_fst_1621_);
lean_dec(v_a_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1710_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1625_ = l_Lean_Meta_mkGenDiseqMask(v___x_1610_);
lean_dec_ref(v___x_1610_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = lean_array_get_size(v___x_1625_);
v___x_1628_ = l_Array_toSubarray___redArg(v___x_1625_, v___x_1626_, v___x_1627_);
v___x_1629_ = lean_box(0);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 1, v___x_1628_);
lean_ctor_set(v___x_1623_, 0, v___x_1629_);
v___x_1631_ = v___x_1623_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1628_);
v___x_1631_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
size_t v_sz_1632_; size_t v___x_1633_; lean_object* v___x_1634_; 
v_sz_1632_ = lean_array_size(v_fst_1621_);
v___x_1633_ = ((size_t)0ULL);
v___x_1634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1621_, v_sz_1632_, v___x_1633_, v___x_1631_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1700_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1700_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1700_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_fst_1639_; 
v_fst_1639_ = lean_ctor_get(v_a_1635_, 0);
lean_inc(v_fst_1639_);
lean_dec(v_a_1635_);
if (lean_obj_tag(v_fst_1639_) == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1695_; 
lean_del_object(v___x_1637_);
v___x_1640_ = l_Lean_LocalDecl_toExpr(v_localDecl_1612_);
v___x_1641_ = l_Lean_mkAppN(v___x_1640_, v_fst_1621_);
lean_dec(v_fst_1621_);
v___x_1642_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1641_, v___y_1615_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1695_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1695_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; 
lean_inc(v_a_1643_);
v___x_1647_ = l_Lean_Meta_hasAssignableMVar(v_a_1643_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1686_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1686_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1686_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_unbox(v_a_1648_);
lean_dec(v_a_1648_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_del_object(v___x_1650_);
v___x_1653_ = l_Lean_MVarId_getType(v_mvarId_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1655_ = l_Lean_Meta_mkFalseElim(v_a_1654_, v_a_1643_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1666_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1666_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1666_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 1);
lean_ctor_set(v___x_1645_, 0, v_a_1656_);
v___x_1661_ = v___x_1645_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1661_);
v___x_1663_ = v___x_1658_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_del_object(v___x_1645_);
v_a_1667_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1655_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1655_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_del_object(v___x_1645_);
lean_dec(v_a_1643_);
v_a_1675_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1653_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1653_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
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
lean_object* v___x_1684_; 
lean_del_object(v___x_1645_);
lean_dec(v_a_1643_);
lean_dec(v_mvarId_1613_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1629_);
v___x_1684_ = v___x_1650_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1629_);
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
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_del_object(v___x_1645_);
lean_dec(v_a_1643_);
lean_dec(v_mvarId_1613_);
v_a_1687_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1647_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1647_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
else
{
lean_object* v_val_1696_; lean_object* v___x_1698_; 
lean_dec(v_fst_1621_);
lean_dec(v_mvarId_1613_);
lean_dec_ref(v_localDecl_1612_);
v_val_1696_ = lean_ctor_get(v_fst_1639_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v_fst_1639_, 1);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v_val_1696_);
v___x_1698_ = v___x_1637_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_val_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_fst_1621_);
lean_dec(v_mvarId_1613_);
lean_dec_ref(v_localDecl_1612_);
v_a_1701_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1634_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1634_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_mvarId_1613_);
lean_dec_ref(v_localDecl_1612_);
lean_dec_ref(v___x_1610_);
v_a_1712_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1619_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1619_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1720_, lean_object* v___x_1721_, lean_object* v_localDecl_1722_, lean_object* v_mvarId_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v___x_6078__boxed_1729_; lean_object* v_res_1730_; 
v___x_6078__boxed_1729_ = lean_unbox(v___x_1721_);
v_res_1730_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1720_, v___x_6078__boxed_1729_, v_localDecl_1722_, v_mvarId_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1730_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1735_ = lean_unsigned_to_nat(2u);
v___x_1736_ = lean_unsigned_to_nat(120u);
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1739_ = l_mkPanicMessageWithDecl(v___x_1738_, v___x_1737_, v___x_1736_, v___x_1735_, v___x_1734_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1740_, lean_object* v_localDecl_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = l_Lean_LocalDecl_type(v_localDecl_1741_);
lean_inc_ref(v___x_1747_);
v___x_1748_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec_ref(v___x_1747_);
lean_dec_ref(v_localDecl_1741_);
lean_dec(v_mvarId_1740_);
v___x_1749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1750_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1749_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
return v___x_1750_;
}
else
{
uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___f_1753_; uint8_t v___x_1754_; lean_object* v___x_1755_; 
v___x_1751_ = 0;
v___x_1752_ = lean_box(v___x_1751_);
lean_inc(v_mvarId_1740_);
v___f_1753_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1753_, 0, v___x_1747_);
lean_closure_set(v___f_1753_, 1, v___x_1752_);
lean_closure_set(v___f_1753_, 2, v_localDecl_1741_);
lean_closure_set(v___f_1753_, 3, v_mvarId_1740_);
v___x_1754_ = 0;
v___x_1755_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1753_, v___x_1754_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1775_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1775_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1775_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
if (lean_obj_tag(v_a_1756_) == 1)
{
lean_object* v_val_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1769_; 
lean_del_object(v___x_1758_);
v_val_1760_ = lean_ctor_get(v_a_1756_, 0);
lean_inc(v_val_1760_);
lean_dec_ref_known(v_a_1756_, 1);
v___x_1761_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1740_, v_val_1760_, v_a_1743_);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1761_, 0);
lean_dec(v_unused_1770_);
v___x_1763_ = v___x_1761_;
v_isShared_1764_ = v_isSharedCheck_1769_;
goto v_resetjp_1762_;
}
else
{
lean_dec(v___x_1761_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1769_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = lean_box(v___x_1748_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1765_);
v___x_1767_ = v___x_1763_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
lean_dec(v_a_1756_);
lean_dec(v_mvarId_1740_);
v___x_1771_ = lean_box(v___x_1754_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1771_);
v___x_1773_ = v___x_1758_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_mvarId_1740_);
v_a_1776_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1755_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1755_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1784_, lean_object* v_localDecl_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1784_, v_localDecl_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
return v_res_1791_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = lean_box(0);
v___x_1804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1805_ = l_Lean_mkConst(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1806_; lean_object* v_dummy_1807_; 
v___x_1806_ = lean_box(0);
v_dummy_1807_ = l_Lean_Expr_sort___override(v___x_1806_);
return v_dummy_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1808_, lean_object* v_mvarId_1809_, lean_object* v_as_1810_, size_t v_sz_1811_, size_t v_i_1812_, lean_object* v_b_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
uint8_t v___x_1819_; 
v___x_1819_ = lean_usize_dec_lt(v_i_1812_, v_sz_1811_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; 
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v_b_1813_);
return v___x_1820_;
}
else
{
lean_object* v_snd_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_2471_; 
v_snd_1821_ = lean_ctor_get(v_b_1813_, 1);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_b_1813_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; 
v_unused_2472_ = lean_ctor_get(v_b_1813_, 0);
lean_dec(v_unused_2472_);
v___x_1823_ = v_b_1813_;
v_isShared_1824_ = v_isSharedCheck_2471_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_snd_1821_);
lean_dec(v_b_1813_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_2471_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_a_1826_; lean_object* v___x_1832_; lean_object* v_a_1834_; lean_object* v_a_1839_; 
v___x_1832_ = lean_box(0);
v_a_1839_ = lean_array_uget(v_as_1810_, v_i_1812_);
if (lean_obj_tag(v_a_1839_) == 0)
{
lean_del_object(v___x_1823_);
v_a_1834_ = v_snd_1821_;
goto v___jp_1833_;
}
else
{
lean_object* v_val_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_2470_; 
v_val_1840_ = lean_ctor_get(v_a_1839_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_a_1839_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_1842_ = v_a_1839_;
v_isShared_1843_ = v_isSharedCheck_2470_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_val_1840_);
lean_dec(v_a_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_2470_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___x_1885_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; uint8_t v___y_1912_; uint8_t v___x_1913_; lean_object* v___y_1915_; uint8_t v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1921_; uint8_t v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; uint8_t v___y_1926_; uint8_t v___y_1928_; uint8_t v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; uint8_t v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; uint8_t v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; uint8_t v___y_1942_; 
v___x_1844_ = lean_box(0);
v___x_1885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1913_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1840_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1957_; uint8_t v___y_1959_; uint8_t v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1968_; lean_object* v___y_1969_; uint8_t v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; uint8_t v___y_1973_; lean_object* v___y_1974_; uint8_t v___y_1975_; lean_object* v___y_1978_; uint8_t v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; uint8_t v___y_1982_; lean_object* v___y_1983_; lean_object* v_a_1984_; lean_object* v___y_1988_; lean_object* v___y_1989_; uint8_t v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_2032_; uint8_t v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; uint8_t v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2061_; uint8_t v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; uint8_t v___y_2065_; lean_object* v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2069_; uint8_t v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; uint8_t v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; uint8_t v___y_2076_; lean_object* v___y_2079_; uint8_t v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; uint8_t v___y_2083_; lean_object* v___y_2084_; uint8_t v___y_2085_; lean_object* v___y_2098_; uint8_t v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; uint8_t v___y_2102_; lean_object* v___y_2103_; uint8_t v___y_2104_; uint8_t v___y_2106_; uint8_t v_isHEq_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; uint8_t v___y_2121_; uint8_t v_isEq_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___x_2407_; 
v___x_1957_ = l_Lean_LocalDecl_type(v_val_1840_);
lean_inc_ref(v___x_1957_);
v___x_2407_ = l_Lean_Meta_matchNot_x3f(v___x_1957_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
if (lean_obj_tag(v_a_2408_) == 1)
{
lean_object* v_val_2409_; lean_object* v___x_2410_; 
v_val_2409_ = lean_ctor_get(v_a_2408_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v_a_2408_, 1);
v___x_2410_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2409_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
if (lean_obj_tag(v_a_2411_) == 1)
{
lean_object* v_val_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec_ref(v_config_1808_);
v_val_2412_ = lean_ctor_get(v_a_2411_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_a_2411_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2414_ = v_a_2411_;
v_isShared_2415_ = v_isSharedCheck_2453_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_val_2412_);
lean_dec(v_a_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2453_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; 
lean_inc(v_mvarId_1809_);
v___x_2416_ = l_Lean_MVarId_getType(v_mvarId_1809_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v___x_2418_ = l_Lean_LocalDecl_toExpr(v_val_1840_);
v___x_2419_ = l_Lean_mkFVar(v_val_2412_);
v___x_2420_ = l_Lean_Expr_app___override(v___x_2418_, v___x_2419_);
v___x_2421_ = l_Lean_Meta_mkFalseElim(v_a_2417_, v___x_2420_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2423_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2423_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1809_, v_a_2422_, v___y_1815_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
lean_dec_ref_known(v___x_2423_, 1);
v___x_2424_ = lean_box(v___x_1819_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2424_);
v___x_2426_ = v___x_2414_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v___x_1844_);
v_a_1826_ = v___x_2427_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_del_object(v___x_2414_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
v_a_2429_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2423_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2423_);
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
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_del_object(v___x_2414_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2437_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2421_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2421_);
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
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_del_object(v___x_2414_);
lean_dec(v_val_2412_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2445_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2416_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2416_);
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
}
}
else
{
lean_dec(v_a_2411_);
v___y_2273_ = v___y_1814_;
v___y_2274_ = v___y_1815_;
v___y_2275_ = v___y_1816_;
v___y_2276_ = v___y_1817_;
goto v___jp_2272_;
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2454_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2410_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2410_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_dec(v_a_2408_);
v___y_2273_ = v___y_1814_;
v___y_2274_ = v___y_1815_;
v___y_2275_ = v___y_1816_;
v___y_2276_ = v___y_1817_;
goto v___jp_2272_;
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2462_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2407_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2407_);
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
v___jp_1958_:
{
uint8_t v_genDiseq_1965_; 
v_genDiseq_1965_ = lean_ctor_get_uint8(v_config_1808_, sizeof(void*)*1 + 2);
if (v_genDiseq_1965_ == 0)
{
lean_dec_ref(v___x_1957_);
v___y_1936_ = v___y_1959_;
v___y_1937_ = v___y_1961_;
v___y_1938_ = v___y_1962_;
v___y_1939_ = v___y_1960_;
v___y_1940_ = v___y_1964_;
v___y_1941_ = v___y_1963_;
v___y_1942_ = v___x_1913_;
goto v___jp_1935_;
}
else
{
uint8_t v___x_1966_; 
v___x_1966_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1957_);
v___y_1936_ = v___y_1959_;
v___y_1937_ = v___y_1961_;
v___y_1938_ = v___y_1962_;
v___y_1939_ = v___y_1960_;
v___y_1940_ = v___y_1964_;
v___y_1941_ = v___y_1963_;
v___y_1942_ = v___x_1966_;
goto v___jp_1935_;
}
}
v___jp_1967_:
{
if (v___y_1975_ == 0)
{
lean_dec_ref(v___y_1969_);
v___y_1959_ = v___y_1970_;
v___y_1960_ = v___y_1973_;
v___y_1961_ = v___y_1972_;
v___y_1962_ = v___y_1971_;
v___y_1963_ = v___y_1974_;
v___y_1964_ = v___y_1968_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_1976_; 
lean_dec_ref(v___x_1957_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___y_1969_);
return v___x_1976_;
}
}
v___jp_1977_:
{
uint8_t v___x_1985_; 
v___x_1985_ = l_Lean_Exception_isInterrupt(v_a_1984_);
if (v___x_1985_ == 0)
{
uint8_t v___x_1986_; 
lean_inc_ref(v_a_1984_);
v___x_1986_ = l_Lean_Exception_isRuntime(v_a_1984_);
v___y_1968_ = v___y_1978_;
v___y_1969_ = v_a_1984_;
v___y_1970_ = v___y_1979_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1983_;
v___y_1975_ = v___x_1986_;
goto v___jp_1967_;
}
else
{
v___y_1968_ = v___y_1978_;
v___y_1969_ = v_a_1984_;
v___y_1970_ = v___y_1979_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1983_;
v___y_1975_ = v___x_1985_;
goto v___jp_1967_;
}
}
v___jp_1987_:
{
if (lean_obj_tag(v___y_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_a_1996_ = lean_ctor_get(v___y_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___y_1995_, 1);
v___x_1997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_1998_ = l_Lean_Expr_isConstOf(v_a_1996_, v___x_1997_);
lean_dec(v_a_1996_);
if (v___x_1998_ == 0)
{
lean_dec_ref(v___y_1989_);
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1993_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1991_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1988_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_1999_; 
lean_inc_ref(v___y_1989_);
v___x_1999_ = l_Lean_Meta_mkEqRefl(v___y_1989_, v___y_1992_, v___y_1991_, v___y_1994_, v___y_1988_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; lean_object* v_dummy_2002_; lean_object* v_nargs_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2002_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2003_ = l_Lean_Expr_getAppNumArgs(v___y_1989_);
lean_inc(v_nargs_2003_);
v___x_2004_ = lean_mk_array(v_nargs_2003_, v_dummy_2002_);
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = lean_nat_sub(v_nargs_2003_, v___x_2005_);
lean_dec(v_nargs_2003_);
v___x_2007_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1989_, v___x_2004_, v___x_2006_);
v___x_2008_ = lean_array_push(v___x_2007_, v_a_2000_);
v___x_2009_ = l_Lean_mkAppN(v___x_2001_, v___x_2008_);
lean_dec_ref(v___x_2008_);
lean_inc(v_mvarId_1809_);
v___x_2010_ = l_Lean_MVarId_getType(v_mvarId_1809_, v___y_1992_, v___y_1991_, v___y_1994_, v___y_1988_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
lean_inc(v_val_1840_);
v___x_2012_ = l_Lean_LocalDecl_toExpr(v_val_1840_);
v___x_2013_ = l_Lean_Meta_mkAbsurd(v_a_2011_, v___x_2012_, v___x_2009_, v___y_1992_, v___y_1991_, v___y_1994_, v___y_1988_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
lean_inc(v_mvarId_1809_);
v___x_2015_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1809_, v_a_2014_, v___y_1991_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v___x_1957_);
lean_dec(v_val_1840_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v___x_2015_, 0);
lean_dec(v_unused_2025_);
v___x_2017_ = v___x_2015_;
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v___x_2015_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_box(v___x_1819_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 1);
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set(v___x_2022_, 1, v___x_1844_);
v_a_1826_ = v___x_2022_;
goto v___jp_1825_;
}
}
}
else
{
lean_object* v_a_2026_; 
v_a_2026_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2015_, 1);
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v_a_1984_ = v_a_2026_;
goto v___jp_1977_;
}
}
else
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2013_, 1);
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v_a_1984_ = v_a_2027_;
goto v___jp_1977_;
}
}
else
{
lean_object* v_a_2028_; 
lean_dec_ref(v___x_2009_);
v_a_2028_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2010_, 1);
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v_a_1984_ = v_a_2028_;
goto v___jp_1977_;
}
}
else
{
lean_object* v_a_2029_; 
lean_dec_ref(v___y_1989_);
v_a_2029_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_1999_, 1);
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v_a_1984_ = v_a_2029_;
goto v___jp_1977_;
}
}
}
else
{
lean_object* v_a_2030_; 
lean_dec_ref(v___y_1989_);
v_a_2030_ = lean_ctor_get(v___y_1995_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___y_1995_, 1);
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v_a_1984_ = v_a_2030_;
goto v___jp_1977_;
}
}
v___jp_2031_:
{
lean_object* v___x_2038_; 
lean_inc_ref(v___x_1957_);
v___x_2038_ = l_Lean_Meta_mkDecide(v___x_1957_, v___y_2035_, v___y_2034_, v___y_2037_, v___y_2032_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; uint8_t v_transparency_2041_; uint8_t v___x_2042_; uint8_t v___x_2043_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = l_Lean_Meta_Context_config(v___y_2035_);
v_transparency_2041_ = lean_ctor_get_uint8(v___x_2040_, 9);
lean_dec_ref(v___x_2040_);
v___x_2042_ = 1;
v___x_2043_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v_keyedConfig_2044_; uint8_t v_trackZetaDelta_2045_; lean_object* v_zetaDeltaSet_2046_; lean_object* v_lctx_2047_; lean_object* v_localInstances_2048_; lean_object* v_defEqCtx_x3f_2049_; lean_object* v_synthPendingDepth_2050_; lean_object* v_customCanUnfoldPredicate_x3f_2051_; uint8_t v_univApprox_2052_; uint8_t v_inTypeClassResolution_2053_; uint8_t v_cacheInferType_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_keyedConfig_2044_ = lean_ctor_get(v___y_2035_, 0);
v_trackZetaDelta_2045_ = lean_ctor_get_uint8(v___y_2035_, sizeof(void*)*7);
v_zetaDeltaSet_2046_ = lean_ctor_get(v___y_2035_, 1);
v_lctx_2047_ = lean_ctor_get(v___y_2035_, 2);
v_localInstances_2048_ = lean_ctor_get(v___y_2035_, 3);
v_defEqCtx_x3f_2049_ = lean_ctor_get(v___y_2035_, 4);
v_synthPendingDepth_2050_ = lean_ctor_get(v___y_2035_, 5);
v_customCanUnfoldPredicate_x3f_2051_ = lean_ctor_get(v___y_2035_, 6);
v_univApprox_2052_ = lean_ctor_get_uint8(v___y_2035_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2053_ = lean_ctor_get_uint8(v___y_2035_, sizeof(void*)*7 + 2);
v_cacheInferType_2054_ = lean_ctor_get_uint8(v___y_2035_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2044_);
v___x_2055_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2042_, v_keyedConfig_2044_);
lean_inc(v_customCanUnfoldPredicate_x3f_2051_);
lean_inc(v_synthPendingDepth_2050_);
lean_inc(v_defEqCtx_x3f_2049_);
lean_inc_ref(v_localInstances_2048_);
lean_inc_ref(v_lctx_2047_);
lean_inc(v_zetaDeltaSet_2046_);
v___x_2056_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v_zetaDeltaSet_2046_);
lean_ctor_set(v___x_2056_, 2, v_lctx_2047_);
lean_ctor_set(v___x_2056_, 3, v_localInstances_2048_);
lean_ctor_set(v___x_2056_, 4, v_defEqCtx_x3f_2049_);
lean_ctor_set(v___x_2056_, 5, v_synthPendingDepth_2050_);
lean_ctor_set(v___x_2056_, 6, v_customCanUnfoldPredicate_x3f_2051_);
lean_ctor_set_uint8(v___x_2056_, sizeof(void*)*7, v_trackZetaDelta_2045_);
lean_ctor_set_uint8(v___x_2056_, sizeof(void*)*7 + 1, v_univApprox_2052_);
lean_ctor_set_uint8(v___x_2056_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2053_);
lean_ctor_set_uint8(v___x_2056_, sizeof(void*)*7 + 3, v_cacheInferType_2054_);
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2034_);
lean_inc(v_a_2039_);
v___x_2057_ = lean_whnf(v_a_2039_, v___x_2056_, v___y_2034_, v___y_2037_, v___y_2032_);
v___y_1988_ = v___y_2032_;
v___y_1989_ = v_a_2039_;
v___y_1990_ = v___y_2033_;
v___y_1991_ = v___y_2034_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___y_2036_;
v___y_1994_ = v___y_2037_;
v___y_1995_ = v___x_2057_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_2058_; 
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2035_);
lean_inc(v_a_2039_);
v___x_2058_ = lean_whnf(v_a_2039_, v___y_2035_, v___y_2034_, v___y_2037_, v___y_2032_);
v___y_1988_ = v___y_2032_;
v___y_1989_ = v_a_2039_;
v___y_1990_ = v___y_2033_;
v___y_1991_ = v___y_2034_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___y_2036_;
v___y_1994_ = v___y_2037_;
v___y_1995_ = v___x_2058_;
goto v___jp_1987_;
}
}
else
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2038_, 1);
v___y_1978_ = v___y_2032_;
v___y_1979_ = v___y_2033_;
v___y_1980_ = v___y_2034_;
v___y_1981_ = v___y_2035_;
v___y_1982_ = v___y_2036_;
v___y_1983_ = v___y_2037_;
v_a_1984_ = v_a_2059_;
goto v___jp_1977_;
}
}
v___jp_2060_:
{
if (v___y_2067_ == 0)
{
v___y_1959_ = v___y_2062_;
v___y_1960_ = v___y_2065_;
v___y_1961_ = v___y_2064_;
v___y_1962_ = v___y_2063_;
v___y_1963_ = v___y_2066_;
v___y_1964_ = v___y_2061_;
goto v___jp_1958_;
}
else
{
v___y_2032_ = v___y_2061_;
v___y_2033_ = v___y_2062_;
v___y_2034_ = v___y_2063_;
v___y_2035_ = v___y_2064_;
v___y_2036_ = v___y_2065_;
v___y_2037_ = v___y_2066_;
goto v___jp_2031_;
}
}
v___jp_2068_:
{
if (v___y_2076_ == 0)
{
lean_dec_ref(v___y_2074_);
v___y_2061_ = v___y_2069_;
v___y_2062_ = v___y_2070_;
v___y_2063_ = v___y_2071_;
v___y_2064_ = v___y_2072_;
v___y_2065_ = v___y_2073_;
v___y_2066_ = v___y_2075_;
v___y_2067_ = v___x_1913_;
goto v___jp_2060_;
}
else
{
uint8_t v___x_2077_; 
v___x_2077_ = l_Lean_Expr_hasFVar(v___y_2074_);
lean_dec_ref(v___y_2074_);
if (v___x_2077_ == 0)
{
v___y_2032_ = v___y_2069_;
v___y_2033_ = v___y_2070_;
v___y_2034_ = v___y_2071_;
v___y_2035_ = v___y_2072_;
v___y_2036_ = v___y_2073_;
v___y_2037_ = v___y_2075_;
goto v___jp_2031_;
}
else
{
v___y_2061_ = v___y_2069_;
v___y_2062_ = v___y_2070_;
v___y_2063_ = v___y_2071_;
v___y_2064_ = v___y_2072_;
v___y_2065_ = v___y_2073_;
v___y_2066_ = v___y_2075_;
v___y_2067_ = v___x_1913_;
goto v___jp_2060_;
}
}
}
v___jp_2078_:
{
lean_object* v___x_2086_; 
lean_inc_ref(v___x_1957_);
v___x_2086_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1957_, v___y_2081_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; uint8_t v___x_2088_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = l_Lean_Expr_hasMVar(v_a_2087_);
if (v___x_2088_ == 0)
{
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v___y_2082_;
v___y_2073_ = v___y_2083_;
v___y_2074_ = v_a_2087_;
v___y_2075_ = v___y_2084_;
v___y_2076_ = v___y_2085_;
goto v___jp_2068_;
}
else
{
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v___y_2082_;
v___y_2073_ = v___y_2083_;
v___y_2074_ = v_a_2087_;
v___y_2075_ = v___y_2084_;
v___y_2076_ = v___x_1913_;
goto v___jp_2068_;
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v___x_1957_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2089_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2086_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2086_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
v___jp_2097_:
{
if (v___y_2104_ == 0)
{
v___y_1959_ = v___y_2099_;
v___y_1960_ = v___y_2102_;
v___y_1961_ = v___y_2101_;
v___y_1962_ = v___y_2100_;
v___y_1963_ = v___y_2103_;
v___y_1964_ = v___y_2098_;
goto v___jp_1958_;
}
else
{
v___y_2079_ = v___y_2098_;
v___y_2080_ = v___y_2099_;
v___y_2081_ = v___y_2100_;
v___y_2082_ = v___y_2101_;
v___y_2083_ = v___y_2102_;
v___y_2084_ = v___y_2103_;
v___y_2085_ = v___y_2104_;
goto v___jp_2078_;
}
}
v___jp_2105_:
{
uint8_t v_useDecide_2112_; 
v_useDecide_2112_ = lean_ctor_get_uint8(v_config_1808_, sizeof(void*)*1);
if (v_useDecide_2112_ == 0)
{
v___y_2098_ = v___y_2111_;
v___y_2099_ = v_isHEq_2107_;
v___y_2100_ = v___y_2109_;
v___y_2101_ = v___y_2108_;
v___y_2102_ = v___y_2106_;
v___y_2103_ = v___y_2110_;
v___y_2104_ = v___x_1913_;
goto v___jp_2097_;
}
else
{
uint8_t v___x_2113_; 
v___x_2113_ = l_Lean_Expr_hasFVar(v___x_1957_);
if (v___x_2113_ == 0)
{
v___y_2079_ = v___y_2111_;
v___y_2080_ = v_isHEq_2107_;
v___y_2081_ = v___y_2109_;
v___y_2082_ = v___y_2108_;
v___y_2083_ = v___y_2106_;
v___y_2084_ = v___y_2110_;
v___y_2085_ = v_useDecide_2112_;
goto v___jp_2078_;
}
else
{
v___y_2098_ = v___y_2111_;
v___y_2099_ = v_isHEq_2107_;
v___y_2100_ = v___y_2109_;
v___y_2101_ = v___y_2108_;
v___y_2102_ = v___y_2106_;
v___y_2103_ = v___y_2110_;
v___y_2104_ = v___x_1913_;
goto v___jp_2097_;
}
}
}
v___jp_2114_:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Meta_isExprDefEq(v___y_2117_, v___y_2118_, v___y_2120_, v___y_2119_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; uint8_t v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = lean_unbox(v_a_2123_);
lean_dec(v_a_2123_);
if (v___x_2124_ == 0)
{
v___y_2106_ = v___y_2121_;
v_isHEq_2107_ = v___x_1819_;
v___y_2108_ = v___y_2120_;
v___y_2109_ = v___y_2119_;
v___y_2110_ = v___y_2115_;
v___y_2111_ = v___y_2116_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2125_; 
lean_dec_ref(v___x_1957_);
lean_dec_ref(v_config_1808_);
lean_inc(v_mvarId_1809_);
v___x_2125_ = l_Lean_MVarId_getType(v_mvarId_1809_, v___y_2120_, v___y_2119_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = l_Lean_LocalDecl_toExpr(v_val_1840_);
v___x_2128_ = l_Lean_Meta_mkEqOfHEq(v___x_2127_, v___x_1819_, v___y_2120_, v___y_2119_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = l_Lean_Meta_mkNoConfusion(v_a_2126_, v_a_2129_, v___y_2120_, v___y_2119_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1809_, v_a_2131_, v___y_2119_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
lean_dec_ref_known(v___x_2132_, 1);
v___x_2133_ = lean_box(v___x_1819_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
lean_ctor_set(v___x_2135_, 1, v___x_1844_);
v_a_1826_ = v___x_2135_;
goto v___jp_1825_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
v_a_2136_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2132_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2132_);
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
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2144_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2130_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2130_);
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
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v_a_2126_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2152_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2128_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2128_);
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
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2160_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2125_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2125_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref(v___x_1957_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2168_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2122_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2122_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
v___jp_2176_:
{
lean_object* v___x_2182_; 
lean_inc_ref(v___x_1957_);
v___x_2182_ = l_Lean_Meta_matchHEq_x3f(v___x_1957_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
if (lean_obj_tag(v_a_2183_) == 1)
{
lean_object* v_val_2184_; lean_object* v_snd_2185_; lean_object* v_snd_2186_; lean_object* v_fst_2187_; lean_object* v_fst_2188_; lean_object* v_fst_2189_; lean_object* v_snd_2190_; lean_object* v___x_2191_; 
v_val_2184_ = lean_ctor_get(v_a_2183_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v_a_2183_, 1);
v_snd_2185_ = lean_ctor_get(v_val_2184_, 1);
lean_inc(v_snd_2185_);
v_snd_2186_ = lean_ctor_get(v_snd_2185_, 1);
lean_inc(v_snd_2186_);
v_fst_2187_ = lean_ctor_get(v_val_2184_, 0);
lean_inc(v_fst_2187_);
lean_dec(v_val_2184_);
v_fst_2188_ = lean_ctor_get(v_snd_2185_, 0);
lean_inc(v_fst_2188_);
lean_dec(v_snd_2185_);
v_fst_2189_ = lean_ctor_get(v_snd_2186_, 0);
lean_inc(v_fst_2189_);
v_snd_2190_ = lean_ctor_get(v_snd_2186_, 1);
lean_inc(v_snd_2190_);
lean_dec(v_snd_2186_);
v___x_2191_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2188_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2191_, 1);
if (lean_obj_tag(v_a_2192_) == 1)
{
lean_object* v_val_2193_; lean_object* v___x_2194_; 
v_val_2193_ = lean_ctor_get(v_a_2192_, 0);
lean_inc(v_val_2193_);
lean_dec_ref_known(v_a_2192_, 1);
v___x_2194_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2190_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
if (lean_obj_tag(v_a_2195_) == 1)
{
lean_object* v_toConstantVal_2196_; lean_object* v_val_2197_; lean_object* v_toConstantVal_2198_; lean_object* v_name_2199_; lean_object* v_name_2200_; uint8_t v___x_2201_; 
v_toConstantVal_2196_ = lean_ctor_get(v_val_2193_, 0);
lean_inc_ref(v_toConstantVal_2196_);
lean_dec(v_val_2193_);
v_val_2197_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_val_2197_);
lean_dec_ref_known(v_a_2195_, 1);
v_toConstantVal_2198_ = lean_ctor_get(v_val_2197_, 0);
lean_inc_ref(v_toConstantVal_2198_);
lean_dec(v_val_2197_);
v_name_2199_ = lean_ctor_get(v_toConstantVal_2196_, 0);
lean_inc(v_name_2199_);
lean_dec_ref(v_toConstantVal_2196_);
v_name_2200_ = lean_ctor_get(v_toConstantVal_2198_, 0);
lean_inc(v_name_2200_);
lean_dec_ref(v_toConstantVal_2198_);
v___x_2201_ = lean_name_eq(v_name_2199_, v_name_2200_);
lean_dec(v_name_2200_);
lean_dec(v_name_2199_);
if (v___x_2201_ == 0)
{
v___y_2115_ = v___y_2180_;
v___y_2116_ = v___y_2181_;
v___y_2117_ = v_fst_2187_;
v___y_2118_ = v_fst_2189_;
v___y_2119_ = v___y_2179_;
v___y_2120_ = v___y_2178_;
v___y_2121_ = v_isEq_2177_;
goto v___jp_2114_;
}
else
{
if (v___x_1913_ == 0)
{
lean_dec(v_fst_2189_);
lean_dec(v_fst_2187_);
v___y_2106_ = v_isEq_2177_;
v_isHEq_2107_ = v___x_1819_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
v___y_2111_ = v___y_2181_;
goto v___jp_2105_;
}
else
{
v___y_2115_ = v___y_2180_;
v___y_2116_ = v___y_2181_;
v___y_2117_ = v_fst_2187_;
v___y_2118_ = v_fst_2189_;
v___y_2119_ = v___y_2179_;
v___y_2120_ = v___y_2178_;
v___y_2121_ = v_isEq_2177_;
goto v___jp_2114_;
}
}
}
else
{
lean_dec(v_a_2195_);
lean_dec(v_val_2193_);
lean_dec(v_fst_2189_);
lean_dec(v_fst_2187_);
v___y_2106_ = v_isEq_2177_;
v_isHEq_2107_ = v___x_1819_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
v___y_2111_ = v___y_2181_;
goto v___jp_2105_;
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_val_2193_);
lean_dec(v_fst_2189_);
lean_dec(v_fst_2187_);
lean_dec_ref(v___x_1957_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2202_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2194_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2194_);
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
lean_dec(v_a_2192_);
lean_dec(v_snd_2190_);
lean_dec(v_fst_2189_);
lean_dec(v_fst_2187_);
v___y_2106_ = v_isEq_2177_;
v_isHEq_2107_ = v___x_1819_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
v___y_2111_ = v___y_2181_;
goto v___jp_2105_;
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_snd_2190_);
lean_dec(v_fst_2189_);
lean_dec(v_fst_2187_);
lean_dec_ref(v___x_1957_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2210_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2191_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2191_);
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
else
{
lean_dec(v_a_2183_);
v___y_2106_ = v_isEq_2177_;
v_isHEq_2107_ = v___x_1913_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
v___y_2111_ = v___y_2181_;
goto v___jp_2105_;
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v___x_1957_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2218_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2182_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2182_);
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
v___jp_2226_:
{
lean_object* v___x_2231_; 
lean_inc_ref(v___x_1957_);
v___x_2231_ = l_Lean_Meta_matchEq_x3f(v___x_1957_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
if (lean_obj_tag(v_a_2232_) == 1)
{
lean_object* v_val_2233_; lean_object* v_snd_2234_; lean_object* v_fst_2235_; lean_object* v_snd_2236_; lean_object* v___x_2237_; 
v_val_2233_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_val_2233_);
lean_dec_ref_known(v_a_2232_, 1);
v_snd_2234_ = lean_ctor_get(v_val_2233_, 1);
lean_inc(v_snd_2234_);
lean_dec(v_val_2233_);
v_fst_2235_ = lean_ctor_get(v_snd_2234_, 0);
lean_inc(v_fst_2235_);
v_snd_2236_ = lean_ctor_get(v_snd_2234_, 1);
lean_inc(v_snd_2236_);
lean_dec(v_snd_2234_);
v___x_2237_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2235_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
if (lean_obj_tag(v_a_2238_) == 1)
{
lean_object* v_val_2239_; lean_object* v___x_2240_; 
v_val_2239_ = lean_ctor_get(v_a_2238_, 0);
lean_inc(v_val_2239_);
lean_dec_ref_known(v_a_2238_, 1);
v___x_2240_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2236_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
if (lean_obj_tag(v_a_2241_) == 1)
{
lean_object* v_toConstantVal_2242_; lean_object* v_val_2243_; lean_object* v_toConstantVal_2244_; lean_object* v_name_2245_; lean_object* v_name_2246_; uint8_t v___x_2247_; 
v_toConstantVal_2242_ = lean_ctor_get(v_val_2239_, 0);
lean_inc_ref(v_toConstantVal_2242_);
lean_dec(v_val_2239_);
v_val_2243_ = lean_ctor_get(v_a_2241_, 0);
lean_inc(v_val_2243_);
lean_dec_ref_known(v_a_2241_, 1);
v_toConstantVal_2244_ = lean_ctor_get(v_val_2243_, 0);
lean_inc_ref(v_toConstantVal_2244_);
lean_dec(v_val_2243_);
v_name_2245_ = lean_ctor_get(v_toConstantVal_2242_, 0);
lean_inc(v_name_2245_);
lean_dec_ref(v_toConstantVal_2242_);
v_name_2246_ = lean_ctor_get(v_toConstantVal_2244_, 0);
lean_inc(v_name_2246_);
lean_dec_ref(v_toConstantVal_2244_);
v___x_2247_ = lean_name_eq(v_name_2245_, v_name_2246_);
lean_dec(v_name_2246_);
lean_dec(v_name_2245_);
if (v___x_2247_ == 0)
{
lean_dec_ref(v___x_1957_);
lean_dec_ref(v_config_1808_);
v___y_1846_ = v___y_2230_;
v___y_1847_ = v___y_2229_;
v___y_1848_ = v___y_2228_;
v___y_1849_ = v___y_2227_;
goto v___jp_1845_;
}
else
{
if (v___x_1913_ == 0)
{
lean_del_object(v___x_1842_);
v_isEq_2177_ = v___x_1819_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
v___y_2181_ = v___y_2230_;
goto v___jp_2176_;
}
else
{
lean_dec_ref(v___x_1957_);
lean_dec_ref(v_config_1808_);
v___y_1846_ = v___y_2230_;
v___y_1847_ = v___y_2229_;
v___y_1848_ = v___y_2228_;
v___y_1849_ = v___y_2227_;
goto v___jp_1845_;
}
}
}
else
{
lean_dec(v_a_2241_);
lean_dec(v_val_2239_);
lean_del_object(v___x_1842_);
v_isEq_2177_ = v___x_1819_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
v___y_2181_ = v___y_2230_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_val_2239_);
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2248_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2240_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2240_);
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
else
{
lean_dec(v_a_2238_);
lean_dec(v_snd_2236_);
lean_del_object(v___x_1842_);
v_isEq_2177_ = v___x_1819_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
v___y_2181_ = v___y_2230_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_snd_2236_);
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2256_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2237_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2237_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_dec(v_a_2232_);
lean_del_object(v___x_1842_);
v_isEq_2177_ = v___x_1913_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
v___y_2181_ = v___y_2230_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2264_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2231_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2231_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
v___jp_2272_:
{
lean_object* v___x_2277_; 
lean_inc_ref(v___x_1957_);
v___x_2277_ = l_Lean_refutableHasNotBit_x3f(v___x_1957_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
if (lean_obj_tag(v_a_2278_) == 1)
{
lean_object* v_val_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec_ref(v_config_1808_);
v_val_2279_ = lean_ctor_get(v_a_2278_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_a_2278_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2281_ = v_a_2278_;
v_isShared_2282_ = v_isSharedCheck_2318_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_val_2279_);
lean_dec(v_a_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2318_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; 
lean_inc(v_mvarId_1809_);
v___x_2283_ = l_Lean_MVarId_getType(v_mvarId_1809_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v___x_2285_ = l_Lean_LocalDecl_toExpr(v_val_1840_);
v___x_2286_ = l_Lean_Meta_mkAbsurd(v_a_2284_, v_val_2279_, v___x_2285_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1809_, v_a_2287_, v___y_2274_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
lean_dec_ref_known(v___x_2288_, 1);
v___x_2289_ = lean_box(v___x_1819_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2289_);
v___x_2291_ = v___x_2281_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___x_1844_);
v_a_1826_ = v___x_2292_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_del_object(v___x_2281_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
v_a_2294_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2288_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2288_);
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
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_del_object(v___x_2281_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2302_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2286_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2286_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_del_object(v___x_2281_);
lean_dec(v_val_2279_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2310_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2283_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2283_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
else
{
lean_object* v___x_2319_; 
lean_dec(v_a_2278_);
lean_inc_ref(v___x_1957_);
v___x_2319_ = l_Lean_Meta_matchNe_x3f(v___x_1957_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
if (lean_obj_tag(v_a_2320_) == 1)
{
lean_object* v_val_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2390_; 
v_val_2321_ = lean_ctor_get(v_a_2320_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_a_2320_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2323_ = v_a_2320_;
v_isShared_2324_ = v_isSharedCheck_2390_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_val_2321_);
lean_dec(v_a_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2390_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_snd_2325_; lean_object* v_fst_2326_; lean_object* v_snd_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2389_; 
v_snd_2325_ = lean_ctor_get(v_val_2321_, 1);
lean_inc(v_snd_2325_);
lean_dec(v_val_2321_);
v_fst_2326_ = lean_ctor_get(v_snd_2325_, 0);
v_snd_2327_ = lean_ctor_get(v_snd_2325_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_snd_2325_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2329_ = v_snd_2325_;
v_isShared_2330_ = v_isSharedCheck_2389_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_snd_2327_);
lean_inc(v_fst_2326_);
lean_dec(v_snd_2325_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2389_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; 
lean_inc(v_fst_2326_);
v___x_2331_ = l_Lean_Meta_isExprDefEq(v_fst_2326_, v_snd_2327_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; uint8_t v___x_2333_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = lean_unbox(v_a_2332_);
lean_dec(v_a_2332_);
if (v___x_2333_ == 0)
{
lean_del_object(v___x_2329_);
lean_dec(v_fst_2326_);
lean_del_object(v___x_2323_);
v___y_2227_ = v___y_2273_;
v___y_2228_ = v___y_2274_;
v___y_2229_ = v___y_2275_;
v___y_2230_ = v___y_2276_;
goto v___jp_2226_;
}
else
{
lean_object* v___x_2334_; 
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec_ref(v_config_1808_);
lean_inc(v_mvarId_1809_);
v___x_2334_ = l_Lean_MVarId_getType(v_mvarId_1809_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_Meta_mkEqRefl(v_fst_2326_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = l_Lean_LocalDecl_toExpr(v_val_1840_);
v___x_2339_ = l_Lean_Meta_mkAbsurd(v_a_2335_, v_a_2337_, v___x_2338_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1809_, v_a_2340_, v___y_2274_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_dec_ref_known(v___x_2341_, 1);
v___x_2342_ = lean_box(v___x_1819_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2342_);
v___x_2344_ = v___x_2323_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2346_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 1, v___x_1844_);
lean_ctor_set(v___x_2329_, 0, v___x_2344_);
v___x_2346_ = v___x_2329_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v___x_1844_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
v_a_1826_ = v___x_2346_;
goto v___jp_1825_;
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_del_object(v___x_2329_);
lean_del_object(v___x_2323_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
v_a_2349_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2341_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2341_);
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
lean_del_object(v___x_2329_);
lean_del_object(v___x_2323_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2357_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2339_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2339_);
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
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_a_2335_);
lean_del_object(v___x_2329_);
lean_del_object(v___x_2323_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2365_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2336_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2336_);
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
lean_del_object(v___x_2329_);
lean_dec(v_fst_2326_);
lean_del_object(v___x_2323_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_2373_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2334_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2334_);
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
lean_del_object(v___x_2329_);
lean_dec(v_fst_2326_);
lean_del_object(v___x_2323_);
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2381_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2331_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2331_);
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
}
else
{
lean_dec(v_a_2320_);
v___y_2227_ = v___y_2273_;
v___y_2228_ = v___y_2274_;
v___y_2229_ = v___y_2275_;
v___y_2230_ = v___y_2276_;
goto v___jp_2226_;
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2391_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2319_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2319_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v___x_1957_);
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_2399_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2277_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2277_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
else
{
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
v_a_1834_ = v___x_1885_;
goto v___jp_1833_;
}
v___jp_1845_:
{
lean_object* v___x_1850_; 
lean_inc(v_mvarId_1809_);
v___x_1850_ = l_Lean_MVarId_getType(v_mvarId_1809_, v___y_1849_, v___y_1848_, v___y_1847_, v___y_1846_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v___x_1852_ = l_Lean_LocalDecl_toExpr(v_val_1840_);
v___x_1853_ = l_Lean_Meta_mkNoConfusion(v_a_1851_, v___x_1852_, v___y_1849_, v___y_1848_, v___y_1847_, v___y_1846_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1809_, v_a_1854_, v___y_1848_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
lean_dec_ref_known(v___x_1855_, 1);
v___x_1856_ = lean_box(v___x_1819_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1856_);
v___x_1858_ = v___x_1842_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1844_);
v_a_1826_ = v___x_1859_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_del_object(v___x_1842_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
v_a_1861_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1855_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1855_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_del_object(v___x_1842_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_1869_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1853_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1853_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_del_object(v___x_1842_);
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
v_a_1877_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1850_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1850_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
v___jp_1886_:
{
lean_object* v_searchFuel_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_searchFuel_1891_ = lean_ctor_get(v_config_1808_, 0);
v___x_1892_ = l_Lean_LocalDecl_fvarId(v_val_1840_);
lean_dec(v_val_1840_);
lean_inc(v_searchFuel_1891_);
lean_inc(v_mvarId_1809_);
v___x_1893_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1809_, v___x_1892_, v_searchFuel_1891_, v___y_1889_, v___y_1887_, v___y_1890_, v___y_1888_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; uint8_t v___x_1895_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___x_1895_ = lean_unbox(v_a_1894_);
lean_dec(v_a_1894_);
if (v___x_1895_ == 0)
{
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
v_a_1834_ = v___x_1885_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v___x_1896_ = lean_box(v___x_1819_);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v___x_1844_);
v_a_1826_ = v___x_1898_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_1899_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1893_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1893_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
v___jp_1907_:
{
if (v___y_1912_ == 0)
{
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
v_a_1834_ = v___x_1885_;
goto v___jp_1833_;
}
else
{
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1909_;
v___y_1889_ = v___y_1910_;
v___y_1890_ = v___y_1911_;
goto v___jp_1886_;
}
}
v___jp_1914_:
{
if (v___y_1916_ == 0)
{
v___y_1887_ = v___y_1915_;
v___y_1888_ = v___y_1917_;
v___y_1889_ = v___y_1918_;
v___y_1890_ = v___y_1919_;
goto v___jp_1886_;
}
else
{
v___y_1908_ = v___y_1915_;
v___y_1909_ = v___y_1917_;
v___y_1910_ = v___y_1918_;
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___x_1913_;
goto v___jp_1907_;
}
}
v___jp_1920_:
{
if (v___y_1926_ == 0)
{
v___y_1908_ = v___y_1921_;
v___y_1909_ = v___y_1923_;
v___y_1910_ = v___y_1924_;
v___y_1911_ = v___y_1925_;
v___y_1912_ = v___x_1913_;
goto v___jp_1907_;
}
else
{
v___y_1915_ = v___y_1921_;
v___y_1916_ = v___y_1922_;
v___y_1917_ = v___y_1923_;
v___y_1918_ = v___y_1924_;
v___y_1919_ = v___y_1925_;
goto v___jp_1914_;
}
}
v___jp_1927_:
{
uint8_t v_emptyType_1934_; 
v_emptyType_1934_ = lean_ctor_get_uint8(v_config_1808_, sizeof(void*)*1 + 1);
if (v_emptyType_1934_ == 0)
{
v___y_1921_ = v___y_1931_;
v___y_1922_ = v___y_1928_;
v___y_1923_ = v___y_1933_;
v___y_1924_ = v___y_1930_;
v___y_1925_ = v___y_1932_;
v___y_1926_ = v___x_1913_;
goto v___jp_1920_;
}
else
{
if (v___y_1929_ == 0)
{
v___y_1915_ = v___y_1931_;
v___y_1916_ = v___y_1928_;
v___y_1917_ = v___y_1933_;
v___y_1918_ = v___y_1930_;
v___y_1919_ = v___y_1932_;
goto v___jp_1914_;
}
else
{
v___y_1921_ = v___y_1931_;
v___y_1922_ = v___y_1928_;
v___y_1923_ = v___y_1933_;
v___y_1924_ = v___y_1930_;
v___y_1925_ = v___y_1932_;
v___y_1926_ = v___x_1913_;
goto v___jp_1920_;
}
}
}
v___jp_1935_:
{
if (v___y_1942_ == 0)
{
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___y_1939_;
v___y_1930_ = v___y_1937_;
v___y_1931_ = v___y_1938_;
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1940_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_1943_; 
lean_inc(v_val_1840_);
lean_inc(v_mvarId_1809_);
v___x_1943_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1809_, v_val_1840_, v___y_1937_, v___y_1938_, v___y_1941_, v___y_1940_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; uint8_t v___x_1945_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1945_ = lean_unbox(v_a_1944_);
lean_dec(v_a_1944_);
if (v___x_1945_ == 0)
{
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___y_1939_;
v___y_1930_ = v___y_1937_;
v___y_1931_ = v___y_1938_;
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1940_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
lean_dec(v_val_1840_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v___x_1946_ = lean_box(v___x_1819_);
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1844_);
v_a_1826_ = v___x_1948_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_val_1840_);
lean_del_object(v___x_1823_);
lean_dec(v_snd_1821_);
lean_dec(v_mvarId_1809_);
lean_dec_ref(v_config_1808_);
v_a_1949_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1943_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1943_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
}
v___jp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_a_1826_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1827_);
v___x_1829_ = v___x_1823_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_snd_1821_);
v___x_1829_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
}
v___jp_1833_:
{
lean_object* v___x_1835_; size_t v___x_1836_; size_t v___x_1837_; 
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1832_);
lean_ctor_set(v___x_1835_, 1, v_a_1834_);
v___x_1836_ = ((size_t)1ULL);
v___x_1837_ = lean_usize_add(v_i_1812_, v___x_1836_);
v_i_1812_ = v___x_1837_;
v_b_1813_ = v___x_1835_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2473_, lean_object* v_mvarId_2474_, lean_object* v_as_2475_, lean_object* v_sz_2476_, lean_object* v_i_2477_, lean_object* v_b_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
size_t v_sz_boxed_2484_; size_t v_i_boxed_2485_; lean_object* v_res_2486_; 
v_sz_boxed_2484_ = lean_unbox_usize(v_sz_2476_);
lean_dec(v_sz_2476_);
v_i_boxed_2485_ = lean_unbox_usize(v_i_2477_);
lean_dec(v_i_2477_);
v_res_2486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2473_, v_mvarId_2474_, v_as_2475_, v_sz_boxed_2484_, v_i_boxed_2485_, v_b_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_as_2475_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2487_, lean_object* v_mvarId_2488_, lean_object* v_as_2489_, size_t v_sz_2490_, size_t v_i_2491_, lean_object* v_b_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
uint8_t v___x_2498_; 
v___x_2498_ = lean_usize_dec_lt(v_i_2491_, v_sz_2490_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; 
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_b_2492_);
return v___x_2499_;
}
else
{
lean_object* v_snd_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_3150_; 
v_snd_2500_ = lean_ctor_get(v_b_2492_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_b_2492_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v_b_2492_, 0);
lean_dec(v_unused_3151_);
v___x_2502_ = v_b_2492_;
v_isShared_2503_ = v_isSharedCheck_3150_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_snd_2500_);
lean_dec(v_b_2492_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_3150_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_a_2505_; lean_object* v___x_2511_; lean_object* v_a_2513_; lean_object* v_a_2518_; 
v___x_2511_ = lean_box(0);
v_a_2518_ = lean_array_uget(v_as_2489_, v_i_2491_);
if (lean_obj_tag(v_a_2518_) == 0)
{
lean_del_object(v___x_2502_);
v_a_2513_ = v_snd_2500_;
goto v___jp_2512_;
}
else
{
lean_object* v_val_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_3149_; 
v_val_2519_ = lean_ctor_get(v_a_2518_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_a_2518_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_2521_ = v_a_2518_;
v_isShared_2522_ = v_isSharedCheck_3149_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_val_2519_);
lean_dec(v_a_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_3149_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___x_2564_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; uint8_t v___y_2591_; uint8_t v___x_2592_; lean_object* v___y_2594_; lean_object* v___y_2595_; uint8_t v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2600_; lean_object* v___y_2601_; uint8_t v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; uint8_t v___y_2605_; uint8_t v___y_2607_; uint8_t v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; uint8_t v___y_2615_; uint8_t v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; uint8_t v___y_2621_; 
v___x_2523_ = lean_box(0);
v___x_2564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2592_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2519_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2636_; uint8_t v___y_2638_; uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2647_; uint8_t v___y_2648_; uint8_t v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; uint8_t v___y_2654_; uint8_t v___y_2657_; uint8_t v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v_a_2663_; uint8_t v___y_2667_; uint8_t v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; uint8_t v___y_2711_; uint8_t v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; uint8_t v___y_2740_; uint8_t v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; uint8_t v___y_2746_; lean_object* v___y_2748_; uint8_t v___y_2749_; uint8_t v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; uint8_t v___y_2755_; uint8_t v___y_2758_; uint8_t v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; uint8_t v___y_2764_; uint8_t v___y_2777_; uint8_t v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; uint8_t v___y_2783_; uint8_t v___y_2785_; uint8_t v_isHEq_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; uint8_t v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; uint8_t v_isEq_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___x_3086_; 
v___x_2636_ = l_Lean_LocalDecl_type(v_val_2519_);
lean_inc_ref(v___x_2636_);
v___x_3086_ = l_Lean_Meta_matchNot_x3f(v___x_2636_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
if (lean_obj_tag(v_a_3087_) == 1)
{
lean_object* v_val_3088_; lean_object* v___x_3089_; 
v_val_3088_ = lean_ctor_get(v_a_3087_, 0);
lean_inc(v_val_3088_);
lean_dec_ref_known(v_a_3087_, 1);
v___x_3089_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3088_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v___x_3089_, 1);
if (lean_obj_tag(v_a_3090_) == 1)
{
lean_object* v_val_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3132_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec_ref(v_config_2487_);
v_val_3091_ = lean_ctor_get(v_a_3090_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_a_3090_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3093_ = v_a_3090_;
v_isShared_3094_ = v_isSharedCheck_3132_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_val_3091_);
lean_dec(v_a_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3132_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; 
lean_inc(v_mvarId_2488_);
v___x_3095_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_3098_ = l_Lean_mkFVar(v_val_3091_);
v___x_3099_ = l_Lean_Expr_app___override(v___x_3097_, v___x_3098_);
v___x_3100_ = l_Lean_Meta_mkFalseElim(v_a_3096_, v___x_3099_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3102_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v___x_3102_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_3101_, v___y_2494_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
lean_dec_ref_known(v___x_3102_, 1);
v___x_3103_ = lean_box(v___x_2498_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3103_);
v___x_3105_ = v___x_3093_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_2523_);
v_a_2505_ = v___x_3106_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_del_object(v___x_3093_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_3108_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3102_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3102_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_del_object(v___x_3093_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_3116_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3100_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3100_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_del_object(v___x_3093_);
lean_dec(v_val_3091_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_3124_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3095_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3095_);
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
}
else
{
lean_dec(v_a_3090_);
v___y_2952_ = v___y_2493_;
v___y_2953_ = v___y_2494_;
v___y_2954_ = v___y_2495_;
v___y_2955_ = v___y_2496_;
goto v___jp_2951_;
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_3133_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3089_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3089_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_dec(v_a_3087_);
v___y_2952_ = v___y_2493_;
v___y_2953_ = v___y_2494_;
v___y_2954_ = v___y_2495_;
v___y_2955_ = v___y_2496_;
goto v___jp_2951_;
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_3141_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3086_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3086_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
v___jp_2637_:
{
uint8_t v_genDiseq_2644_; 
v_genDiseq_2644_ = lean_ctor_get_uint8(v_config_2487_, sizeof(void*)*1 + 2);
if (v_genDiseq_2644_ == 0)
{
lean_dec_ref(v___x_2636_);
v___y_2615_ = v___y_2638_;
v___y_2616_ = v___y_2639_;
v___y_2617_ = v___y_2643_;
v___y_2618_ = v___y_2640_;
v___y_2619_ = v___y_2641_;
v___y_2620_ = v___y_2642_;
v___y_2621_ = v___x_2592_;
goto v___jp_2614_;
}
else
{
uint8_t v___x_2645_; 
v___x_2645_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2636_);
v___y_2615_ = v___y_2638_;
v___y_2616_ = v___y_2639_;
v___y_2617_ = v___y_2643_;
v___y_2618_ = v___y_2640_;
v___y_2619_ = v___y_2641_;
v___y_2620_ = v___y_2642_;
v___y_2621_ = v___x_2645_;
goto v___jp_2614_;
}
}
v___jp_2646_:
{
if (v___y_2654_ == 0)
{
lean_dec_ref(v___y_2647_);
v___y_2638_ = v___y_2648_;
v___y_2639_ = v___y_2649_;
v___y_2640_ = v___y_2651_;
v___y_2641_ = v___y_2650_;
v___y_2642_ = v___y_2652_;
v___y_2643_ = v___y_2653_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2655_; 
lean_dec_ref(v___x_2636_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v___x_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___y_2647_);
return v___x_2655_;
}
}
v___jp_2656_:
{
uint8_t v___x_2664_; 
v___x_2664_ = l_Lean_Exception_isInterrupt(v_a_2663_);
if (v___x_2664_ == 0)
{
uint8_t v___x_2665_; 
lean_inc_ref(v_a_2663_);
v___x_2665_ = l_Lean_Exception_isRuntime(v_a_2663_);
v___y_2647_ = v_a_2663_;
v___y_2648_ = v___y_2657_;
v___y_2649_ = v___y_2658_;
v___y_2650_ = v___y_2660_;
v___y_2651_ = v___y_2659_;
v___y_2652_ = v___y_2661_;
v___y_2653_ = v___y_2662_;
v___y_2654_ = v___x_2665_;
goto v___jp_2646_;
}
else
{
v___y_2647_ = v_a_2663_;
v___y_2648_ = v___y_2657_;
v___y_2649_ = v___y_2658_;
v___y_2650_ = v___y_2660_;
v___y_2651_ = v___y_2659_;
v___y_2652_ = v___y_2661_;
v___y_2653_ = v___y_2662_;
v___y_2654_ = v___x_2664_;
goto v___jp_2646_;
}
}
v___jp_2666_:
{
if (lean_obj_tag(v___y_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v_a_2675_ = lean_ctor_get(v___y_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___y_2674_, 1);
v___x_2676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2677_ = l_Lean_Expr_isConstOf(v_a_2675_, v___x_2676_);
lean_dec(v_a_2675_);
if (v___x_2677_ == 0)
{
lean_dec_ref(v___y_2671_);
v___y_2638_ = v___y_2667_;
v___y_2639_ = v___y_2668_;
v___y_2640_ = v___y_2670_;
v___y_2641_ = v___y_2669_;
v___y_2642_ = v___y_2672_;
v___y_2643_ = v___y_2673_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2678_; 
lean_inc_ref(v___y_2671_);
v___x_2678_ = l_Lean_Meta_mkEqRefl(v___y_2671_, v___y_2670_, v___y_2669_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; lean_object* v_dummy_2681_; lean_object* v_nargs_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2682_ = l_Lean_Expr_getAppNumArgs(v___y_2671_);
lean_inc(v_nargs_2682_);
v___x_2683_ = lean_mk_array(v_nargs_2682_, v_dummy_2681_);
v___x_2684_ = lean_unsigned_to_nat(1u);
v___x_2685_ = lean_nat_sub(v_nargs_2682_, v___x_2684_);
lean_dec(v_nargs_2682_);
v___x_2686_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2671_, v___x_2683_, v___x_2685_);
v___x_2687_ = lean_array_push(v___x_2686_, v_a_2679_);
v___x_2688_ = l_Lean_mkAppN(v___x_2680_, v___x_2687_);
lean_dec_ref(v___x_2687_);
lean_inc(v_mvarId_2488_);
v___x_2689_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2670_, v___y_2669_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
lean_inc(v_val_2519_);
v___x_2691_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_2692_ = l_Lean_Meta_mkAbsurd(v_a_2690_, v___x_2691_, v___x_2688_, v___y_2670_, v___y_2669_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
lean_inc(v_mvarId_2488_);
v___x_2694_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_2693_, v___y_2669_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref(v___x_2636_);
lean_dec(v_val_2519_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2703_ == 0)
{
lean_object* v_unused_2704_; 
v_unused_2704_ = lean_ctor_get(v___x_2694_, 0);
lean_dec(v_unused_2704_);
v___x_2696_ = v___x_2694_;
v_isShared_2697_ = v_isSharedCheck_2703_;
goto v_resetjp_2695_;
}
else
{
lean_dec(v___x_2694_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2703_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2698_ = lean_box(v___x_2498_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set_tag(v___x_2696_, 1);
lean_ctor_set(v___x_2696_, 0, v___x_2698_);
v___x_2700_ = v___x_2696_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v___x_2523_);
v_a_2505_ = v___x_2701_;
goto v___jp_2504_;
}
}
}
else
{
lean_object* v_a_2705_; 
v_a_2705_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2694_, 1);
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2669_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2673_;
v_a_2663_ = v_a_2705_;
goto v___jp_2656_;
}
}
else
{
lean_object* v_a_2706_; 
v_a_2706_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2692_, 1);
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2669_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2673_;
v_a_2663_ = v_a_2706_;
goto v___jp_2656_;
}
}
else
{
lean_object* v_a_2707_; 
lean_dec_ref(v___x_2688_);
v_a_2707_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2689_, 1);
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2669_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2673_;
v_a_2663_ = v_a_2707_;
goto v___jp_2656_;
}
}
else
{
lean_object* v_a_2708_; 
lean_dec_ref(v___y_2671_);
v_a_2708_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2678_, 1);
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2669_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2673_;
v_a_2663_ = v_a_2708_;
goto v___jp_2656_;
}
}
}
else
{
lean_object* v_a_2709_; 
lean_dec_ref(v___y_2671_);
v_a_2709_ = lean_ctor_get(v___y_2674_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___y_2674_, 1);
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2669_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2673_;
v_a_2663_ = v_a_2709_;
goto v___jp_2656_;
}
}
v___jp_2710_:
{
lean_object* v___x_2717_; 
lean_inc_ref(v___x_2636_);
v___x_2717_ = l_Lean_Meta_mkDecide(v___x_2636_, v___y_2714_, v___y_2713_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2719_; uint8_t v_transparency_2720_; uint8_t v___x_2721_; uint8_t v___x_2722_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = l_Lean_Meta_Context_config(v___y_2714_);
v_transparency_2720_ = lean_ctor_get_uint8(v___x_2719_, 9);
lean_dec_ref(v___x_2719_);
v___x_2721_ = 1;
v___x_2722_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2720_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v_keyedConfig_2723_; uint8_t v_trackZetaDelta_2724_; lean_object* v_zetaDeltaSet_2725_; lean_object* v_lctx_2726_; lean_object* v_localInstances_2727_; lean_object* v_defEqCtx_x3f_2728_; lean_object* v_synthPendingDepth_2729_; lean_object* v_customCanUnfoldPredicate_x3f_2730_; uint8_t v_univApprox_2731_; uint8_t v_inTypeClassResolution_2732_; uint8_t v_cacheInferType_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_keyedConfig_2723_ = lean_ctor_get(v___y_2714_, 0);
v_trackZetaDelta_2724_ = lean_ctor_get_uint8(v___y_2714_, sizeof(void*)*7);
v_zetaDeltaSet_2725_ = lean_ctor_get(v___y_2714_, 1);
v_lctx_2726_ = lean_ctor_get(v___y_2714_, 2);
v_localInstances_2727_ = lean_ctor_get(v___y_2714_, 3);
v_defEqCtx_x3f_2728_ = lean_ctor_get(v___y_2714_, 4);
v_synthPendingDepth_2729_ = lean_ctor_get(v___y_2714_, 5);
v_customCanUnfoldPredicate_x3f_2730_ = lean_ctor_get(v___y_2714_, 6);
v_univApprox_2731_ = lean_ctor_get_uint8(v___y_2714_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2732_ = lean_ctor_get_uint8(v___y_2714_, sizeof(void*)*7 + 2);
v_cacheInferType_2733_ = lean_ctor_get_uint8(v___y_2714_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2723_);
v___x_2734_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2721_, v_keyedConfig_2723_);
lean_inc(v_customCanUnfoldPredicate_x3f_2730_);
lean_inc(v_synthPendingDepth_2729_);
lean_inc(v_defEqCtx_x3f_2728_);
lean_inc_ref(v_localInstances_2727_);
lean_inc_ref(v_lctx_2726_);
lean_inc(v_zetaDeltaSet_2725_);
v___x_2735_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
lean_ctor_set(v___x_2735_, 1, v_zetaDeltaSet_2725_);
lean_ctor_set(v___x_2735_, 2, v_lctx_2726_);
lean_ctor_set(v___x_2735_, 3, v_localInstances_2727_);
lean_ctor_set(v___x_2735_, 4, v_defEqCtx_x3f_2728_);
lean_ctor_set(v___x_2735_, 5, v_synthPendingDepth_2729_);
lean_ctor_set(v___x_2735_, 6, v_customCanUnfoldPredicate_x3f_2730_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7, v_trackZetaDelta_2724_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7 + 1, v_univApprox_2731_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2732_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7 + 3, v_cacheInferType_2733_);
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2715_);
lean_inc(v___y_2713_);
lean_inc(v_a_2718_);
v___x_2736_ = lean_whnf(v_a_2718_, v___x_2735_, v___y_2713_, v___y_2715_, v___y_2716_);
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v___y_2669_ = v___y_2713_;
v___y_2670_ = v___y_2714_;
v___y_2671_ = v_a_2718_;
v___y_2672_ = v___y_2715_;
v___y_2673_ = v___y_2716_;
v___y_2674_ = v___x_2736_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2737_; 
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2715_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2714_);
lean_inc(v_a_2718_);
v___x_2737_ = lean_whnf(v_a_2718_, v___y_2714_, v___y_2713_, v___y_2715_, v___y_2716_);
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v___y_2669_ = v___y_2713_;
v___y_2670_ = v___y_2714_;
v___y_2671_ = v_a_2718_;
v___y_2672_ = v___y_2715_;
v___y_2673_ = v___y_2716_;
v___y_2674_ = v___x_2737_;
goto v___jp_2666_;
}
}
else
{
lean_object* v_a_2738_; 
v_a_2738_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2717_, 1);
v___y_2657_ = v___y_2711_;
v___y_2658_ = v___y_2712_;
v___y_2659_ = v___y_2714_;
v___y_2660_ = v___y_2713_;
v___y_2661_ = v___y_2715_;
v___y_2662_ = v___y_2716_;
v_a_2663_ = v_a_2738_;
goto v___jp_2656_;
}
}
v___jp_2739_:
{
if (v___y_2746_ == 0)
{
v___y_2638_ = v___y_2740_;
v___y_2639_ = v___y_2741_;
v___y_2640_ = v___y_2743_;
v___y_2641_ = v___y_2742_;
v___y_2642_ = v___y_2744_;
v___y_2643_ = v___y_2745_;
goto v___jp_2637_;
}
else
{
v___y_2711_ = v___y_2740_;
v___y_2712_ = v___y_2741_;
v___y_2713_ = v___y_2742_;
v___y_2714_ = v___y_2743_;
v___y_2715_ = v___y_2744_;
v___y_2716_ = v___y_2745_;
goto v___jp_2710_;
}
}
v___jp_2747_:
{
if (v___y_2755_ == 0)
{
lean_dec_ref(v___y_2748_);
v___y_2740_ = v___y_2749_;
v___y_2741_ = v___y_2750_;
v___y_2742_ = v___y_2752_;
v___y_2743_ = v___y_2751_;
v___y_2744_ = v___y_2753_;
v___y_2745_ = v___y_2754_;
v___y_2746_ = v___x_2592_;
goto v___jp_2739_;
}
else
{
uint8_t v___x_2756_; 
v___x_2756_ = l_Lean_Expr_hasFVar(v___y_2748_);
lean_dec_ref(v___y_2748_);
if (v___x_2756_ == 0)
{
v___y_2711_ = v___y_2749_;
v___y_2712_ = v___y_2750_;
v___y_2713_ = v___y_2752_;
v___y_2714_ = v___y_2751_;
v___y_2715_ = v___y_2753_;
v___y_2716_ = v___y_2754_;
goto v___jp_2710_;
}
else
{
v___y_2740_ = v___y_2749_;
v___y_2741_ = v___y_2750_;
v___y_2742_ = v___y_2752_;
v___y_2743_ = v___y_2751_;
v___y_2744_ = v___y_2753_;
v___y_2745_ = v___y_2754_;
v___y_2746_ = v___x_2592_;
goto v___jp_2739_;
}
}
}
v___jp_2757_:
{
lean_object* v___x_2765_; 
lean_inc_ref(v___x_2636_);
v___x_2765_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2636_, v___y_2761_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; uint8_t v___x_2767_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
v___x_2767_ = l_Lean_Expr_hasMVar(v_a_2766_);
if (v___x_2767_ == 0)
{
v___y_2748_ = v_a_2766_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___y_2759_;
v___y_2751_ = v___y_2760_;
v___y_2752_ = v___y_2761_;
v___y_2753_ = v___y_2762_;
v___y_2754_ = v___y_2763_;
v___y_2755_ = v___y_2764_;
goto v___jp_2747_;
}
else
{
v___y_2748_ = v_a_2766_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___y_2759_;
v___y_2751_ = v___y_2760_;
v___y_2752_ = v___y_2761_;
v___y_2753_ = v___y_2762_;
v___y_2754_ = v___y_2763_;
v___y_2755_ = v___x_2592_;
goto v___jp_2747_;
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v___x_2636_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2768_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2765_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2765_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
v___jp_2776_:
{
if (v___y_2783_ == 0)
{
v___y_2638_ = v___y_2777_;
v___y_2639_ = v___y_2778_;
v___y_2640_ = v___y_2780_;
v___y_2641_ = v___y_2779_;
v___y_2642_ = v___y_2781_;
v___y_2643_ = v___y_2782_;
goto v___jp_2637_;
}
else
{
v___y_2758_ = v___y_2777_;
v___y_2759_ = v___y_2778_;
v___y_2760_ = v___y_2780_;
v___y_2761_ = v___y_2779_;
v___y_2762_ = v___y_2781_;
v___y_2763_ = v___y_2782_;
v___y_2764_ = v___y_2783_;
goto v___jp_2757_;
}
}
v___jp_2784_:
{
uint8_t v_useDecide_2791_; 
v_useDecide_2791_ = lean_ctor_get_uint8(v_config_2487_, sizeof(void*)*1);
if (v_useDecide_2791_ == 0)
{
v___y_2777_ = v_isHEq_2786_;
v___y_2778_ = v___y_2785_;
v___y_2779_ = v___y_2788_;
v___y_2780_ = v___y_2787_;
v___y_2781_ = v___y_2789_;
v___y_2782_ = v___y_2790_;
v___y_2783_ = v___x_2592_;
goto v___jp_2776_;
}
else
{
uint8_t v___x_2792_; 
v___x_2792_ = l_Lean_Expr_hasFVar(v___x_2636_);
if (v___x_2792_ == 0)
{
v___y_2758_ = v_isHEq_2786_;
v___y_2759_ = v___y_2785_;
v___y_2760_ = v___y_2787_;
v___y_2761_ = v___y_2788_;
v___y_2762_ = v___y_2789_;
v___y_2763_ = v___y_2790_;
v___y_2764_ = v_useDecide_2791_;
goto v___jp_2757_;
}
else
{
v___y_2777_ = v_isHEq_2786_;
v___y_2778_ = v___y_2785_;
v___y_2779_ = v___y_2788_;
v___y_2780_ = v___y_2787_;
v___y_2781_ = v___y_2789_;
v___y_2782_ = v___y_2790_;
v___y_2783_ = v___x_2592_;
goto v___jp_2776_;
}
}
}
v___jp_2793_:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Meta_isExprDefEq(v___y_2798_, v___y_2800_, v___y_2794_, v___y_2799_, v___y_2796_, v___y_2795_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; uint8_t v___x_2803_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = lean_unbox(v_a_2802_);
lean_dec(v_a_2802_);
if (v___x_2803_ == 0)
{
v___y_2785_ = v___y_2797_;
v_isHEq_2786_ = v___x_2498_;
v___y_2787_ = v___y_2794_;
v___y_2788_ = v___y_2799_;
v___y_2789_ = v___y_2796_;
v___y_2790_ = v___y_2795_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2804_; 
lean_dec_ref(v___x_2636_);
lean_dec_ref(v_config_2487_);
lean_inc(v_mvarId_2488_);
v___x_2804_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2794_, v___y_2799_, v___y_2796_, v___y_2795_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___x_2806_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_2807_ = l_Lean_Meta_mkEqOfHEq(v___x_2806_, v___x_2498_, v___y_2794_, v___y_2799_, v___y_2796_, v___y_2795_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = l_Lean_Meta_mkNoConfusion(v_a_2805_, v_a_2808_, v___y_2794_, v___y_2799_, v___y_2796_, v___y_2795_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2811_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2809_, 1);
v___x_2811_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_2810_, v___y_2799_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_dec_ref_known(v___x_2811_, 1);
v___x_2812_ = lean_box(v___x_2498_);
v___x_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v___x_2523_);
v_a_2505_ = v___x_2814_;
goto v___jp_2504_;
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2815_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2811_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2811_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2823_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2809_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2809_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec(v_a_2805_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2831_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2807_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2807_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2839_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2804_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2804_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec_ref(v___x_2636_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2847_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2801_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2801_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
v___jp_2855_:
{
lean_object* v___x_2861_; 
lean_inc_ref(v___x_2636_);
v___x_2861_ = l_Lean_Meta_matchHEq_x3f(v___x_2636_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
if (lean_obj_tag(v_a_2862_) == 1)
{
lean_object* v_val_2863_; lean_object* v_snd_2864_; lean_object* v_snd_2865_; lean_object* v_fst_2866_; lean_object* v_fst_2867_; lean_object* v_fst_2868_; lean_object* v_snd_2869_; lean_object* v___x_2870_; 
v_val_2863_ = lean_ctor_get(v_a_2862_, 0);
lean_inc(v_val_2863_);
lean_dec_ref_known(v_a_2862_, 1);
v_snd_2864_ = lean_ctor_get(v_val_2863_, 1);
lean_inc(v_snd_2864_);
v_snd_2865_ = lean_ctor_get(v_snd_2864_, 1);
lean_inc(v_snd_2865_);
v_fst_2866_ = lean_ctor_get(v_val_2863_, 0);
lean_inc(v_fst_2866_);
lean_dec(v_val_2863_);
v_fst_2867_ = lean_ctor_get(v_snd_2864_, 0);
lean_inc(v_fst_2867_);
lean_dec(v_snd_2864_);
v_fst_2868_ = lean_ctor_get(v_snd_2865_, 0);
lean_inc(v_fst_2868_);
v_snd_2869_ = lean_ctor_get(v_snd_2865_, 1);
lean_inc(v_snd_2869_);
lean_dec(v_snd_2865_);
v___x_2870_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2867_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
if (lean_obj_tag(v_a_2871_) == 1)
{
lean_object* v_val_2872_; lean_object* v___x_2873_; 
v_val_2872_ = lean_ctor_get(v_a_2871_, 0);
lean_inc(v_val_2872_);
lean_dec_ref_known(v_a_2871_, 1);
v___x_2873_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2869_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
if (lean_obj_tag(v_a_2874_) == 1)
{
lean_object* v_toConstantVal_2875_; lean_object* v_val_2876_; lean_object* v_toConstantVal_2877_; lean_object* v_name_2878_; lean_object* v_name_2879_; uint8_t v___x_2880_; 
v_toConstantVal_2875_ = lean_ctor_get(v_val_2872_, 0);
lean_inc_ref(v_toConstantVal_2875_);
lean_dec(v_val_2872_);
v_val_2876_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_val_2876_);
lean_dec_ref_known(v_a_2874_, 1);
v_toConstantVal_2877_ = lean_ctor_get(v_val_2876_, 0);
lean_inc_ref(v_toConstantVal_2877_);
lean_dec(v_val_2876_);
v_name_2878_ = lean_ctor_get(v_toConstantVal_2875_, 0);
lean_inc(v_name_2878_);
lean_dec_ref(v_toConstantVal_2875_);
v_name_2879_ = lean_ctor_get(v_toConstantVal_2877_, 0);
lean_inc(v_name_2879_);
lean_dec_ref(v_toConstantVal_2877_);
v___x_2880_ = lean_name_eq(v_name_2878_, v_name_2879_);
lean_dec(v_name_2879_);
lean_dec(v_name_2878_);
if (v___x_2880_ == 0)
{
v___y_2794_ = v___y_2857_;
v___y_2795_ = v___y_2860_;
v___y_2796_ = v___y_2859_;
v___y_2797_ = v_isEq_2856_;
v___y_2798_ = v_fst_2866_;
v___y_2799_ = v___y_2858_;
v___y_2800_ = v_fst_2868_;
goto v___jp_2793_;
}
else
{
if (v___x_2592_ == 0)
{
lean_dec(v_fst_2868_);
lean_dec(v_fst_2866_);
v___y_2785_ = v_isEq_2856_;
v_isHEq_2786_ = v___x_2498_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
v___y_2790_ = v___y_2860_;
goto v___jp_2784_;
}
else
{
v___y_2794_ = v___y_2857_;
v___y_2795_ = v___y_2860_;
v___y_2796_ = v___y_2859_;
v___y_2797_ = v_isEq_2856_;
v___y_2798_ = v_fst_2866_;
v___y_2799_ = v___y_2858_;
v___y_2800_ = v_fst_2868_;
goto v___jp_2793_;
}
}
}
else
{
lean_dec(v_a_2874_);
lean_dec(v_val_2872_);
lean_dec(v_fst_2868_);
lean_dec(v_fst_2866_);
v___y_2785_ = v_isEq_2856_;
v_isHEq_2786_ = v___x_2498_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
v___y_2790_ = v___y_2860_;
goto v___jp_2784_;
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_val_2872_);
lean_dec(v_fst_2868_);
lean_dec(v_fst_2866_);
lean_dec_ref(v___x_2636_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2881_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2873_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2873_);
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
else
{
lean_dec(v_a_2871_);
lean_dec(v_snd_2869_);
lean_dec(v_fst_2868_);
lean_dec(v_fst_2866_);
v___y_2785_ = v_isEq_2856_;
v_isHEq_2786_ = v___x_2498_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
v___y_2790_ = v___y_2860_;
goto v___jp_2784_;
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v_snd_2869_);
lean_dec(v_fst_2868_);
lean_dec(v_fst_2866_);
lean_dec_ref(v___x_2636_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2889_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2870_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2870_);
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
else
{
lean_dec(v_a_2862_);
v___y_2785_ = v_isEq_2856_;
v_isHEq_2786_ = v___x_2592_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
v___y_2790_ = v___y_2860_;
goto v___jp_2784_;
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v___x_2636_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2897_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2861_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2861_);
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
v___jp_2905_:
{
lean_object* v___x_2910_; 
lean_inc_ref(v___x_2636_);
v___x_2910_ = l_Lean_Meta_matchEq_x3f(v___x_2636_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
if (lean_obj_tag(v_a_2911_) == 1)
{
lean_object* v_val_2912_; lean_object* v_snd_2913_; lean_object* v_fst_2914_; lean_object* v_snd_2915_; lean_object* v___x_2916_; 
v_val_2912_ = lean_ctor_get(v_a_2911_, 0);
lean_inc(v_val_2912_);
lean_dec_ref_known(v_a_2911_, 1);
v_snd_2913_ = lean_ctor_get(v_val_2912_, 1);
lean_inc(v_snd_2913_);
lean_dec(v_val_2912_);
v_fst_2914_ = lean_ctor_get(v_snd_2913_, 0);
lean_inc(v_fst_2914_);
v_snd_2915_ = lean_ctor_get(v_snd_2913_, 1);
lean_inc(v_snd_2915_);
lean_dec(v_snd_2913_);
v___x_2916_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2914_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2916_, 1);
if (lean_obj_tag(v_a_2917_) == 1)
{
lean_object* v_val_2918_; lean_object* v___x_2919_; 
v_val_2918_ = lean_ctor_get(v_a_2917_, 0);
lean_inc(v_val_2918_);
lean_dec_ref_known(v_a_2917_, 1);
v___x_2919_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2915_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
if (lean_obj_tag(v_a_2920_) == 1)
{
lean_object* v_toConstantVal_2921_; lean_object* v_val_2922_; lean_object* v_toConstantVal_2923_; lean_object* v_name_2924_; lean_object* v_name_2925_; uint8_t v___x_2926_; 
v_toConstantVal_2921_ = lean_ctor_get(v_val_2918_, 0);
lean_inc_ref(v_toConstantVal_2921_);
lean_dec(v_val_2918_);
v_val_2922_ = lean_ctor_get(v_a_2920_, 0);
lean_inc(v_val_2922_);
lean_dec_ref_known(v_a_2920_, 1);
v_toConstantVal_2923_ = lean_ctor_get(v_val_2922_, 0);
lean_inc_ref(v_toConstantVal_2923_);
lean_dec(v_val_2922_);
v_name_2924_ = lean_ctor_get(v_toConstantVal_2921_, 0);
lean_inc(v_name_2924_);
lean_dec_ref(v_toConstantVal_2921_);
v_name_2925_ = lean_ctor_get(v_toConstantVal_2923_, 0);
lean_inc(v_name_2925_);
lean_dec_ref(v_toConstantVal_2923_);
v___x_2926_ = lean_name_eq(v_name_2924_, v_name_2925_);
lean_dec(v_name_2925_);
lean_dec(v_name_2924_);
if (v___x_2926_ == 0)
{
lean_dec_ref(v___x_2636_);
lean_dec_ref(v_config_2487_);
v___y_2525_ = v___y_2908_;
v___y_2526_ = v___y_2909_;
v___y_2527_ = v___y_2907_;
v___y_2528_ = v___y_2906_;
goto v___jp_2524_;
}
else
{
if (v___x_2592_ == 0)
{
lean_del_object(v___x_2521_);
v_isEq_2856_ = v___x_2498_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
v___y_2860_ = v___y_2909_;
goto v___jp_2855_;
}
else
{
lean_dec_ref(v___x_2636_);
lean_dec_ref(v_config_2487_);
v___y_2525_ = v___y_2908_;
v___y_2526_ = v___y_2909_;
v___y_2527_ = v___y_2907_;
v___y_2528_ = v___y_2906_;
goto v___jp_2524_;
}
}
}
else
{
lean_dec(v_a_2920_);
lean_dec(v_val_2918_);
lean_del_object(v___x_2521_);
v_isEq_2856_ = v___x_2498_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
v___y_2860_ = v___y_2909_;
goto v___jp_2855_;
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v_val_2918_);
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2927_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2919_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2919_);
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
lean_dec(v_a_2917_);
lean_dec(v_snd_2915_);
lean_del_object(v___x_2521_);
v_isEq_2856_ = v___x_2498_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
v___y_2860_ = v___y_2909_;
goto v___jp_2855_;
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec(v_snd_2915_);
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2935_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2916_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2916_);
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
else
{
lean_dec(v_a_2911_);
lean_del_object(v___x_2521_);
v_isEq_2856_ = v___x_2592_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
v___y_2860_ = v___y_2909_;
goto v___jp_2855_;
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2943_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2910_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2910_);
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
v___jp_2951_:
{
lean_object* v___x_2956_; 
lean_inc_ref(v___x_2636_);
v___x_2956_ = l_Lean_refutableHasNotBit_x3f(v___x_2636_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
if (lean_obj_tag(v_a_2957_) == 1)
{
lean_object* v_val_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec_ref(v_config_2487_);
v_val_2958_ = lean_ctor_get(v_a_2957_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2960_ = v_a_2957_;
v_isShared_2961_ = v_isSharedCheck_2997_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_val_2958_);
lean_dec(v_a_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2997_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; 
lean_inc(v_mvarId_2488_);
v___x_2962_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v___x_2964_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_2965_ = l_Lean_Meta_mkAbsurd(v_a_2963_, v_val_2958_, v___x_2964_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v___x_2967_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_2966_, v___y_2953_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
lean_dec_ref_known(v___x_2967_, 1);
v___x_2968_ = lean_box(v___x_2498_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2968_);
v___x_2970_ = v___x_2960_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
lean_ctor_set(v___x_2971_, 1, v___x_2523_);
v_a_2505_ = v___x_2971_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_del_object(v___x_2960_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2973_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2967_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2967_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_del_object(v___x_2960_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2981_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2965_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2965_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_del_object(v___x_2960_);
lean_dec(v_val_2958_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2989_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2962_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2962_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
else
{
lean_object* v___x_2998_; 
lean_dec(v_a_2957_);
lean_inc_ref(v___x_2636_);
v___x_2998_ = l_Lean_Meta_matchNe_x3f(v___x_2636_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
if (lean_obj_tag(v_a_2999_) == 1)
{
lean_object* v_val_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3069_; 
v_val_3000_ = lean_ctor_get(v_a_2999_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_a_2999_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3002_ = v_a_2999_;
v_isShared_3003_ = v_isSharedCheck_3069_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_val_3000_);
lean_dec(v_a_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3069_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v_snd_3004_; lean_object* v_fst_3005_; lean_object* v_snd_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3068_; 
v_snd_3004_ = lean_ctor_get(v_val_3000_, 1);
lean_inc(v_snd_3004_);
lean_dec(v_val_3000_);
v_fst_3005_ = lean_ctor_get(v_snd_3004_, 0);
v_snd_3006_ = lean_ctor_get(v_snd_3004_, 1);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_snd_3004_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3008_ = v_snd_3004_;
v_isShared_3009_ = v_isSharedCheck_3068_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_snd_3006_);
lean_inc(v_fst_3005_);
lean_dec(v_snd_3004_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3068_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; 
lean_inc(v_fst_3005_);
v___x_3010_ = l_Lean_Meta_isExprDefEq(v_fst_3005_, v_snd_3006_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; uint8_t v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = lean_unbox(v_a_3011_);
lean_dec(v_a_3011_);
if (v___x_3012_ == 0)
{
lean_del_object(v___x_3008_);
lean_dec(v_fst_3005_);
lean_del_object(v___x_3002_);
v___y_2906_ = v___y_2952_;
v___y_2907_ = v___y_2953_;
v___y_2908_ = v___y_2954_;
v___y_2909_ = v___y_2955_;
goto v___jp_2905_;
}
else
{
lean_object* v___x_3013_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec_ref(v_config_2487_);
lean_inc(v_mvarId_2488_);
v___x_3013_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v___x_3015_ = l_Lean_Meta_mkEqRefl(v_fst_3005_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_3018_ = l_Lean_Meta_mkAbsurd(v_a_3014_, v_a_3016_, v___x_3017_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_3019_, v___y_2953_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3020_, 1);
v___x_3021_ = lean_box(v___x_2498_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_3021_);
v___x_3023_ = v___x_3002_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3025_; 
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 1, v___x_2523_);
lean_ctor_set(v___x_3008_, 0, v___x_3023_);
v___x_3025_ = v___x_3008_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v___x_2523_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
v_a_2505_ = v___x_3025_;
goto v___jp_2504_;
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_del_object(v___x_3008_);
lean_del_object(v___x_3002_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_3028_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3020_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3020_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_del_object(v___x_3008_);
lean_del_object(v___x_3002_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_3036_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3018_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3018_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v_a_3014_);
lean_del_object(v___x_3008_);
lean_del_object(v___x_3002_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_3044_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3015_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3015_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_del_object(v___x_3008_);
lean_dec(v_fst_3005_);
lean_del_object(v___x_3002_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_3052_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3013_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3013_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_del_object(v___x_3008_);
lean_dec(v_fst_3005_);
lean_del_object(v___x_3002_);
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_3060_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3010_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3010_);
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
}
else
{
lean_dec(v_a_2999_);
v___y_2906_ = v___y_2952_;
v___y_2907_ = v___y_2953_;
v___y_2908_ = v___y_2954_;
v___y_2909_ = v___y_2955_;
goto v___jp_2905_;
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_3070_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_2998_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_2998_);
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
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_3078_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_2956_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_2956_);
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
}
else
{
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2513_ = v___x_2564_;
goto v___jp_2512_;
}
v___jp_2524_:
{
lean_object* v___x_2529_; 
lean_inc(v_mvarId_2488_);
v___x_2529_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2528_, v___y_2527_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_2532_ = l_Lean_Meta_mkNoConfusion(v_a_2530_, v___x_2531_, v___y_2528_, v___y_2527_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_2533_, v___y_2527_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
lean_dec_ref_known(v___x_2534_, 1);
v___x_2535_ = lean_box(v___x_2498_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2535_);
v___x_2537_ = v___x_2521_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
lean_ctor_set(v___x_2538_, 1, v___x_2523_);
v_a_2505_ = v___x_2538_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_del_object(v___x_2521_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2540_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2534_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2534_);
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
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_del_object(v___x_2521_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2548_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2532_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2532_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2556_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2529_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2529_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
v___jp_2565_:
{
lean_object* v_searchFuel_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_searchFuel_2570_ = lean_ctor_get(v_config_2487_, 0);
v___x_2571_ = l_Lean_LocalDecl_fvarId(v_val_2519_);
lean_dec(v_val_2519_);
lean_inc(v_searchFuel_2570_);
lean_inc(v_mvarId_2488_);
v___x_2572_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2488_, v___x_2571_, v_searchFuel_2570_, v___y_2567_, v___y_2566_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; uint8_t v___x_2574_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v___x_2574_ = lean_unbox(v_a_2573_);
lean_dec(v_a_2573_);
if (v___x_2574_ == 0)
{
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2513_ = v___x_2564_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v___x_2575_ = lean_box(v___x_2498_);
v___x_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___x_2523_);
v_a_2505_ = v___x_2577_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2578_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2572_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2572_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
v___jp_2586_:
{
if (v___y_2591_ == 0)
{
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2513_ = v___x_2564_;
goto v___jp_2512_;
}
else
{
v___y_2566_ = v___y_2587_;
v___y_2567_ = v___y_2588_;
v___y_2568_ = v___y_2589_;
v___y_2569_ = v___y_2590_;
goto v___jp_2565_;
}
}
v___jp_2593_:
{
if (v___y_2596_ == 0)
{
v___y_2566_ = v___y_2594_;
v___y_2567_ = v___y_2595_;
v___y_2568_ = v___y_2597_;
v___y_2569_ = v___y_2598_;
goto v___jp_2565_;
}
else
{
v___y_2587_ = v___y_2594_;
v___y_2588_ = v___y_2595_;
v___y_2589_ = v___y_2597_;
v___y_2590_ = v___y_2598_;
v___y_2591_ = v___x_2592_;
goto v___jp_2586_;
}
}
v___jp_2599_:
{
if (v___y_2605_ == 0)
{
v___y_2587_ = v___y_2600_;
v___y_2588_ = v___y_2601_;
v___y_2589_ = v___y_2603_;
v___y_2590_ = v___y_2604_;
v___y_2591_ = v___x_2592_;
goto v___jp_2586_;
}
else
{
v___y_2594_ = v___y_2600_;
v___y_2595_ = v___y_2601_;
v___y_2596_ = v___y_2602_;
v___y_2597_ = v___y_2603_;
v___y_2598_ = v___y_2604_;
goto v___jp_2593_;
}
}
v___jp_2606_:
{
uint8_t v_emptyType_2613_; 
v_emptyType_2613_ = lean_ctor_get_uint8(v_config_2487_, sizeof(void*)*1 + 1);
if (v_emptyType_2613_ == 0)
{
v___y_2600_ = v___y_2610_;
v___y_2601_ = v___y_2609_;
v___y_2602_ = v___y_2607_;
v___y_2603_ = v___y_2611_;
v___y_2604_ = v___y_2612_;
v___y_2605_ = v___x_2592_;
goto v___jp_2599_;
}
else
{
if (v___y_2608_ == 0)
{
v___y_2594_ = v___y_2610_;
v___y_2595_ = v___y_2609_;
v___y_2596_ = v___y_2607_;
v___y_2597_ = v___y_2611_;
v___y_2598_ = v___y_2612_;
goto v___jp_2593_;
}
else
{
v___y_2600_ = v___y_2610_;
v___y_2601_ = v___y_2609_;
v___y_2602_ = v___y_2607_;
v___y_2603_ = v___y_2611_;
v___y_2604_ = v___y_2612_;
v___y_2605_ = v___x_2592_;
goto v___jp_2599_;
}
}
}
v___jp_2614_:
{
if (v___y_2621_ == 0)
{
v___y_2607_ = v___y_2615_;
v___y_2608_ = v___y_2616_;
v___y_2609_ = v___y_2618_;
v___y_2610_ = v___y_2619_;
v___y_2611_ = v___y_2620_;
v___y_2612_ = v___y_2617_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2622_; 
lean_inc(v_val_2519_);
lean_inc(v_mvarId_2488_);
v___x_2622_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2488_, v_val_2519_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2617_);
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
v___y_2607_ = v___y_2615_;
v___y_2608_ = v___y_2616_;
v___y_2609_ = v___y_2618_;
v___y_2610_ = v___y_2619_;
v___y_2611_ = v___y_2620_;
v___y_2612_ = v___y_2617_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec(v_val_2519_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v___x_2625_ = lean_box(v___x_2498_);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___x_2523_);
v_a_2505_ = v___x_2627_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
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
}
v___jp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_a_2505_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2506_);
v___x_2508_ = v___x_2502_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_snd_2500_);
v___x_2508_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
v___jp_2512_:
{
lean_object* v___x_2514_; size_t v___x_2515_; size_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2511_);
lean_ctor_set(v___x_2514_, 1, v_a_2513_);
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_add(v_i_2491_, v___x_2515_);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2487_, v_mvarId_2488_, v_as_2489_, v_sz_2490_, v___x_2516_, v___x_2514_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
return v___x_2517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3152_, lean_object* v_mvarId_3153_, lean_object* v_as_3154_, lean_object* v_sz_3155_, lean_object* v_i_3156_, lean_object* v_b_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
size_t v_sz_boxed_3163_; size_t v_i_boxed_3164_; lean_object* v_res_3165_; 
v_sz_boxed_3163_ = lean_unbox_usize(v_sz_3155_);
lean_dec(v_sz_3155_);
v_i_boxed_3164_ = lean_unbox_usize(v_i_3156_);
lean_dec(v_i_3156_);
v_res_3165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3152_, v_mvarId_3153_, v_as_3154_, v_sz_boxed_3163_, v_i_boxed_3164_, v_b_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec_ref(v_as_3154_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3169_, lean_object* v_mvarId_3170_, lean_object* v_as_3171_, size_t v_sz_3172_, size_t v_i_3173_, lean_object* v_b_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
uint8_t v___x_3180_; 
v___x_3180_ = lean_usize_dec_lt(v_i_3173_, v_sz_3172_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_b_3174_);
return v___x_3181_;
}
else
{
lean_object* v_snd_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3852_; 
v_snd_3182_ = lean_ctor_get(v_b_3174_, 1);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_b_3174_);
if (v_isSharedCheck_3852_ == 0)
{
lean_object* v_unused_3853_; 
v_unused_3853_ = lean_ctor_get(v_b_3174_, 0);
lean_dec(v_unused_3853_);
v___x_3184_ = v_b_3174_;
v_isShared_3185_ = v_isSharedCheck_3852_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_snd_3182_);
lean_dec(v_b_3174_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3852_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_a_3187_; lean_object* v___x_3193_; lean_object* v_a_3195_; lean_object* v_a_3200_; 
v___x_3193_ = lean_box(0);
v_a_3200_ = lean_array_uget(v_as_3171_, v_i_3173_);
if (lean_obj_tag(v_a_3200_) == 0)
{
lean_del_object(v___x_3184_);
v_a_3195_ = v_snd_3182_;
goto v___jp_3194_;
}
else
{
lean_object* v_val_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3851_; 
v_val_3201_ = lean_ctor_get(v_a_3200_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v_a_3200_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3203_ = v_a_3200_;
v_isShared_3204_ = v_isSharedCheck_3851_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_val_3201_);
lean_dec(v_a_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3851_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___x_3247_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint8_t v___y_3275_; uint8_t v___x_3276_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; uint8_t v___y_3282_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; uint8_t v___y_3288_; uint8_t v___y_3289_; uint8_t v___y_3291_; uint8_t v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3299_; uint8_t v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; uint8_t v___y_3304_; uint8_t v___y_3305_; 
v___x_3205_ = lean_box(0);
v___x_3247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3276_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3201_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3321_; uint8_t v___y_3323_; uint8_t v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3332_; lean_object* v___y_3333_; uint8_t v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; uint8_t v___y_3337_; lean_object* v___y_3338_; uint8_t v___y_3339_; lean_object* v___y_3342_; lean_object* v___y_3343_; uint8_t v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; uint8_t v___y_3347_; lean_object* v_a_3348_; lean_object* v___y_3352_; lean_object* v___y_3353_; uint8_t v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; uint8_t v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3403_; lean_object* v___y_3404_; uint8_t v___y_3405_; lean_object* v___y_3406_; uint8_t v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3432_; lean_object* v___y_3433_; uint8_t v___y_3434_; lean_object* v___y_3435_; uint8_t v___y_3436_; lean_object* v___y_3437_; uint8_t v___y_3438_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; uint8_t v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; uint8_t v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3450_; lean_object* v___y_3451_; uint8_t v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; uint8_t v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3469_; lean_object* v___y_3470_; uint8_t v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; lean_object* v___y_3474_; uint8_t v___y_3475_; uint8_t v___y_3477_; uint8_t v_isHEq_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; uint8_t v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; uint8_t v_isEq_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___x_3781_; 
v___x_3321_ = l_Lean_LocalDecl_type(v_val_3201_);
lean_inc_ref(v___x_3321_);
v___x_3781_ = l_Lean_Meta_matchNot_x3f(v___x_3321_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
if (lean_obj_tag(v_a_3782_) == 1)
{
lean_object* v_val_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3842_; 
v_val_3783_ = lean_ctor_get(v_a_3782_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_a_3782_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3785_ = v_a_3782_;
v_isShared_3786_ = v_isSharedCheck_3842_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_val_3783_);
lean_dec(v_a_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3842_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; 
v___x_3787_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3783_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref_known(v___x_3787_, 1);
if (lean_obj_tag(v_a_3788_) == 1)
{
lean_object* v_val_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec_ref(v_config_3169_);
v_val_3789_ = lean_ctor_get(v_a_3788_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_a_3788_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3791_ = v_a_3788_;
v_isShared_3792_ = v_isSharedCheck_3833_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_val_3789_);
lean_dec(v_a_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3833_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3793_; 
lean_inc(v_mvarId_3170_);
v___x_3793_ = l_Lean_MVarId_getType(v_mvarId_3170_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref_known(v___x_3793_, 1);
v___x_3795_ = l_Lean_LocalDecl_toExpr(v_val_3201_);
v___x_3796_ = l_Lean_mkFVar(v_val_3789_);
v___x_3797_ = l_Lean_Expr_app___override(v___x_3795_, v___x_3796_);
v___x_3798_ = l_Lean_Meta_mkFalseElim(v_a_3794_, v___x_3797_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3800_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3798_, 1);
v___x_3800_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3170_, v_a_3799_, v___y_3176_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3803_; 
lean_dec_ref_known(v___x_3800_, 1);
v___x_3801_ = lean_box(v___x_3180_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3801_);
v___x_3803_ = v___x_3791_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3801_);
v___x_3803_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3804_; lean_object* v___x_3806_; 
v___x_3804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
lean_ctor_set(v___x_3804_, 1, v___x_3205_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set_tag(v___x_3785_, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3804_);
v___x_3806_ = v___x_3785_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
v_a_3187_ = v___x_3806_;
goto v___jp_3186_;
}
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_del_object(v___x_3791_);
lean_del_object(v___x_3785_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
v_a_3809_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3800_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3800_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_del_object(v___x_3791_);
lean_del_object(v___x_3785_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3817_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3798_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3798_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_del_object(v___x_3791_);
lean_dec(v_val_3789_);
lean_del_object(v___x_3785_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3825_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3793_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3793_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
else
{
lean_dec(v_a_3788_);
lean_del_object(v___x_3785_);
v___y_3645_ = v___y_3175_;
v___y_3646_ = v___y_3176_;
v___y_3647_ = v___y_3177_;
v___y_3648_ = v___y_3178_;
goto v___jp_3644_;
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_del_object(v___x_3785_);
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3834_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3787_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3787_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
else
{
lean_dec(v_a_3782_);
v___y_3645_ = v___y_3175_;
v___y_3646_ = v___y_3176_;
v___y_3647_ = v___y_3177_;
v___y_3648_ = v___y_3178_;
goto v___jp_3644_;
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3843_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3781_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3781_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
v___jp_3322_:
{
uint8_t v_genDiseq_3329_; 
v_genDiseq_3329_ = lean_ctor_get_uint8(v_config_3169_, sizeof(void*)*1 + 2);
if (v_genDiseq_3329_ == 0)
{
lean_dec_ref(v___x_3321_);
v___y_3299_ = v___y_3327_;
v___y_3300_ = v___y_3323_;
v___y_3301_ = v___y_3328_;
v___y_3302_ = v___y_3326_;
v___y_3303_ = v___y_3325_;
v___y_3304_ = v___y_3324_;
v___y_3305_ = v___x_3276_;
goto v___jp_3298_;
}
else
{
uint8_t v___x_3330_; 
v___x_3330_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3321_);
v___y_3299_ = v___y_3327_;
v___y_3300_ = v___y_3323_;
v___y_3301_ = v___y_3328_;
v___y_3302_ = v___y_3326_;
v___y_3303_ = v___y_3325_;
v___y_3304_ = v___y_3324_;
v___y_3305_ = v___x_3330_;
goto v___jp_3298_;
}
}
v___jp_3331_:
{
if (v___y_3339_ == 0)
{
lean_dec_ref(v___y_3336_);
v___y_3323_ = v___y_3334_;
v___y_3324_ = v___y_3337_;
v___y_3325_ = v___y_3335_;
v___y_3326_ = v___y_3333_;
v___y_3327_ = v___y_3338_;
v___y_3328_ = v___y_3332_;
goto v___jp_3322_;
}
else
{
lean_object* v___x_3340_; 
lean_dec_ref(v___x_3321_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v___x_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3340_, 0, v___y_3336_);
return v___x_3340_;
}
}
v___jp_3341_:
{
uint8_t v___x_3349_; 
v___x_3349_ = l_Lean_Exception_isInterrupt(v_a_3348_);
if (v___x_3349_ == 0)
{
uint8_t v___x_3350_; 
lean_inc_ref(v_a_3348_);
v___x_3350_ = l_Lean_Exception_isRuntime(v_a_3348_);
v___y_3332_ = v___y_3342_;
v___y_3333_ = v___y_3343_;
v___y_3334_ = v___y_3344_;
v___y_3335_ = v___y_3345_;
v___y_3336_ = v_a_3348_;
v___y_3337_ = v___y_3347_;
v___y_3338_ = v___y_3346_;
v___y_3339_ = v___x_3350_;
goto v___jp_3331_;
}
else
{
v___y_3332_ = v___y_3342_;
v___y_3333_ = v___y_3343_;
v___y_3334_ = v___y_3344_;
v___y_3335_ = v___y_3345_;
v___y_3336_ = v_a_3348_;
v___y_3337_ = v___y_3347_;
v___y_3338_ = v___y_3346_;
v___y_3339_ = v___x_3349_;
goto v___jp_3331_;
}
}
v___jp_3351_:
{
if (lean_obj_tag(v___y_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v_a_3360_ = lean_ctor_get(v___y_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___y_3359_, 1);
v___x_3361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3362_ = l_Lean_Expr_isConstOf(v_a_3360_, v___x_3361_);
lean_dec(v_a_3360_);
if (v___x_3362_ == 0)
{
lean_dec_ref(v___y_3356_);
v___y_3323_ = v___y_3354_;
v___y_3324_ = v___y_3357_;
v___y_3325_ = v___y_3355_;
v___y_3326_ = v___y_3353_;
v___y_3327_ = v___y_3358_;
v___y_3328_ = v___y_3352_;
goto v___jp_3322_;
}
else
{
lean_object* v___x_3363_; 
lean_inc_ref(v___y_3356_);
v___x_3363_ = l_Lean_Meta_mkEqRefl(v___y_3356_, v___y_3355_, v___y_3353_, v___y_3358_, v___y_3352_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3365_; lean_object* v_dummy_3366_; lean_object* v_nargs_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v___x_3365_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3367_ = l_Lean_Expr_getAppNumArgs(v___y_3356_);
lean_inc(v_nargs_3367_);
v___x_3368_ = lean_mk_array(v_nargs_3367_, v_dummy_3366_);
v___x_3369_ = lean_unsigned_to_nat(1u);
v___x_3370_ = lean_nat_sub(v_nargs_3367_, v___x_3369_);
lean_dec(v_nargs_3367_);
v___x_3371_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3356_, v___x_3368_, v___x_3370_);
v___x_3372_ = lean_array_push(v___x_3371_, v_a_3364_);
v___x_3373_ = l_Lean_mkAppN(v___x_3365_, v___x_3372_);
lean_dec_ref(v___x_3372_);
lean_inc(v_mvarId_3170_);
v___x_3374_ = l_Lean_MVarId_getType(v_mvarId_3170_, v___y_3355_, v___y_3353_, v___y_3358_, v___y_3352_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
lean_inc(v_val_3201_);
v___x_3376_ = l_Lean_LocalDecl_toExpr(v_val_3201_);
v___x_3377_ = l_Lean_Meta_mkAbsurd(v_a_3375_, v___x_3376_, v___x_3373_, v___y_3355_, v___y_3353_, v___y_3358_, v___y_3352_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3397_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3380_ = v___x_3377_;
v_isShared_3381_ = v_isSharedCheck_3397_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3377_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3397_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; 
lean_inc(v_mvarId_3170_);
v___x_3382_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3170_, v_a_3378_, v___y_3353_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v___x_3321_);
lean_dec(v_val_3201_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; 
v_unused_3395_ = lean_ctor_get(v___x_3382_, 0);
lean_dec(v_unused_3395_);
v___x_3384_ = v___x_3382_;
v_isShared_3385_ = v_isSharedCheck_3394_;
goto v_resetjp_3383_;
}
else
{
lean_dec(v___x_3382_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3394_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3386_ = lean_box(v___x_3180_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set_tag(v___x_3384_, 1);
lean_ctor_set(v___x_3384_, 0, v___x_3386_);
v___x_3388_ = v___x_3384_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v___x_3205_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3389_);
v___x_3391_ = v___x_3380_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
v_a_3187_ = v___x_3391_;
goto v___jp_3186_;
}
}
}
}
else
{
lean_object* v_a_3396_; 
lean_del_object(v___x_3380_);
v_a_3396_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3382_, 1);
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3357_;
v_a_3348_ = v_a_3396_;
goto v___jp_3341_;
}
}
}
else
{
lean_object* v_a_3398_; 
v_a_3398_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3377_, 1);
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3357_;
v_a_3348_ = v_a_3398_;
goto v___jp_3341_;
}
}
else
{
lean_object* v_a_3399_; 
lean_dec_ref(v___x_3373_);
v_a_3399_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3374_, 1);
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3357_;
v_a_3348_ = v_a_3399_;
goto v___jp_3341_;
}
}
else
{
lean_object* v_a_3400_; 
lean_dec_ref(v___y_3356_);
v_a_3400_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3363_, 1);
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3357_;
v_a_3348_ = v_a_3400_;
goto v___jp_3341_;
}
}
}
else
{
lean_object* v_a_3401_; 
lean_dec_ref(v___y_3356_);
v_a_3401_ = lean_ctor_get(v___y_3359_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___y_3359_, 1);
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3357_;
v_a_3348_ = v_a_3401_;
goto v___jp_3341_;
}
}
v___jp_3402_:
{
lean_object* v___x_3409_; 
lean_inc_ref(v___x_3321_);
v___x_3409_ = l_Lean_Meta_mkDecide(v___x_3321_, v___y_3406_, v___y_3404_, v___y_3408_, v___y_3403_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3411_; uint8_t v_transparency_3412_; uint8_t v___x_3413_; uint8_t v___x_3414_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3409_, 1);
v___x_3411_ = l_Lean_Meta_Context_config(v___y_3406_);
v_transparency_3412_ = lean_ctor_get_uint8(v___x_3411_, 9);
lean_dec_ref(v___x_3411_);
v___x_3413_ = 1;
v___x_3414_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v_keyedConfig_3415_; uint8_t v_trackZetaDelta_3416_; lean_object* v_zetaDeltaSet_3417_; lean_object* v_lctx_3418_; lean_object* v_localInstances_3419_; lean_object* v_defEqCtx_x3f_3420_; lean_object* v_synthPendingDepth_3421_; lean_object* v_customCanUnfoldPredicate_x3f_3422_; uint8_t v_univApprox_3423_; uint8_t v_inTypeClassResolution_3424_; uint8_t v_cacheInferType_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_keyedConfig_3415_ = lean_ctor_get(v___y_3406_, 0);
v_trackZetaDelta_3416_ = lean_ctor_get_uint8(v___y_3406_, sizeof(void*)*7);
v_zetaDeltaSet_3417_ = lean_ctor_get(v___y_3406_, 1);
v_lctx_3418_ = lean_ctor_get(v___y_3406_, 2);
v_localInstances_3419_ = lean_ctor_get(v___y_3406_, 3);
v_defEqCtx_x3f_3420_ = lean_ctor_get(v___y_3406_, 4);
v_synthPendingDepth_3421_ = lean_ctor_get(v___y_3406_, 5);
v_customCanUnfoldPredicate_x3f_3422_ = lean_ctor_get(v___y_3406_, 6);
v_univApprox_3423_ = lean_ctor_get_uint8(v___y_3406_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3424_ = lean_ctor_get_uint8(v___y_3406_, sizeof(void*)*7 + 2);
v_cacheInferType_3425_ = lean_ctor_get_uint8(v___y_3406_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3415_);
v___x_3426_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3413_, v_keyedConfig_3415_);
lean_inc(v_customCanUnfoldPredicate_x3f_3422_);
lean_inc(v_synthPendingDepth_3421_);
lean_inc(v_defEqCtx_x3f_3420_);
lean_inc_ref(v_localInstances_3419_);
lean_inc_ref(v_lctx_3418_);
lean_inc(v_zetaDeltaSet_3417_);
v___x_3427_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v_zetaDeltaSet_3417_);
lean_ctor_set(v___x_3427_, 2, v_lctx_3418_);
lean_ctor_set(v___x_3427_, 3, v_localInstances_3419_);
lean_ctor_set(v___x_3427_, 4, v_defEqCtx_x3f_3420_);
lean_ctor_set(v___x_3427_, 5, v_synthPendingDepth_3421_);
lean_ctor_set(v___x_3427_, 6, v_customCanUnfoldPredicate_x3f_3422_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*7, v_trackZetaDelta_3416_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*7 + 1, v_univApprox_3423_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3424_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*7 + 3, v_cacheInferType_3425_);
lean_inc(v___y_3403_);
lean_inc_ref(v___y_3408_);
lean_inc(v___y_3404_);
lean_inc(v_a_3410_);
v___x_3428_ = lean_whnf(v_a_3410_, v___x_3427_, v___y_3404_, v___y_3408_, v___y_3403_);
v___y_3352_ = v___y_3403_;
v___y_3353_ = v___y_3404_;
v___y_3354_ = v___y_3405_;
v___y_3355_ = v___y_3406_;
v___y_3356_ = v_a_3410_;
v___y_3357_ = v___y_3407_;
v___y_3358_ = v___y_3408_;
v___y_3359_ = v___x_3428_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3429_; 
lean_inc(v___y_3403_);
lean_inc_ref(v___y_3408_);
lean_inc(v___y_3404_);
lean_inc_ref(v___y_3406_);
lean_inc(v_a_3410_);
v___x_3429_ = lean_whnf(v_a_3410_, v___y_3406_, v___y_3404_, v___y_3408_, v___y_3403_);
v___y_3352_ = v___y_3403_;
v___y_3353_ = v___y_3404_;
v___y_3354_ = v___y_3405_;
v___y_3355_ = v___y_3406_;
v___y_3356_ = v_a_3410_;
v___y_3357_ = v___y_3407_;
v___y_3358_ = v___y_3408_;
v___y_3359_ = v___x_3429_;
goto v___jp_3351_;
}
}
else
{
lean_object* v_a_3430_; 
v_a_3430_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3409_, 1);
v___y_3342_ = v___y_3403_;
v___y_3343_ = v___y_3404_;
v___y_3344_ = v___y_3405_;
v___y_3345_ = v___y_3406_;
v___y_3346_ = v___y_3408_;
v___y_3347_ = v___y_3407_;
v_a_3348_ = v_a_3430_;
goto v___jp_3341_;
}
}
v___jp_3431_:
{
if (v___y_3438_ == 0)
{
v___y_3323_ = v___y_3434_;
v___y_3324_ = v___y_3436_;
v___y_3325_ = v___y_3435_;
v___y_3326_ = v___y_3433_;
v___y_3327_ = v___y_3437_;
v___y_3328_ = v___y_3432_;
goto v___jp_3322_;
}
else
{
v___y_3403_ = v___y_3432_;
v___y_3404_ = v___y_3433_;
v___y_3405_ = v___y_3434_;
v___y_3406_ = v___y_3435_;
v___y_3407_ = v___y_3436_;
v___y_3408_ = v___y_3437_;
goto v___jp_3402_;
}
}
v___jp_3439_:
{
if (v___y_3447_ == 0)
{
lean_dec_ref(v___y_3440_);
v___y_3432_ = v___y_3441_;
v___y_3433_ = v___y_3442_;
v___y_3434_ = v___y_3443_;
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3446_;
v___y_3437_ = v___y_3445_;
v___y_3438_ = v___x_3276_;
goto v___jp_3431_;
}
else
{
uint8_t v___x_3448_; 
v___x_3448_ = l_Lean_Expr_hasFVar(v___y_3440_);
lean_dec_ref(v___y_3440_);
if (v___x_3448_ == 0)
{
v___y_3403_ = v___y_3441_;
v___y_3404_ = v___y_3442_;
v___y_3405_ = v___y_3443_;
v___y_3406_ = v___y_3444_;
v___y_3407_ = v___y_3446_;
v___y_3408_ = v___y_3445_;
goto v___jp_3402_;
}
else
{
v___y_3432_ = v___y_3441_;
v___y_3433_ = v___y_3442_;
v___y_3434_ = v___y_3443_;
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3446_;
v___y_3437_ = v___y_3445_;
v___y_3438_ = v___x_3276_;
goto v___jp_3431_;
}
}
}
v___jp_3449_:
{
lean_object* v___x_3457_; 
lean_inc_ref(v___x_3321_);
v___x_3457_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3321_, v___y_3451_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; uint8_t v___x_3459_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = l_Lean_Expr_hasMVar(v_a_3458_);
if (v___x_3459_ == 0)
{
v___y_3440_ = v_a_3458_;
v___y_3441_ = v___y_3450_;
v___y_3442_ = v___y_3451_;
v___y_3443_ = v___y_3452_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3454_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___y_3456_;
goto v___jp_3439_;
}
else
{
v___y_3440_ = v_a_3458_;
v___y_3441_ = v___y_3450_;
v___y_3442_ = v___y_3451_;
v___y_3443_ = v___y_3452_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3454_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___x_3276_;
goto v___jp_3439_;
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v___x_3321_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3460_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3457_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3457_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
v___jp_3468_:
{
if (v___y_3475_ == 0)
{
v___y_3323_ = v___y_3471_;
v___y_3324_ = v___y_3473_;
v___y_3325_ = v___y_3472_;
v___y_3326_ = v___y_3470_;
v___y_3327_ = v___y_3474_;
v___y_3328_ = v___y_3469_;
goto v___jp_3322_;
}
else
{
v___y_3450_ = v___y_3469_;
v___y_3451_ = v___y_3470_;
v___y_3452_ = v___y_3471_;
v___y_3453_ = v___y_3472_;
v___y_3454_ = v___y_3474_;
v___y_3455_ = v___y_3473_;
v___y_3456_ = v___y_3475_;
goto v___jp_3449_;
}
}
v___jp_3476_:
{
uint8_t v_useDecide_3483_; 
v_useDecide_3483_ = lean_ctor_get_uint8(v_config_3169_, sizeof(void*)*1);
if (v_useDecide_3483_ == 0)
{
v___y_3469_ = v___y_3482_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3477_;
v___y_3472_ = v___y_3479_;
v___y_3473_ = v_isHEq_3478_;
v___y_3474_ = v___y_3481_;
v___y_3475_ = v___x_3276_;
goto v___jp_3468_;
}
else
{
uint8_t v___x_3484_; 
v___x_3484_ = l_Lean_Expr_hasFVar(v___x_3321_);
if (v___x_3484_ == 0)
{
v___y_3450_ = v___y_3482_;
v___y_3451_ = v___y_3480_;
v___y_3452_ = v___y_3477_;
v___y_3453_ = v___y_3479_;
v___y_3454_ = v___y_3481_;
v___y_3455_ = v_isHEq_3478_;
v___y_3456_ = v_useDecide_3483_;
goto v___jp_3449_;
}
else
{
v___y_3469_ = v___y_3482_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3477_;
v___y_3472_ = v___y_3479_;
v___y_3473_ = v_isHEq_3478_;
v___y_3474_ = v___y_3481_;
v___y_3475_ = v___x_3276_;
goto v___jp_3468_;
}
}
}
v___jp_3485_:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_Meta_isExprDefEq(v___y_3487_, v___y_3488_, v___y_3490_, v___y_3486_, v___y_3492_, v___y_3491_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; uint8_t v___x_3495_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___x_3495_ = lean_unbox(v_a_3494_);
lean_dec(v_a_3494_);
if (v___x_3495_ == 0)
{
v___y_3477_ = v___y_3489_;
v_isHEq_3478_ = v___x_3180_;
v___y_3479_ = v___y_3490_;
v___y_3480_ = v___y_3486_;
v___y_3481_ = v___y_3492_;
v___y_3482_ = v___y_3491_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3496_; 
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_config_3169_);
lean_inc(v_mvarId_3170_);
v___x_3496_ = l_Lean_MVarId_getType(v_mvarId_3170_, v___y_3490_, v___y_3486_, v___y_3492_, v___y_3491_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v___x_3498_ = l_Lean_LocalDecl_toExpr(v_val_3201_);
v___x_3499_ = l_Lean_Meta_mkEqOfHEq(v___x_3498_, v___x_3180_, v___y_3490_, v___y_3486_, v___y_3492_, v___y_3491_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___x_3501_ = l_Lean_Meta_mkNoConfusion(v_a_3497_, v_a_3500_, v___y_3490_, v___y_3486_, v___y_3492_, v___y_3491_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3170_, v_a_3502_, v___y_3486_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_dec_ref_known(v___x_3503_, 1);
v___x_3504_ = lean_box(v___x_3180_);
v___x_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
lean_ctor_set(v___x_3506_, 1, v___x_3205_);
v___x_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
v_a_3187_ = v___x_3507_;
goto v___jp_3186_;
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
v_a_3508_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3503_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3503_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3516_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3501_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3501_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec(v_a_3497_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3524_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3499_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3499_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3532_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3496_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3496_);
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
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v___x_3321_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3540_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3493_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3493_);
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
v___jp_3548_:
{
lean_object* v___x_3554_; 
lean_inc_ref(v___x_3321_);
v___x_3554_ = l_Lean_Meta_matchHEq_x3f(v___x_3321_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
if (lean_obj_tag(v_a_3555_) == 1)
{
lean_object* v_val_3556_; lean_object* v_snd_3557_; lean_object* v_snd_3558_; lean_object* v_fst_3559_; lean_object* v_fst_3560_; lean_object* v_fst_3561_; lean_object* v_snd_3562_; lean_object* v___x_3563_; 
v_val_3556_ = lean_ctor_get(v_a_3555_, 0);
lean_inc(v_val_3556_);
lean_dec_ref_known(v_a_3555_, 1);
v_snd_3557_ = lean_ctor_get(v_val_3556_, 1);
lean_inc(v_snd_3557_);
v_snd_3558_ = lean_ctor_get(v_snd_3557_, 1);
lean_inc(v_snd_3558_);
v_fst_3559_ = lean_ctor_get(v_val_3556_, 0);
lean_inc(v_fst_3559_);
lean_dec(v_val_3556_);
v_fst_3560_ = lean_ctor_get(v_snd_3557_, 0);
lean_inc(v_fst_3560_);
lean_dec(v_snd_3557_);
v_fst_3561_ = lean_ctor_get(v_snd_3558_, 0);
lean_inc(v_fst_3561_);
v_snd_3562_ = lean_ctor_get(v_snd_3558_, 1);
lean_inc(v_snd_3562_);
lean_dec(v_snd_3558_);
v___x_3563_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3560_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3563_, 1);
if (lean_obj_tag(v_a_3564_) == 1)
{
lean_object* v_val_3565_; lean_object* v___x_3566_; 
v_val_3565_ = lean_ctor_get(v_a_3564_, 0);
lean_inc(v_val_3565_);
lean_dec_ref_known(v_a_3564_, 1);
v___x_3566_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3562_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3566_, 1);
if (lean_obj_tag(v_a_3567_) == 1)
{
lean_object* v_toConstantVal_3568_; lean_object* v_val_3569_; lean_object* v_toConstantVal_3570_; lean_object* v_name_3571_; lean_object* v_name_3572_; uint8_t v___x_3573_; 
v_toConstantVal_3568_ = lean_ctor_get(v_val_3565_, 0);
lean_inc_ref(v_toConstantVal_3568_);
lean_dec(v_val_3565_);
v_val_3569_ = lean_ctor_get(v_a_3567_, 0);
lean_inc(v_val_3569_);
lean_dec_ref_known(v_a_3567_, 1);
v_toConstantVal_3570_ = lean_ctor_get(v_val_3569_, 0);
lean_inc_ref(v_toConstantVal_3570_);
lean_dec(v_val_3569_);
v_name_3571_ = lean_ctor_get(v_toConstantVal_3568_, 0);
lean_inc(v_name_3571_);
lean_dec_ref(v_toConstantVal_3568_);
v_name_3572_ = lean_ctor_get(v_toConstantVal_3570_, 0);
lean_inc(v_name_3572_);
lean_dec_ref(v_toConstantVal_3570_);
v___x_3573_ = lean_name_eq(v_name_3571_, v_name_3572_);
lean_dec(v_name_3572_);
lean_dec(v_name_3571_);
if (v___x_3573_ == 0)
{
v___y_3486_ = v___y_3551_;
v___y_3487_ = v_fst_3559_;
v___y_3488_ = v_fst_3561_;
v___y_3489_ = v_isEq_3549_;
v___y_3490_ = v___y_3550_;
v___y_3491_ = v___y_3553_;
v___y_3492_ = v___y_3552_;
goto v___jp_3485_;
}
else
{
if (v___x_3276_ == 0)
{
lean_dec(v_fst_3561_);
lean_dec(v_fst_3559_);
v___y_3477_ = v_isEq_3549_;
v_isHEq_3478_ = v___x_3180_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
v___y_3482_ = v___y_3553_;
goto v___jp_3476_;
}
else
{
v___y_3486_ = v___y_3551_;
v___y_3487_ = v_fst_3559_;
v___y_3488_ = v_fst_3561_;
v___y_3489_ = v_isEq_3549_;
v___y_3490_ = v___y_3550_;
v___y_3491_ = v___y_3553_;
v___y_3492_ = v___y_3552_;
goto v___jp_3485_;
}
}
}
else
{
lean_dec(v_a_3567_);
lean_dec(v_val_3565_);
lean_dec(v_fst_3561_);
lean_dec(v_fst_3559_);
v___y_3477_ = v_isEq_3549_;
v_isHEq_3478_ = v___x_3180_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
v___y_3482_ = v___y_3553_;
goto v___jp_3476_;
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec(v_val_3565_);
lean_dec(v_fst_3561_);
lean_dec(v_fst_3559_);
lean_dec_ref(v___x_3321_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3574_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3566_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3566_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_dec(v_a_3564_);
lean_dec(v_snd_3562_);
lean_dec(v_fst_3561_);
lean_dec(v_fst_3559_);
v___y_3477_ = v_isEq_3549_;
v_isHEq_3478_ = v___x_3180_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
v___y_3482_ = v___y_3553_;
goto v___jp_3476_;
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v_snd_3562_);
lean_dec(v_fst_3561_);
lean_dec(v_fst_3559_);
lean_dec_ref(v___x_3321_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3582_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3563_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3563_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
lean_dec(v_a_3555_);
v___y_3477_ = v_isEq_3549_;
v_isHEq_3478_ = v___x_3276_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
v___y_3482_ = v___y_3553_;
goto v___jp_3476_;
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v___x_3321_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3590_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3554_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3554_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
v___jp_3598_:
{
lean_object* v___x_3603_; 
lean_inc_ref(v___x_3321_);
v___x_3603_ = l_Lean_Meta_matchEq_x3f(v___x_3321_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
if (lean_obj_tag(v_a_3604_) == 1)
{
lean_object* v_val_3605_; lean_object* v_snd_3606_; lean_object* v_fst_3607_; lean_object* v_snd_3608_; lean_object* v___x_3609_; 
v_val_3605_ = lean_ctor_get(v_a_3604_, 0);
lean_inc(v_val_3605_);
lean_dec_ref_known(v_a_3604_, 1);
v_snd_3606_ = lean_ctor_get(v_val_3605_, 1);
lean_inc(v_snd_3606_);
lean_dec(v_val_3605_);
v_fst_3607_ = lean_ctor_get(v_snd_3606_, 0);
lean_inc(v_fst_3607_);
v_snd_3608_ = lean_ctor_get(v_snd_3606_, 1);
lean_inc(v_snd_3608_);
lean_dec(v_snd_3606_);
v___x_3609_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3607_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
if (lean_obj_tag(v_a_3610_) == 1)
{
lean_object* v_val_3611_; lean_object* v___x_3612_; 
v_val_3611_ = lean_ctor_get(v_a_3610_, 0);
lean_inc(v_val_3611_);
lean_dec_ref_known(v_a_3610_, 1);
v___x_3612_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3608_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
if (lean_obj_tag(v_a_3613_) == 1)
{
lean_object* v_toConstantVal_3614_; lean_object* v_val_3615_; lean_object* v_toConstantVal_3616_; lean_object* v_name_3617_; lean_object* v_name_3618_; uint8_t v___x_3619_; 
v_toConstantVal_3614_ = lean_ctor_get(v_val_3611_, 0);
lean_inc_ref(v_toConstantVal_3614_);
lean_dec(v_val_3611_);
v_val_3615_ = lean_ctor_get(v_a_3613_, 0);
lean_inc(v_val_3615_);
lean_dec_ref_known(v_a_3613_, 1);
v_toConstantVal_3616_ = lean_ctor_get(v_val_3615_, 0);
lean_inc_ref(v_toConstantVal_3616_);
lean_dec(v_val_3615_);
v_name_3617_ = lean_ctor_get(v_toConstantVal_3614_, 0);
lean_inc(v_name_3617_);
lean_dec_ref(v_toConstantVal_3614_);
v_name_3618_ = lean_ctor_get(v_toConstantVal_3616_, 0);
lean_inc(v_name_3618_);
lean_dec_ref(v_toConstantVal_3616_);
v___x_3619_ = lean_name_eq(v_name_3617_, v_name_3618_);
lean_dec(v_name_3618_);
lean_dec(v_name_3617_);
if (v___x_3619_ == 0)
{
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_config_3169_);
v___y_3207_ = v___y_3601_;
v___y_3208_ = v___y_3602_;
v___y_3209_ = v___y_3599_;
v___y_3210_ = v___y_3600_;
goto v___jp_3206_;
}
else
{
if (v___x_3276_ == 0)
{
lean_del_object(v___x_3203_);
v_isEq_3549_ = v___x_3180_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3602_;
goto v___jp_3548_;
}
else
{
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_config_3169_);
v___y_3207_ = v___y_3601_;
v___y_3208_ = v___y_3602_;
v___y_3209_ = v___y_3599_;
v___y_3210_ = v___y_3600_;
goto v___jp_3206_;
}
}
}
else
{
lean_dec(v_a_3613_);
lean_dec(v_val_3611_);
lean_del_object(v___x_3203_);
v_isEq_3549_ = v___x_3180_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3602_;
goto v___jp_3548_;
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v_val_3611_);
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3620_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3612_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3612_);
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
lean_dec(v_a_3610_);
lean_dec(v_snd_3608_);
lean_del_object(v___x_3203_);
v_isEq_3549_ = v___x_3180_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3602_;
goto v___jp_3548_;
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec(v_snd_3608_);
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3628_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3609_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3609_);
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
else
{
lean_dec(v_a_3604_);
lean_del_object(v___x_3203_);
v_isEq_3549_ = v___x_3276_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3602_;
goto v___jp_3548_;
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3636_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3603_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3603_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
v___jp_3644_:
{
lean_object* v___x_3649_; 
lean_inc_ref(v___x_3321_);
v___x_3649_ = l_Lean_refutableHasNotBit_x3f(v___x_3321_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
if (lean_obj_tag(v_a_3650_) == 1)
{
lean_object* v_val_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3691_; 
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec_ref(v_config_3169_);
v_val_3651_ = lean_ctor_get(v_a_3650_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3653_ = v_a_3650_;
v_isShared_3654_ = v_isSharedCheck_3691_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_val_3651_);
lean_dec(v_a_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3691_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; 
lean_inc(v_mvarId_3170_);
v___x_3655_ = l_Lean_MVarId_getType(v_mvarId_3170_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
v___x_3657_ = l_Lean_LocalDecl_toExpr(v_val_3201_);
v___x_3658_ = l_Lean_Meta_mkAbsurd(v_a_3656_, v_val_3651_, v___x_3657_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3660_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref_known(v___x_3658_, 1);
v___x_3660_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3170_, v_a_3659_, v___y_3646_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3663_; 
lean_dec_ref_known(v___x_3660_, 1);
v___x_3661_ = lean_box(v___x_3180_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3661_);
v___x_3663_ = v___x_3653_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
lean_ctor_set(v___x_3664_, 1, v___x_3205_);
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
v_a_3187_ = v___x_3665_;
goto v___jp_3186_;
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_del_object(v___x_3653_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
v_a_3667_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3660_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3660_);
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
lean_del_object(v___x_3653_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3675_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3658_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3658_);
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
lean_del_object(v___x_3653_);
lean_dec(v_val_3651_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3683_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3655_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3655_);
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
}
else
{
lean_object* v___x_3692_; 
lean_dec(v_a_3650_);
lean_inc_ref(v___x_3321_);
v___x_3692_ = l_Lean_Meta_matchNe_x3f(v___x_3321_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
if (lean_obj_tag(v_a_3693_) == 1)
{
lean_object* v_val_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3764_; 
v_val_3694_ = lean_ctor_get(v_a_3693_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_a_3693_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3696_ = v_a_3693_;
v_isShared_3697_ = v_isSharedCheck_3764_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_val_3694_);
lean_dec(v_a_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3764_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v_snd_3698_; lean_object* v_fst_3699_; lean_object* v_snd_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3763_; 
v_snd_3698_ = lean_ctor_get(v_val_3694_, 1);
lean_inc(v_snd_3698_);
lean_dec(v_val_3694_);
v_fst_3699_ = lean_ctor_get(v_snd_3698_, 0);
v_snd_3700_ = lean_ctor_get(v_snd_3698_, 1);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_snd_3698_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3702_ = v_snd_3698_;
v_isShared_3703_ = v_isSharedCheck_3763_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_snd_3700_);
lean_inc(v_fst_3699_);
lean_dec(v_snd_3698_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3763_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3704_; 
lean_inc(v_fst_3699_);
v___x_3704_ = l_Lean_Meta_isExprDefEq(v_fst_3699_, v_snd_3700_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; uint8_t v___x_3706_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___x_3706_ = lean_unbox(v_a_3705_);
lean_dec(v_a_3705_);
if (v___x_3706_ == 0)
{
lean_del_object(v___x_3702_);
lean_dec(v_fst_3699_);
lean_del_object(v___x_3696_);
v___y_3599_ = v___y_3645_;
v___y_3600_ = v___y_3646_;
v___y_3601_ = v___y_3647_;
v___y_3602_ = v___y_3648_;
goto v___jp_3598_;
}
else
{
lean_object* v___x_3707_; 
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec_ref(v_config_3169_);
lean_inc(v_mvarId_3170_);
v___x_3707_ = l_Lean_MVarId_getType(v_mvarId_3170_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3709_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v___x_3709_ = l_Lean_Meta_mkEqRefl(v_fst_3699_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3709_, 1);
v___x_3711_ = l_Lean_LocalDecl_toExpr(v_val_3201_);
v___x_3712_ = l_Lean_Meta_mkAbsurd(v_a_3708_, v_a_3710_, v___x_3711_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v___x_3714_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3170_, v_a_3713_, v___y_3646_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v___x_3715_; lean_object* v___x_3717_; 
lean_dec_ref_known(v___x_3714_, 1);
v___x_3715_ = lean_box(v___x_3180_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3715_);
v___x_3717_ = v___x_3696_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3719_; 
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 1, v___x_3205_);
lean_ctor_set(v___x_3702_, 0, v___x_3717_);
v___x_3719_ = v___x_3702_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v___x_3205_);
v___x_3719_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
v_a_3187_ = v___x_3720_;
goto v___jp_3186_;
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_del_object(v___x_3702_);
lean_del_object(v___x_3696_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
v_a_3723_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3714_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3714_);
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
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_del_object(v___x_3702_);
lean_del_object(v___x_3696_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3731_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3712_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3712_);
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
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec(v_a_3708_);
lean_del_object(v___x_3702_);
lean_del_object(v___x_3696_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3739_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3709_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3709_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_del_object(v___x_3702_);
lean_dec(v_fst_3699_);
lean_del_object(v___x_3696_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3747_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3707_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3707_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_del_object(v___x_3702_);
lean_dec(v_fst_3699_);
lean_del_object(v___x_3696_);
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3755_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3704_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3704_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3693_);
v___y_3599_ = v___y_3645_;
v___y_3600_ = v___y_3646_;
v___y_3601_ = v___y_3647_;
v___y_3602_ = v___y_3648_;
goto v___jp_3598_;
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3765_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3692_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3692_);
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
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec_ref(v___x_3321_);
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3773_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3649_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3649_);
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
}
else
{
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
v_a_3195_ = v___x_3247_;
goto v___jp_3194_;
}
v___jp_3206_:
{
lean_object* v___x_3211_; 
lean_inc(v_mvarId_3170_);
v___x_3211_ = l_Lean_MVarId_getType(v_mvarId_3170_, v___y_3209_, v___y_3210_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v___x_3213_ = l_Lean_LocalDecl_toExpr(v_val_3201_);
v___x_3214_ = l_Lean_Meta_mkNoConfusion(v_a_3212_, v___x_3213_, v___y_3209_, v___y_3210_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3216_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3214_, 1);
v___x_3216_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3170_, v_a_3215_, v___y_3210_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
lean_dec_ref_known(v___x_3216_, 1);
v___x_3217_ = lean_box(v___x_3180_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3217_);
v___x_3219_ = v___x_3203_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_ctor_set(v___x_3220_, 1, v___x_3205_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
v_a_3187_ = v___x_3221_;
goto v___jp_3186_;
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_del_object(v___x_3203_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
v_a_3223_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3216_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3216_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
lean_del_object(v___x_3203_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3231_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3214_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3214_);
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
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_del_object(v___x_3203_);
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
v_a_3239_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3211_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3211_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
v___jp_3248_:
{
lean_object* v_searchFuel_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v_searchFuel_3253_ = lean_ctor_get(v_config_3169_, 0);
v___x_3254_ = l_Lean_LocalDecl_fvarId(v_val_3201_);
lean_dec(v_val_3201_);
lean_inc(v_searchFuel_3253_);
lean_inc(v_mvarId_3170_);
v___x_3255_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3170_, v___x_3254_, v_searchFuel_3253_, v___y_3251_, v___y_3249_, v___y_3252_, v___y_3250_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; uint8_t v___x_3257_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
v___x_3257_ = lean_unbox(v_a_3256_);
lean_dec(v_a_3256_);
if (v___x_3257_ == 0)
{
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
v_a_3195_ = v___x_3247_;
goto v___jp_3194_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v___x_3258_ = lean_box(v___x_3180_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v___x_3205_);
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
v_a_3187_ = v___x_3261_;
goto v___jp_3186_;
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3262_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3255_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3255_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
v___jp_3270_:
{
if (v___y_3275_ == 0)
{
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
v_a_3195_ = v___x_3247_;
goto v___jp_3194_;
}
else
{
v___y_3249_ = v___y_3271_;
v___y_3250_ = v___y_3272_;
v___y_3251_ = v___y_3273_;
v___y_3252_ = v___y_3274_;
goto v___jp_3248_;
}
}
v___jp_3277_:
{
if (v___y_3282_ == 0)
{
v___y_3249_ = v___y_3278_;
v___y_3250_ = v___y_3279_;
v___y_3251_ = v___y_3280_;
v___y_3252_ = v___y_3281_;
goto v___jp_3248_;
}
else
{
v___y_3271_ = v___y_3278_;
v___y_3272_ = v___y_3279_;
v___y_3273_ = v___y_3280_;
v___y_3274_ = v___y_3281_;
v___y_3275_ = v___x_3276_;
goto v___jp_3270_;
}
}
v___jp_3283_:
{
if (v___y_3289_ == 0)
{
v___y_3271_ = v___y_3284_;
v___y_3272_ = v___y_3285_;
v___y_3273_ = v___y_3286_;
v___y_3274_ = v___y_3287_;
v___y_3275_ = v___x_3276_;
goto v___jp_3270_;
}
else
{
v___y_3278_ = v___y_3284_;
v___y_3279_ = v___y_3285_;
v___y_3280_ = v___y_3286_;
v___y_3281_ = v___y_3287_;
v___y_3282_ = v___y_3288_;
goto v___jp_3277_;
}
}
v___jp_3290_:
{
uint8_t v_emptyType_3297_; 
v_emptyType_3297_ = lean_ctor_get_uint8(v_config_3169_, sizeof(void*)*1 + 1);
if (v_emptyType_3297_ == 0)
{
v___y_3284_ = v___y_3294_;
v___y_3285_ = v___y_3296_;
v___y_3286_ = v___y_3293_;
v___y_3287_ = v___y_3295_;
v___y_3288_ = v___y_3292_;
v___y_3289_ = v___x_3276_;
goto v___jp_3283_;
}
else
{
if (v___y_3291_ == 0)
{
v___y_3278_ = v___y_3294_;
v___y_3279_ = v___y_3296_;
v___y_3280_ = v___y_3293_;
v___y_3281_ = v___y_3295_;
v___y_3282_ = v___y_3292_;
goto v___jp_3277_;
}
else
{
v___y_3284_ = v___y_3294_;
v___y_3285_ = v___y_3296_;
v___y_3286_ = v___y_3293_;
v___y_3287_ = v___y_3295_;
v___y_3288_ = v___y_3292_;
v___y_3289_ = v___x_3276_;
goto v___jp_3283_;
}
}
}
v___jp_3298_:
{
if (v___y_3305_ == 0)
{
v___y_3291_ = v___y_3300_;
v___y_3292_ = v___y_3304_;
v___y_3293_ = v___y_3303_;
v___y_3294_ = v___y_3302_;
v___y_3295_ = v___y_3299_;
v___y_3296_ = v___y_3301_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3306_; 
lean_inc(v_val_3201_);
lean_inc(v_mvarId_3170_);
v___x_3306_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3170_, v_val_3201_, v___y_3303_, v___y_3302_, v___y_3299_, v___y_3301_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; uint8_t v___x_3308_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = lean_unbox(v_a_3307_);
lean_dec(v_a_3307_);
if (v___x_3308_ == 0)
{
v___y_3291_ = v___y_3300_;
v___y_3292_ = v___y_3304_;
v___y_3293_ = v___y_3303_;
v___y_3294_ = v___y_3302_;
v___y_3295_ = v___y_3299_;
v___y_3296_ = v___y_3301_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
lean_dec(v_val_3201_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v___x_3309_ = lean_box(v___x_3180_);
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v___x_3205_);
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
v_a_3187_ = v___x_3312_;
goto v___jp_3186_;
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec(v_val_3201_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3182_);
lean_dec(v_mvarId_3170_);
lean_dec_ref(v_config_3169_);
v_a_3313_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3306_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3306_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
}
}
v___jp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3188_, 0, v_a_3187_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v___x_3188_);
v___x_3190_ = v___x_3184_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_snd_3182_);
v___x_3190_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
v___jp_3194_:
{
lean_object* v___x_3196_; size_t v___x_3197_; size_t v___x_3198_; 
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3193_);
lean_ctor_set(v___x_3196_, 1, v_a_3195_);
v___x_3197_ = ((size_t)1ULL);
v___x_3198_ = lean_usize_add(v_i_3173_, v___x_3197_);
v_i_3173_ = v___x_3198_;
v_b_3174_ = v___x_3196_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3854_, lean_object* v_mvarId_3855_, lean_object* v_as_3856_, lean_object* v_sz_3857_, lean_object* v_i_3858_, lean_object* v_b_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
size_t v_sz_boxed_3865_; size_t v_i_boxed_3866_; lean_object* v_res_3867_; 
v_sz_boxed_3865_ = lean_unbox_usize(v_sz_3857_);
lean_dec(v_sz_3857_);
v_i_boxed_3866_ = lean_unbox_usize(v_i_3858_);
lean_dec(v_i_3858_);
v_res_3867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3854_, v_mvarId_3855_, v_as_3856_, v_sz_boxed_3865_, v_i_boxed_3866_, v_b_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec_ref(v_as_3856_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3868_, lean_object* v_mvarId_3869_, lean_object* v_as_3870_, size_t v_sz_3871_, size_t v_i_3872_, lean_object* v_b_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
uint8_t v___x_3879_; 
v___x_3879_ = lean_usize_dec_lt(v_i_3872_, v_sz_3871_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; 
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v___x_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3880_, 0, v_b_3873_);
return v___x_3880_;
}
else
{
lean_object* v_snd_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_4551_; 
v_snd_3881_ = lean_ctor_get(v_b_3873_, 1);
v_isSharedCheck_4551_ = !lean_is_exclusive(v_b_3873_);
if (v_isSharedCheck_4551_ == 0)
{
lean_object* v_unused_4552_; 
v_unused_4552_ = lean_ctor_get(v_b_3873_, 0);
lean_dec(v_unused_4552_);
v___x_3883_ = v_b_3873_;
v_isShared_3884_ = v_isSharedCheck_4551_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_snd_3881_);
lean_dec(v_b_3873_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_4551_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v_a_3886_; lean_object* v___x_3892_; lean_object* v_a_3894_; lean_object* v_a_3899_; 
v___x_3892_ = lean_box(0);
v_a_3899_ = lean_array_uget(v_as_3870_, v_i_3872_);
if (lean_obj_tag(v_a_3899_) == 0)
{
lean_del_object(v___x_3883_);
v_a_3894_ = v_snd_3881_;
goto v___jp_3893_;
}
else
{
lean_object* v_val_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_4550_; 
v_val_3900_ = lean_ctor_get(v_a_3899_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_a_3899_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_3902_ = v_a_3899_;
v_isShared_3903_ = v_isSharedCheck_4550_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_val_3900_);
lean_dec(v_a_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_4550_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3904_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___x_3946_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; uint8_t v___y_3974_; uint8_t v___x_3975_; lean_object* v___y_3977_; lean_object* v___y_3978_; uint8_t v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; uint8_t v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; uint8_t v___y_3988_; uint8_t v___y_3990_; uint8_t v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; uint8_t v___y_4002_; uint8_t v___y_4003_; uint8_t v___y_4004_; 
v___x_3904_ = lean_box(0);
v___x_3946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3975_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3900_);
if (v___x_3975_ == 0)
{
lean_object* v___x_4020_; uint8_t v___y_4022_; uint8_t v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4031_; lean_object* v___y_4032_; uint8_t v___y_4033_; lean_object* v___y_4034_; uint8_t v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; uint8_t v___y_4038_; lean_object* v___y_4041_; lean_object* v___y_4042_; uint8_t v___y_4043_; lean_object* v___y_4044_; uint8_t v___y_4045_; lean_object* v___y_4046_; lean_object* v_a_4047_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; uint8_t v___y_4054_; uint8_t v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4102_; lean_object* v___y_4103_; uint8_t v___y_4104_; uint8_t v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4131_; lean_object* v___y_4132_; uint8_t v___y_4133_; uint8_t v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; uint8_t v___y_4137_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; uint8_t v___y_4142_; lean_object* v___y_4143_; uint8_t v___y_4144_; lean_object* v___y_4145_; uint8_t v___y_4146_; lean_object* v___y_4149_; lean_object* v___y_4150_; uint8_t v___y_4151_; uint8_t v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; uint8_t v___y_4155_; lean_object* v___y_4168_; lean_object* v___y_4169_; uint8_t v___y_4170_; uint8_t v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; uint8_t v___y_4174_; uint8_t v___y_4176_; uint8_t v_isHEq_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; uint8_t v___y_4191_; uint8_t v_isEq_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___x_4480_; 
v___x_4020_ = l_Lean_LocalDecl_type(v_val_3900_);
lean_inc_ref(v___x_4020_);
v___x_4480_ = l_Lean_Meta_matchNot_x3f(v___x_4020_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref_known(v___x_4480_, 1);
if (lean_obj_tag(v_a_4481_) == 1)
{
lean_object* v_val_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4541_; 
v_val_4482_ = lean_ctor_get(v_a_4481_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v_a_4481_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4484_ = v_a_4481_;
v_isShared_4485_ = v_isSharedCheck_4541_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_val_4482_);
lean_dec(v_a_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4541_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4486_; 
v___x_4486_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4482_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
if (lean_obj_tag(v_a_4487_) == 1)
{
lean_object* v_val_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4532_; 
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec_ref(v_config_3868_);
v_val_4488_ = lean_ctor_get(v_a_4487_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v_a_4487_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4490_ = v_a_4487_;
v_isShared_4491_ = v_isSharedCheck_4532_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_val_4488_);
lean_dec(v_a_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4532_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4492_; 
lean_inc(v_mvarId_3869_);
v___x_4492_ = l_Lean_MVarId_getType(v_mvarId_3869_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
lean_inc(v_a_4493_);
lean_dec_ref_known(v___x_4492_, 1);
v___x_4494_ = l_Lean_LocalDecl_toExpr(v_val_3900_);
v___x_4495_ = l_Lean_mkFVar(v_val_4488_);
v___x_4496_ = l_Lean_Expr_app___override(v___x_4494_, v___x_4495_);
v___x_4497_ = l_Lean_Meta_mkFalseElim(v_a_4493_, v___x_4496_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v___x_4499_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref_known(v___x_4497_, 1);
v___x_4499_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3869_, v_a_4498_, v___y_3875_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v___x_4500_; lean_object* v___x_4502_; 
lean_dec_ref_known(v___x_4499_, 1);
v___x_4500_ = lean_box(v___x_3879_);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v___x_4500_);
v___x_4502_ = v___x_4490_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4500_);
v___x_4502_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_4505_; 
v___x_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
lean_ctor_set(v___x_4503_, 1, v___x_3904_);
if (v_isShared_4485_ == 0)
{
lean_ctor_set_tag(v___x_4484_, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4503_);
v___x_4505_ = v___x_4484_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4503_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
v_a_3886_ = v___x_4505_;
goto v___jp_3885_;
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_del_object(v___x_4490_);
lean_del_object(v___x_4484_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
v_a_4508_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4499_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4499_);
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
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_del_object(v___x_4490_);
lean_del_object(v___x_4484_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4516_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4497_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4497_);
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
else
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
lean_del_object(v___x_4490_);
lean_dec(v_val_4488_);
lean_del_object(v___x_4484_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4524_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4492_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4492_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
}
}
}
else
{
lean_dec(v_a_4487_);
lean_del_object(v___x_4484_);
v___y_4344_ = v___y_3874_;
v___y_4345_ = v___y_3875_;
v___y_4346_ = v___y_3876_;
v___y_4347_ = v___y_3877_;
goto v___jp_4343_;
}
}
else
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_del_object(v___x_4484_);
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4533_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4486_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4486_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
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
}
else
{
lean_dec(v_a_4481_);
v___y_4344_ = v___y_3874_;
v___y_4345_ = v___y_3875_;
v___y_4346_ = v___y_3876_;
v___y_4347_ = v___y_3877_;
goto v___jp_4343_;
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4542_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4480_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4480_);
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
v___jp_4021_:
{
uint8_t v_genDiseq_4028_; 
v_genDiseq_4028_ = lean_ctor_get_uint8(v_config_3868_, sizeof(void*)*1 + 2);
if (v_genDiseq_4028_ == 0)
{
lean_dec_ref(v___x_4020_);
v___y_3998_ = v___y_4027_;
v___y_3999_ = v___y_4026_;
v___y_4000_ = v___y_4025_;
v___y_4001_ = v___y_4024_;
v___y_4002_ = v___y_4022_;
v___y_4003_ = v___y_4023_;
v___y_4004_ = v___x_3975_;
goto v___jp_3997_;
}
else
{
uint8_t v___x_4029_; 
v___x_4029_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4020_);
v___y_3998_ = v___y_4027_;
v___y_3999_ = v___y_4026_;
v___y_4000_ = v___y_4025_;
v___y_4001_ = v___y_4024_;
v___y_4002_ = v___y_4022_;
v___y_4003_ = v___y_4023_;
v___y_4004_ = v___x_4029_;
goto v___jp_3997_;
}
}
v___jp_4030_:
{
if (v___y_4038_ == 0)
{
lean_dec_ref(v___y_4034_);
v___y_4022_ = v___y_4033_;
v___y_4023_ = v___y_4035_;
v___y_4024_ = v___y_4032_;
v___y_4025_ = v___y_4036_;
v___y_4026_ = v___y_4037_;
v___y_4027_ = v___y_4031_;
goto v___jp_4021_;
}
else
{
lean_object* v___x_4039_; 
lean_dec_ref(v___x_4020_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v___x_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___y_4034_);
return v___x_4039_;
}
}
v___jp_4040_:
{
uint8_t v___x_4048_; 
v___x_4048_ = l_Lean_Exception_isInterrupt(v_a_4047_);
if (v___x_4048_ == 0)
{
uint8_t v___x_4049_; 
lean_inc_ref(v_a_4047_);
v___x_4049_ = l_Lean_Exception_isRuntime(v_a_4047_);
v___y_4031_ = v___y_4041_;
v___y_4032_ = v___y_4042_;
v___y_4033_ = v___y_4043_;
v___y_4034_ = v_a_4047_;
v___y_4035_ = v___y_4045_;
v___y_4036_ = v___y_4044_;
v___y_4037_ = v___y_4046_;
v___y_4038_ = v___x_4049_;
goto v___jp_4030_;
}
else
{
v___y_4031_ = v___y_4041_;
v___y_4032_ = v___y_4042_;
v___y_4033_ = v___y_4043_;
v___y_4034_ = v_a_4047_;
v___y_4035_ = v___y_4045_;
v___y_4036_ = v___y_4044_;
v___y_4037_ = v___y_4046_;
v___y_4038_ = v___x_4048_;
goto v___jp_4030_;
}
}
v___jp_4050_:
{
if (lean_obj_tag(v___y_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; 
v_a_4059_ = lean_ctor_get(v___y_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___y_4058_, 1);
v___x_4060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4061_ = l_Lean_Expr_isConstOf(v_a_4059_, v___x_4060_);
lean_dec(v_a_4059_);
if (v___x_4061_ == 0)
{
lean_dec_ref(v___y_4052_);
v___y_4022_ = v___y_4054_;
v___y_4023_ = v___y_4055_;
v___y_4024_ = v___y_4053_;
v___y_4025_ = v___y_4056_;
v___y_4026_ = v___y_4057_;
v___y_4027_ = v___y_4051_;
goto v___jp_4021_;
}
else
{
lean_object* v___x_4062_; 
lean_inc_ref(v___y_4052_);
v___x_4062_ = l_Lean_Meta_mkEqRefl(v___y_4052_, v___y_4053_, v___y_4056_, v___y_4057_, v___y_4051_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4064_; lean_object* v_dummy_4065_; lean_object* v_nargs_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
v___x_4064_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4065_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_4066_ = l_Lean_Expr_getAppNumArgs(v___y_4052_);
lean_inc(v_nargs_4066_);
v___x_4067_ = lean_mk_array(v_nargs_4066_, v_dummy_4065_);
v___x_4068_ = lean_unsigned_to_nat(1u);
v___x_4069_ = lean_nat_sub(v_nargs_4066_, v___x_4068_);
lean_dec(v_nargs_4066_);
v___x_4070_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_4052_, v___x_4067_, v___x_4069_);
v___x_4071_ = lean_array_push(v___x_4070_, v_a_4063_);
v___x_4072_ = l_Lean_mkAppN(v___x_4064_, v___x_4071_);
lean_dec_ref(v___x_4071_);
lean_inc(v_mvarId_3869_);
v___x_4073_ = l_Lean_MVarId_getType(v_mvarId_3869_, v___y_4053_, v___y_4056_, v___y_4057_, v___y_4051_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
lean_inc(v_val_3900_);
v___x_4075_ = l_Lean_LocalDecl_toExpr(v_val_3900_);
v___x_4076_ = l_Lean_Meta_mkAbsurd(v_a_4074_, v___x_4075_, v___x_4072_, v___y_4053_, v___y_4056_, v___y_4057_, v___y_4051_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4096_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4096_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4096_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; 
lean_inc(v_mvarId_3869_);
v___x_4081_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3869_, v_a_4077_, v___y_4056_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4093_; 
lean_dec_ref(v___x_4020_);
lean_dec(v_val_3900_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; 
v_unused_4094_ = lean_ctor_get(v___x_4081_, 0);
lean_dec(v_unused_4094_);
v___x_4083_ = v___x_4081_;
v_isShared_4084_ = v_isSharedCheck_4093_;
goto v_resetjp_4082_;
}
else
{
lean_dec(v___x_4081_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4093_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4085_ = lean_box(v___x_3879_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set_tag(v___x_4083_, 1);
lean_ctor_set(v___x_4083_, 0, v___x_4085_);
v___x_4087_ = v___x_4083_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4090_; 
v___x_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
lean_ctor_set(v___x_4088_, 1, v___x_3904_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v___x_4088_);
v___x_4090_ = v___x_4079_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
v_a_3886_ = v___x_4090_;
goto v___jp_3885_;
}
}
}
}
else
{
lean_object* v_a_4095_; 
lean_del_object(v___x_4079_);
v_a_4095_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4081_, 1);
v___y_4041_ = v___y_4051_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4056_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4057_;
v_a_4047_ = v_a_4095_;
goto v___jp_4040_;
}
}
}
else
{
lean_object* v_a_4097_; 
v_a_4097_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4076_, 1);
v___y_4041_ = v___y_4051_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4056_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4057_;
v_a_4047_ = v_a_4097_;
goto v___jp_4040_;
}
}
else
{
lean_object* v_a_4098_; 
lean_dec_ref(v___x_4072_);
v_a_4098_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4073_, 1);
v___y_4041_ = v___y_4051_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4056_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4057_;
v_a_4047_ = v_a_4098_;
goto v___jp_4040_;
}
}
else
{
lean_object* v_a_4099_; 
lean_dec_ref(v___y_4052_);
v_a_4099_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4062_, 1);
v___y_4041_ = v___y_4051_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4056_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4057_;
v_a_4047_ = v_a_4099_;
goto v___jp_4040_;
}
}
}
else
{
lean_object* v_a_4100_; 
lean_dec_ref(v___y_4052_);
v_a_4100_ = lean_ctor_get(v___y_4058_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v___y_4058_, 1);
v___y_4041_ = v___y_4051_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4056_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4057_;
v_a_4047_ = v_a_4100_;
goto v___jp_4040_;
}
}
v___jp_4101_:
{
lean_object* v___x_4108_; 
lean_inc_ref(v___x_4020_);
v___x_4108_ = l_Lean_Meta_mkDecide(v___x_4020_, v___y_4103_, v___y_4106_, v___y_4107_, v___y_4102_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4110_; uint8_t v_transparency_4111_; uint8_t v___x_4112_; uint8_t v___x_4113_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___x_4108_, 1);
v___x_4110_ = l_Lean_Meta_Context_config(v___y_4103_);
v_transparency_4111_ = lean_ctor_get_uint8(v___x_4110_, 9);
lean_dec_ref(v___x_4110_);
v___x_4112_ = 1;
v___x_4113_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4111_, v___x_4112_);
if (v___x_4113_ == 0)
{
lean_object* v_keyedConfig_4114_; uint8_t v_trackZetaDelta_4115_; lean_object* v_zetaDeltaSet_4116_; lean_object* v_lctx_4117_; lean_object* v_localInstances_4118_; lean_object* v_defEqCtx_x3f_4119_; lean_object* v_synthPendingDepth_4120_; lean_object* v_customCanUnfoldPredicate_x3f_4121_; uint8_t v_univApprox_4122_; uint8_t v_inTypeClassResolution_4123_; uint8_t v_cacheInferType_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v_keyedConfig_4114_ = lean_ctor_get(v___y_4103_, 0);
v_trackZetaDelta_4115_ = lean_ctor_get_uint8(v___y_4103_, sizeof(void*)*7);
v_zetaDeltaSet_4116_ = lean_ctor_get(v___y_4103_, 1);
v_lctx_4117_ = lean_ctor_get(v___y_4103_, 2);
v_localInstances_4118_ = lean_ctor_get(v___y_4103_, 3);
v_defEqCtx_x3f_4119_ = lean_ctor_get(v___y_4103_, 4);
v_synthPendingDepth_4120_ = lean_ctor_get(v___y_4103_, 5);
v_customCanUnfoldPredicate_x3f_4121_ = lean_ctor_get(v___y_4103_, 6);
v_univApprox_4122_ = lean_ctor_get_uint8(v___y_4103_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4123_ = lean_ctor_get_uint8(v___y_4103_, sizeof(void*)*7 + 2);
v_cacheInferType_4124_ = lean_ctor_get_uint8(v___y_4103_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4114_);
v___x_4125_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4112_, v_keyedConfig_4114_);
lean_inc(v_customCanUnfoldPredicate_x3f_4121_);
lean_inc(v_synthPendingDepth_4120_);
lean_inc(v_defEqCtx_x3f_4119_);
lean_inc_ref(v_localInstances_4118_);
lean_inc_ref(v_lctx_4117_);
lean_inc(v_zetaDeltaSet_4116_);
v___x_4126_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
lean_ctor_set(v___x_4126_, 1, v_zetaDeltaSet_4116_);
lean_ctor_set(v___x_4126_, 2, v_lctx_4117_);
lean_ctor_set(v___x_4126_, 3, v_localInstances_4118_);
lean_ctor_set(v___x_4126_, 4, v_defEqCtx_x3f_4119_);
lean_ctor_set(v___x_4126_, 5, v_synthPendingDepth_4120_);
lean_ctor_set(v___x_4126_, 6, v_customCanUnfoldPredicate_x3f_4121_);
lean_ctor_set_uint8(v___x_4126_, sizeof(void*)*7, v_trackZetaDelta_4115_);
lean_ctor_set_uint8(v___x_4126_, sizeof(void*)*7 + 1, v_univApprox_4122_);
lean_ctor_set_uint8(v___x_4126_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4123_);
lean_ctor_set_uint8(v___x_4126_, sizeof(void*)*7 + 3, v_cacheInferType_4124_);
lean_inc(v___y_4102_);
lean_inc_ref(v___y_4107_);
lean_inc(v___y_4106_);
lean_inc(v_a_4109_);
v___x_4127_ = lean_whnf(v_a_4109_, v___x_4126_, v___y_4106_, v___y_4107_, v___y_4102_);
v___y_4051_ = v___y_4102_;
v___y_4052_ = v_a_4109_;
v___y_4053_ = v___y_4103_;
v___y_4054_ = v___y_4104_;
v___y_4055_ = v___y_4105_;
v___y_4056_ = v___y_4106_;
v___y_4057_ = v___y_4107_;
v___y_4058_ = v___x_4127_;
goto v___jp_4050_;
}
else
{
lean_object* v___x_4128_; 
lean_inc(v___y_4102_);
lean_inc_ref(v___y_4107_);
lean_inc(v___y_4106_);
lean_inc_ref(v___y_4103_);
lean_inc(v_a_4109_);
v___x_4128_ = lean_whnf(v_a_4109_, v___y_4103_, v___y_4106_, v___y_4107_, v___y_4102_);
v___y_4051_ = v___y_4102_;
v___y_4052_ = v_a_4109_;
v___y_4053_ = v___y_4103_;
v___y_4054_ = v___y_4104_;
v___y_4055_ = v___y_4105_;
v___y_4056_ = v___y_4106_;
v___y_4057_ = v___y_4107_;
v___y_4058_ = v___x_4128_;
goto v___jp_4050_;
}
}
else
{
lean_object* v_a_4129_; 
v_a_4129_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4108_, 1);
v___y_4041_ = v___y_4102_;
v___y_4042_ = v___y_4103_;
v___y_4043_ = v___y_4104_;
v___y_4044_ = v___y_4106_;
v___y_4045_ = v___y_4105_;
v___y_4046_ = v___y_4107_;
v_a_4047_ = v_a_4129_;
goto v___jp_4040_;
}
}
v___jp_4130_:
{
if (v___y_4137_ == 0)
{
v___y_4022_ = v___y_4133_;
v___y_4023_ = v___y_4134_;
v___y_4024_ = v___y_4132_;
v___y_4025_ = v___y_4135_;
v___y_4026_ = v___y_4136_;
v___y_4027_ = v___y_4131_;
goto v___jp_4021_;
}
else
{
v___y_4102_ = v___y_4131_;
v___y_4103_ = v___y_4132_;
v___y_4104_ = v___y_4133_;
v___y_4105_ = v___y_4134_;
v___y_4106_ = v___y_4135_;
v___y_4107_ = v___y_4136_;
goto v___jp_4101_;
}
}
v___jp_4138_:
{
if (v___y_4146_ == 0)
{
lean_dec_ref(v___y_4140_);
v___y_4131_ = v___y_4139_;
v___y_4132_ = v___y_4141_;
v___y_4133_ = v___y_4142_;
v___y_4134_ = v___y_4144_;
v___y_4135_ = v___y_4143_;
v___y_4136_ = v___y_4145_;
v___y_4137_ = v___x_3975_;
goto v___jp_4130_;
}
else
{
uint8_t v___x_4147_; 
v___x_4147_ = l_Lean_Expr_hasFVar(v___y_4140_);
lean_dec_ref(v___y_4140_);
if (v___x_4147_ == 0)
{
v___y_4102_ = v___y_4139_;
v___y_4103_ = v___y_4141_;
v___y_4104_ = v___y_4142_;
v___y_4105_ = v___y_4144_;
v___y_4106_ = v___y_4143_;
v___y_4107_ = v___y_4145_;
goto v___jp_4101_;
}
else
{
v___y_4131_ = v___y_4139_;
v___y_4132_ = v___y_4141_;
v___y_4133_ = v___y_4142_;
v___y_4134_ = v___y_4144_;
v___y_4135_ = v___y_4143_;
v___y_4136_ = v___y_4145_;
v___y_4137_ = v___x_3975_;
goto v___jp_4130_;
}
}
}
v___jp_4148_:
{
lean_object* v___x_4156_; 
lean_inc_ref(v___x_4020_);
v___x_4156_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4020_, v___y_4153_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; uint8_t v___x_4158_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v___x_4158_ = l_Lean_Expr_hasMVar(v_a_4157_);
if (v___x_4158_ == 0)
{
v___y_4139_ = v___y_4149_;
v___y_4140_ = v_a_4157_;
v___y_4141_ = v___y_4150_;
v___y_4142_ = v___y_4151_;
v___y_4143_ = v___y_4153_;
v___y_4144_ = v___y_4152_;
v___y_4145_ = v___y_4154_;
v___y_4146_ = v___y_4155_;
goto v___jp_4138_;
}
else
{
v___y_4139_ = v___y_4149_;
v___y_4140_ = v_a_4157_;
v___y_4141_ = v___y_4150_;
v___y_4142_ = v___y_4151_;
v___y_4143_ = v___y_4153_;
v___y_4144_ = v___y_4152_;
v___y_4145_ = v___y_4154_;
v___y_4146_ = v___x_3975_;
goto v___jp_4138_;
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec_ref(v___x_4020_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4159_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4156_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4156_);
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
v___jp_4167_:
{
if (v___y_4174_ == 0)
{
v___y_4022_ = v___y_4170_;
v___y_4023_ = v___y_4171_;
v___y_4024_ = v___y_4169_;
v___y_4025_ = v___y_4172_;
v___y_4026_ = v___y_4173_;
v___y_4027_ = v___y_4168_;
goto v___jp_4021_;
}
else
{
v___y_4149_ = v___y_4168_;
v___y_4150_ = v___y_4169_;
v___y_4151_ = v___y_4170_;
v___y_4152_ = v___y_4171_;
v___y_4153_ = v___y_4172_;
v___y_4154_ = v___y_4173_;
v___y_4155_ = v___y_4174_;
goto v___jp_4148_;
}
}
v___jp_4175_:
{
uint8_t v_useDecide_4182_; 
v_useDecide_4182_ = lean_ctor_get_uint8(v_config_3868_, sizeof(void*)*1);
if (v_useDecide_4182_ == 0)
{
v___y_4168_ = v___y_4181_;
v___y_4169_ = v___y_4178_;
v___y_4170_ = v_isHEq_4177_;
v___y_4171_ = v___y_4176_;
v___y_4172_ = v___y_4179_;
v___y_4173_ = v___y_4180_;
v___y_4174_ = v___x_3975_;
goto v___jp_4167_;
}
else
{
uint8_t v___x_4183_; 
v___x_4183_ = l_Lean_Expr_hasFVar(v___x_4020_);
if (v___x_4183_ == 0)
{
v___y_4149_ = v___y_4181_;
v___y_4150_ = v___y_4178_;
v___y_4151_ = v_isHEq_4177_;
v___y_4152_ = v___y_4176_;
v___y_4153_ = v___y_4179_;
v___y_4154_ = v___y_4180_;
v___y_4155_ = v_useDecide_4182_;
goto v___jp_4148_;
}
else
{
v___y_4168_ = v___y_4181_;
v___y_4169_ = v___y_4178_;
v___y_4170_ = v_isHEq_4177_;
v___y_4171_ = v___y_4176_;
v___y_4172_ = v___y_4179_;
v___y_4173_ = v___y_4180_;
v___y_4174_ = v___x_3975_;
goto v___jp_4167_;
}
}
}
v___jp_4184_:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Meta_isExprDefEq(v___y_4190_, v___y_4189_, v___y_4188_, v___y_4187_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; uint8_t v___x_4194_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4194_ = lean_unbox(v_a_4193_);
lean_dec(v_a_4193_);
if (v___x_4194_ == 0)
{
v___y_4176_ = v___y_4191_;
v_isHEq_4177_ = v___x_3879_;
v___y_4178_ = v___y_4188_;
v___y_4179_ = v___y_4187_;
v___y_4180_ = v___y_4185_;
v___y_4181_ = v___y_4186_;
goto v___jp_4175_;
}
else
{
lean_object* v___x_4195_; 
lean_dec_ref(v___x_4020_);
lean_dec_ref(v_config_3868_);
lean_inc(v_mvarId_3869_);
v___x_4195_ = l_Lean_MVarId_getType(v_mvarId_3869_, v___y_4188_, v___y_4187_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4195_, 1);
v___x_4197_ = l_Lean_LocalDecl_toExpr(v_val_3900_);
v___x_4198_ = l_Lean_Meta_mkEqOfHEq(v___x_4197_, v___x_3879_, v___y_4188_, v___y_4187_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4200_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v___x_4200_ = l_Lean_Meta_mkNoConfusion(v_a_4196_, v_a_4199_, v___y_4188_, v___y_4187_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4202_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref_known(v___x_4200_, 1);
v___x_4202_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3869_, v_a_4201_, v___y_4187_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_dec_ref_known(v___x_4202_, 1);
v___x_4203_ = lean_box(v___x_3879_);
v___x_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
v___x_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
lean_ctor_set(v___x_4205_, 1, v___x_3904_);
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
v_a_3886_ = v___x_4206_;
goto v___jp_3885_;
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
v_a_4207_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4202_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4202_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4215_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4200_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4200_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_a_4196_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4223_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4198_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4198_);
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
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4231_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4195_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4195_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec_ref(v___x_4020_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4239_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4192_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4192_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
v___jp_4247_:
{
lean_object* v___x_4253_; 
lean_inc_ref(v___x_4020_);
v___x_4253_ = l_Lean_Meta_matchHEq_x3f(v___x_4020_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
if (lean_obj_tag(v_a_4254_) == 1)
{
lean_object* v_val_4255_; lean_object* v_snd_4256_; lean_object* v_snd_4257_; lean_object* v_fst_4258_; lean_object* v_fst_4259_; lean_object* v_fst_4260_; lean_object* v_snd_4261_; lean_object* v___x_4262_; 
v_val_4255_ = lean_ctor_get(v_a_4254_, 0);
lean_inc(v_val_4255_);
lean_dec_ref_known(v_a_4254_, 1);
v_snd_4256_ = lean_ctor_get(v_val_4255_, 1);
lean_inc(v_snd_4256_);
v_snd_4257_ = lean_ctor_get(v_snd_4256_, 1);
lean_inc(v_snd_4257_);
v_fst_4258_ = lean_ctor_get(v_val_4255_, 0);
lean_inc(v_fst_4258_);
lean_dec(v_val_4255_);
v_fst_4259_ = lean_ctor_get(v_snd_4256_, 0);
lean_inc(v_fst_4259_);
lean_dec(v_snd_4256_);
v_fst_4260_ = lean_ctor_get(v_snd_4257_, 0);
lean_inc(v_fst_4260_);
v_snd_4261_ = lean_ctor_get(v_snd_4257_, 1);
lean_inc(v_snd_4261_);
lean_dec(v_snd_4257_);
v___x_4262_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4259_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
if (lean_obj_tag(v_a_4263_) == 1)
{
lean_object* v_val_4264_; lean_object* v___x_4265_; 
v_val_4264_ = lean_ctor_get(v_a_4263_, 0);
lean_inc(v_val_4264_);
lean_dec_ref_known(v_a_4263_, 1);
v___x_4265_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4261_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v___x_4265_, 1);
if (lean_obj_tag(v_a_4266_) == 1)
{
lean_object* v_toConstantVal_4267_; lean_object* v_val_4268_; lean_object* v_toConstantVal_4269_; lean_object* v_name_4270_; lean_object* v_name_4271_; uint8_t v___x_4272_; 
v_toConstantVal_4267_ = lean_ctor_get(v_val_4264_, 0);
lean_inc_ref(v_toConstantVal_4267_);
lean_dec(v_val_4264_);
v_val_4268_ = lean_ctor_get(v_a_4266_, 0);
lean_inc(v_val_4268_);
lean_dec_ref_known(v_a_4266_, 1);
v_toConstantVal_4269_ = lean_ctor_get(v_val_4268_, 0);
lean_inc_ref(v_toConstantVal_4269_);
lean_dec(v_val_4268_);
v_name_4270_ = lean_ctor_get(v_toConstantVal_4267_, 0);
lean_inc(v_name_4270_);
lean_dec_ref(v_toConstantVal_4267_);
v_name_4271_ = lean_ctor_get(v_toConstantVal_4269_, 0);
lean_inc(v_name_4271_);
lean_dec_ref(v_toConstantVal_4269_);
v___x_4272_ = lean_name_eq(v_name_4270_, v_name_4271_);
lean_dec(v_name_4271_);
lean_dec(v_name_4270_);
if (v___x_4272_ == 0)
{
v___y_4185_ = v___y_4251_;
v___y_4186_ = v___y_4252_;
v___y_4187_ = v___y_4250_;
v___y_4188_ = v___y_4249_;
v___y_4189_ = v_fst_4260_;
v___y_4190_ = v_fst_4258_;
v___y_4191_ = v_isEq_4248_;
goto v___jp_4184_;
}
else
{
if (v___x_3975_ == 0)
{
lean_dec(v_fst_4260_);
lean_dec(v_fst_4258_);
v___y_4176_ = v_isEq_4248_;
v_isHEq_4177_ = v___x_3879_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
v___y_4181_ = v___y_4252_;
goto v___jp_4175_;
}
else
{
v___y_4185_ = v___y_4251_;
v___y_4186_ = v___y_4252_;
v___y_4187_ = v___y_4250_;
v___y_4188_ = v___y_4249_;
v___y_4189_ = v_fst_4260_;
v___y_4190_ = v_fst_4258_;
v___y_4191_ = v_isEq_4248_;
goto v___jp_4184_;
}
}
}
else
{
lean_dec(v_a_4266_);
lean_dec(v_val_4264_);
lean_dec(v_fst_4260_);
lean_dec(v_fst_4258_);
v___y_4176_ = v_isEq_4248_;
v_isHEq_4177_ = v___x_3879_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
v___y_4181_ = v___y_4252_;
goto v___jp_4175_;
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec(v_val_4264_);
lean_dec(v_fst_4260_);
lean_dec(v_fst_4258_);
lean_dec_ref(v___x_4020_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4273_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4265_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4265_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
else
{
lean_dec(v_a_4263_);
lean_dec(v_snd_4261_);
lean_dec(v_fst_4260_);
lean_dec(v_fst_4258_);
v___y_4176_ = v_isEq_4248_;
v_isHEq_4177_ = v___x_3879_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
v___y_4181_ = v___y_4252_;
goto v___jp_4175_;
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v_snd_4261_);
lean_dec(v_fst_4260_);
lean_dec(v_fst_4258_);
lean_dec_ref(v___x_4020_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4281_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4262_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4262_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
else
{
lean_dec(v_a_4254_);
v___y_4176_ = v_isEq_4248_;
v_isHEq_4177_ = v___x_3975_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
v___y_4181_ = v___y_4252_;
goto v___jp_4175_;
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec_ref(v___x_4020_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4289_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4253_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4253_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
v___jp_4297_:
{
lean_object* v___x_4302_; 
lean_inc_ref(v___x_4020_);
v___x_4302_ = l_Lean_Meta_matchEq_x3f(v___x_4020_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
if (lean_obj_tag(v_a_4303_) == 1)
{
lean_object* v_val_4304_; lean_object* v_snd_4305_; lean_object* v_fst_4306_; lean_object* v_snd_4307_; lean_object* v___x_4308_; 
v_val_4304_ = lean_ctor_get(v_a_4303_, 0);
lean_inc(v_val_4304_);
lean_dec_ref_known(v_a_4303_, 1);
v_snd_4305_ = lean_ctor_get(v_val_4304_, 1);
lean_inc(v_snd_4305_);
lean_dec(v_val_4304_);
v_fst_4306_ = lean_ctor_get(v_snd_4305_, 0);
lean_inc(v_fst_4306_);
v_snd_4307_ = lean_ctor_get(v_snd_4305_, 1);
lean_inc(v_snd_4307_);
lean_dec(v_snd_4305_);
v___x_4308_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4306_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4308_, 1);
if (lean_obj_tag(v_a_4309_) == 1)
{
lean_object* v_val_4310_; lean_object* v___x_4311_; 
v_val_4310_ = lean_ctor_get(v_a_4309_, 0);
lean_inc(v_val_4310_);
lean_dec_ref_known(v_a_4309_, 1);
v___x_4311_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4307_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
if (lean_obj_tag(v_a_4312_) == 1)
{
lean_object* v_toConstantVal_4313_; lean_object* v_val_4314_; lean_object* v_toConstantVal_4315_; lean_object* v_name_4316_; lean_object* v_name_4317_; uint8_t v___x_4318_; 
v_toConstantVal_4313_ = lean_ctor_get(v_val_4310_, 0);
lean_inc_ref(v_toConstantVal_4313_);
lean_dec(v_val_4310_);
v_val_4314_ = lean_ctor_get(v_a_4312_, 0);
lean_inc(v_val_4314_);
lean_dec_ref_known(v_a_4312_, 1);
v_toConstantVal_4315_ = lean_ctor_get(v_val_4314_, 0);
lean_inc_ref(v_toConstantVal_4315_);
lean_dec(v_val_4314_);
v_name_4316_ = lean_ctor_get(v_toConstantVal_4313_, 0);
lean_inc(v_name_4316_);
lean_dec_ref(v_toConstantVal_4313_);
v_name_4317_ = lean_ctor_get(v_toConstantVal_4315_, 0);
lean_inc(v_name_4317_);
lean_dec_ref(v_toConstantVal_4315_);
v___x_4318_ = lean_name_eq(v_name_4316_, v_name_4317_);
lean_dec(v_name_4317_);
lean_dec(v_name_4316_);
if (v___x_4318_ == 0)
{
lean_dec_ref(v___x_4020_);
lean_dec_ref(v_config_3868_);
v___y_3906_ = v___y_4300_;
v___y_3907_ = v___y_4298_;
v___y_3908_ = v___y_4299_;
v___y_3909_ = v___y_4301_;
goto v___jp_3905_;
}
else
{
if (v___x_3975_ == 0)
{
lean_del_object(v___x_3902_);
v_isEq_4248_ = v___x_3879_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
v___y_4252_ = v___y_4301_;
goto v___jp_4247_;
}
else
{
lean_dec_ref(v___x_4020_);
lean_dec_ref(v_config_3868_);
v___y_3906_ = v___y_4300_;
v___y_3907_ = v___y_4298_;
v___y_3908_ = v___y_4299_;
v___y_3909_ = v___y_4301_;
goto v___jp_3905_;
}
}
}
else
{
lean_dec(v_a_4312_);
lean_dec(v_val_4310_);
lean_del_object(v___x_3902_);
v_isEq_4248_ = v___x_3879_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
v___y_4252_ = v___y_4301_;
goto v___jp_4247_;
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_dec(v_val_4310_);
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4319_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4311_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4311_);
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
lean_dec(v_a_4309_);
lean_dec(v_snd_4307_);
lean_del_object(v___x_3902_);
v_isEq_4248_ = v___x_3879_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
v___y_4252_ = v___y_4301_;
goto v___jp_4247_;
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_dec(v_snd_4307_);
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4327_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4308_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4308_);
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
else
{
lean_dec(v_a_4303_);
lean_del_object(v___x_3902_);
v_isEq_4248_ = v___x_3975_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
v___y_4252_ = v___y_4301_;
goto v___jp_4247_;
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4335_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4302_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4302_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
v___jp_4343_:
{
lean_object* v___x_4348_; 
lean_inc_ref(v___x_4020_);
v___x_4348_ = l_Lean_refutableHasNotBit_x3f(v___x_4020_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4348_, 1);
if (lean_obj_tag(v_a_4349_) == 1)
{
lean_object* v_val_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4390_; 
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec_ref(v_config_3868_);
v_val_4350_ = lean_ctor_get(v_a_4349_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v_a_4349_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4352_ = v_a_4349_;
v_isShared_4353_ = v_isSharedCheck_4390_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_val_4350_);
lean_dec(v_a_4349_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4390_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; 
lean_inc(v_mvarId_3869_);
v___x_4354_ = l_Lean_MVarId_getType(v_mvarId_3869_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = l_Lean_LocalDecl_toExpr(v_val_3900_);
v___x_4357_ = l_Lean_Meta_mkAbsurd(v_a_4355_, v_val_4350_, v___x_4356_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4359_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v___x_4359_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3869_, v_a_4358_, v___y_4345_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v___x_4360_; lean_object* v___x_4362_; 
lean_dec_ref_known(v___x_4359_, 1);
v___x_4360_ = lean_box(v___x_3879_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4360_);
v___x_4362_ = v___x_4352_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4360_);
v___x_4362_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
lean_ctor_set(v___x_4363_, 1, v___x_3904_);
v___x_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
v_a_3886_ = v___x_4364_;
goto v___jp_3885_;
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_del_object(v___x_4352_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
v_a_4366_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4359_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4359_);
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
lean_del_object(v___x_4352_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4374_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4357_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4357_);
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
lean_del_object(v___x_4352_);
lean_dec(v_val_4350_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4382_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4354_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4354_);
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
}
else
{
lean_object* v___x_4391_; 
lean_dec(v_a_4349_);
lean_inc_ref(v___x_4020_);
v___x_4391_ = l_Lean_Meta_matchNe_x3f(v___x_4020_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v___x_4391_, 1);
if (lean_obj_tag(v_a_4392_) == 1)
{
lean_object* v_val_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4463_; 
v_val_4393_ = lean_ctor_get(v_a_4392_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v_a_4392_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4395_ = v_a_4392_;
v_isShared_4396_ = v_isSharedCheck_4463_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_val_4393_);
lean_dec(v_a_4392_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4463_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v_snd_4397_; lean_object* v_fst_4398_; lean_object* v_snd_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4462_; 
v_snd_4397_ = lean_ctor_get(v_val_4393_, 1);
lean_inc(v_snd_4397_);
lean_dec(v_val_4393_);
v_fst_4398_ = lean_ctor_get(v_snd_4397_, 0);
v_snd_4399_ = lean_ctor_get(v_snd_4397_, 1);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_snd_4397_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4401_ = v_snd_4397_;
v_isShared_4402_ = v_isSharedCheck_4462_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_snd_4399_);
lean_inc(v_fst_4398_);
lean_dec(v_snd_4397_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4462_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; 
lean_inc(v_fst_4398_);
v___x_4403_ = l_Lean_Meta_isExprDefEq(v_fst_4398_, v_snd_4399_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; uint8_t v___x_4405_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = lean_unbox(v_a_4404_);
lean_dec(v_a_4404_);
if (v___x_4405_ == 0)
{
lean_del_object(v___x_4401_);
lean_dec(v_fst_4398_);
lean_del_object(v___x_4395_);
v___y_4298_ = v___y_4344_;
v___y_4299_ = v___y_4345_;
v___y_4300_ = v___y_4346_;
v___y_4301_ = v___y_4347_;
goto v___jp_4297_;
}
else
{
lean_object* v___x_4406_; 
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec_ref(v_config_3868_);
lean_inc(v_mvarId_3869_);
v___x_4406_ = l_Lean_MVarId_getType(v_mvarId_3869_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4408_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
v___x_4408_ = l_Lean_Meta_mkEqRefl(v_fst_4398_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v___x_4408_, 1);
v___x_4410_ = l_Lean_LocalDecl_toExpr(v_val_3900_);
v___x_4411_ = l_Lean_Meta_mkAbsurd(v_a_4407_, v_a_4409_, v___x_4410_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4413_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
v___x_4413_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3869_, v_a_4412_, v___y_4345_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v___x_4414_; lean_object* v___x_4416_; 
lean_dec_ref_known(v___x_4413_, 1);
v___x_4414_ = lean_box(v___x_3879_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4414_);
v___x_4416_ = v___x_4395_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4418_; 
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 1, v___x_3904_);
lean_ctor_set(v___x_4401_, 0, v___x_4416_);
v___x_4418_ = v___x_4401_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v___x_3904_);
v___x_4418_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; 
v___x_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
v_a_3886_ = v___x_4419_;
goto v___jp_3885_;
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_del_object(v___x_4401_);
lean_del_object(v___x_4395_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
v_a_4422_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4413_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4413_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_del_object(v___x_4401_);
lean_del_object(v___x_4395_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4430_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4411_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4411_);
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
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec(v_a_4407_);
lean_del_object(v___x_4401_);
lean_del_object(v___x_4395_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4438_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4408_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4408_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_del_object(v___x_4401_);
lean_dec(v_fst_4398_);
lean_del_object(v___x_4395_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_4446_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4406_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4406_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_del_object(v___x_4401_);
lean_dec(v_fst_4398_);
lean_del_object(v___x_4395_);
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4454_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4403_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4403_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4392_);
v___y_4298_ = v___y_4344_;
v___y_4299_ = v___y_4345_;
v___y_4300_ = v___y_4346_;
v___y_4301_ = v___y_4347_;
goto v___jp_4297_;
}
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4471_; 
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4464_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4466_ = v___x_4391_;
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4391_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4469_; 
if (v_isShared_4467_ == 0)
{
v___x_4469_ = v___x_4466_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4464_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
}
else
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
lean_dec_ref(v___x_4020_);
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4472_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4474_ = v___x_4348_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4348_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
}
else
{
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
v_a_3894_ = v___x_3946_;
goto v___jp_3893_;
}
v___jp_3905_:
{
lean_object* v___x_3910_; 
lean_inc(v_mvarId_3869_);
v___x_3910_ = l_Lean_MVarId_getType(v_mvarId_3869_, v___y_3907_, v___y_3908_, v___y_3906_, v___y_3909_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = l_Lean_LocalDecl_toExpr(v_val_3900_);
v___x_3913_ = l_Lean_Meta_mkNoConfusion(v_a_3911_, v___x_3912_, v___y_3907_, v___y_3908_, v___y_3906_, v___y_3909_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3869_, v_a_3914_, v___y_3908_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v___x_3916_; lean_object* v___x_3918_; 
lean_dec_ref_known(v___x_3915_, 1);
v___x_3916_ = lean_box(v___x_3879_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3916_);
v___x_3918_ = v___x_3902_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
lean_ctor_set(v___x_3919_, 1, v___x_3904_);
v___x_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
v_a_3886_ = v___x_3920_;
goto v___jp_3885_;
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_del_object(v___x_3902_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
v_a_3922_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3915_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3915_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_del_object(v___x_3902_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_3930_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3913_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3913_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_del_object(v___x_3902_);
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_3938_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3910_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3910_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
v___jp_3947_:
{
lean_object* v_searchFuel_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_searchFuel_3952_ = lean_ctor_get(v_config_3868_, 0);
v___x_3953_ = l_Lean_LocalDecl_fvarId(v_val_3900_);
lean_dec(v_val_3900_);
lean_inc(v_searchFuel_3952_);
lean_inc(v_mvarId_3869_);
v___x_3954_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3869_, v___x_3953_, v_searchFuel_3952_, v___y_3951_, v___y_3950_, v___y_3949_, v___y_3948_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; uint8_t v___x_3956_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
v___x_3956_ = lean_unbox(v_a_3955_);
lean_dec(v_a_3955_);
if (v___x_3956_ == 0)
{
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
v_a_3894_ = v___x_3946_;
goto v___jp_3893_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v___x_3957_ = lean_box(v___x_3879_);
v___x_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
v___x_3959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
lean_ctor_set(v___x_3959_, 1, v___x_3904_);
v___x_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
v_a_3886_ = v___x_3960_;
goto v___jp_3885_;
}
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_3961_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3963_ = v___x_3954_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3954_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
v___jp_3969_:
{
if (v___y_3974_ == 0)
{
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
v_a_3894_ = v___x_3946_;
goto v___jp_3893_;
}
else
{
v___y_3948_ = v___y_3971_;
v___y_3949_ = v___y_3970_;
v___y_3950_ = v___y_3972_;
v___y_3951_ = v___y_3973_;
goto v___jp_3947_;
}
}
v___jp_3976_:
{
if (v___y_3979_ == 0)
{
v___y_3948_ = v___y_3978_;
v___y_3949_ = v___y_3977_;
v___y_3950_ = v___y_3980_;
v___y_3951_ = v___y_3981_;
goto v___jp_3947_;
}
else
{
v___y_3970_ = v___y_3977_;
v___y_3971_ = v___y_3978_;
v___y_3972_ = v___y_3980_;
v___y_3973_ = v___y_3981_;
v___y_3974_ = v___x_3975_;
goto v___jp_3969_;
}
}
v___jp_3982_:
{
if (v___y_3988_ == 0)
{
v___y_3970_ = v___y_3985_;
v___y_3971_ = v___y_3984_;
v___y_3972_ = v___y_3986_;
v___y_3973_ = v___y_3987_;
v___y_3974_ = v___x_3975_;
goto v___jp_3969_;
}
else
{
v___y_3977_ = v___y_3985_;
v___y_3978_ = v___y_3984_;
v___y_3979_ = v___y_3983_;
v___y_3980_ = v___y_3986_;
v___y_3981_ = v___y_3987_;
goto v___jp_3976_;
}
}
v___jp_3989_:
{
uint8_t v_emptyType_3996_; 
v_emptyType_3996_ = lean_ctor_get_uint8(v_config_3868_, sizeof(void*)*1 + 1);
if (v_emptyType_3996_ == 0)
{
v___y_3983_ = v___y_3990_;
v___y_3984_ = v___y_3995_;
v___y_3985_ = v___y_3994_;
v___y_3986_ = v___y_3993_;
v___y_3987_ = v___y_3992_;
v___y_3988_ = v___x_3975_;
goto v___jp_3982_;
}
else
{
if (v___y_3991_ == 0)
{
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___y_3995_;
v___y_3979_ = v___y_3990_;
v___y_3980_ = v___y_3993_;
v___y_3981_ = v___y_3992_;
goto v___jp_3976_;
}
else
{
v___y_3983_ = v___y_3990_;
v___y_3984_ = v___y_3995_;
v___y_3985_ = v___y_3994_;
v___y_3986_ = v___y_3993_;
v___y_3987_ = v___y_3992_;
v___y_3988_ = v___x_3975_;
goto v___jp_3982_;
}
}
}
v___jp_3997_:
{
if (v___y_4004_ == 0)
{
v___y_3990_ = v___y_4002_;
v___y_3991_ = v___y_4003_;
v___y_3992_ = v___y_4001_;
v___y_3993_ = v___y_4000_;
v___y_3994_ = v___y_3999_;
v___y_3995_ = v___y_3998_;
goto v___jp_3989_;
}
else
{
lean_object* v___x_4005_; 
lean_inc(v_val_3900_);
lean_inc(v_mvarId_3869_);
v___x_4005_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3869_, v_val_3900_, v___y_4001_, v___y_4000_, v___y_3999_, v___y_3998_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; uint8_t v___x_4007_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v___x_4007_ = lean_unbox(v_a_4006_);
lean_dec(v_a_4006_);
if (v___x_4007_ == 0)
{
v___y_3990_ = v___y_4002_;
v___y_3991_ = v___y_4003_;
v___y_3992_ = v___y_4001_;
v___y_3993_ = v___y_4000_;
v___y_3994_ = v___y_3999_;
v___y_3995_ = v___y_3998_;
goto v___jp_3989_;
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_dec(v_val_3900_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v___x_4008_ = lean_box(v___x_3879_);
v___x_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
v___x_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
lean_ctor_set(v___x_4010_, 1, v___x_3904_);
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
v_a_3886_ = v___x_4011_;
goto v___jp_3885_;
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_dec(v_val_3900_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
lean_dec_ref(v_config_3868_);
v_a_4012_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4005_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4005_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
}
}
v___jp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3887_, 0, v_a_3886_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v___x_3887_);
v___x_3889_ = v___x_3883_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3887_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_snd_3881_);
v___x_3889_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
return v___x_3890_;
}
}
v___jp_3893_:
{
lean_object* v___x_3895_; size_t v___x_3896_; size_t v___x_3897_; lean_object* v___x_3898_; 
v___x_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3892_);
lean_ctor_set(v___x_3895_, 1, v_a_3894_);
v___x_3896_ = ((size_t)1ULL);
v___x_3897_ = lean_usize_add(v_i_3872_, v___x_3896_);
v___x_3898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3868_, v_mvarId_3869_, v_as_3870_, v_sz_3871_, v___x_3897_, v___x_3895_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
return v___x_3898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4553_, lean_object* v_mvarId_4554_, lean_object* v_as_4555_, lean_object* v_sz_4556_, lean_object* v_i_4557_, lean_object* v_b_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
size_t v_sz_boxed_4564_; size_t v_i_boxed_4565_; lean_object* v_res_4566_; 
v_sz_boxed_4564_ = lean_unbox_usize(v_sz_4556_);
lean_dec(v_sz_4556_);
v_i_boxed_4565_ = lean_unbox_usize(v_i_4557_);
lean_dec(v_i_4557_);
v_res_4566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4553_, v_mvarId_4554_, v_as_4555_, v_sz_boxed_4564_, v_i_boxed_4565_, v_b_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec_ref(v_as_4555_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4567_, lean_object* v_config_4568_, lean_object* v_mvarId_4569_, lean_object* v_n_4570_, lean_object* v_b_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
if (lean_obj_tag(v_n_4570_) == 0)
{
lean_object* v_cs_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; size_t v_sz_4580_; size_t v___x_4581_; lean_object* v___x_4582_; 
v_cs_4577_ = lean_ctor_get(v_n_4570_, 0);
v___x_4578_ = lean_box(0);
v___x_4579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
lean_ctor_set(v___x_4579_, 1, v_b_4571_);
v_sz_4580_ = lean_array_size(v_cs_4577_);
v___x_4581_ = ((size_t)0ULL);
v___x_4582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4567_, v_config_4568_, v_mvarId_4569_, v_cs_4577_, v_sz_4580_, v___x_4581_, v___x_4579_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4597_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4597_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4582_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4597_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v_fst_4587_; 
v_fst_4587_ = lean_ctor_get(v_a_4583_, 0);
if (lean_obj_tag(v_fst_4587_) == 0)
{
lean_object* v_snd_4588_; lean_object* v___x_4589_; lean_object* v___x_4591_; 
v_snd_4588_ = lean_ctor_get(v_a_4583_, 1);
lean_inc(v_snd_4588_);
lean_dec(v_a_4583_);
v___x_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4589_, 0, v_snd_4588_);
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 0, v___x_4589_);
v___x_4591_ = v___x_4585_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4589_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
else
{
lean_object* v_val_4593_; lean_object* v___x_4595_; 
lean_inc_ref(v_fst_4587_);
lean_dec(v_a_4583_);
v_val_4593_ = lean_ctor_get(v_fst_4587_, 0);
lean_inc(v_val_4593_);
lean_dec_ref_known(v_fst_4587_, 1);
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 0, v_val_4593_);
v___x_4595_ = v___x_4585_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_val_4593_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4605_; 
v_a_4598_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4600_ = v___x_4582_;
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4582_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4603_; 
if (v_isShared_4601_ == 0)
{
v___x_4603_ = v___x_4600_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4598_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
}
else
{
lean_object* v_vs_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; size_t v_sz_4609_; size_t v___x_4610_; lean_object* v___x_4611_; 
v_vs_4606_ = lean_ctor_get(v_n_4570_, 0);
v___x_4607_ = lean_box(0);
v___x_4608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
lean_ctor_set(v___x_4608_, 1, v_b_4571_);
v_sz_4609_ = lean_array_size(v_vs_4606_);
v___x_4610_ = ((size_t)0ULL);
v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4568_, v_mvarId_4569_, v_vs_4606_, v_sz_4609_, v___x_4610_, v___x_4608_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4626_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4614_ = v___x_4611_;
v_isShared_4615_ = v_isSharedCheck_4626_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4626_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v_fst_4616_; 
v_fst_4616_ = lean_ctor_get(v_a_4612_, 0);
if (lean_obj_tag(v_fst_4616_) == 0)
{
lean_object* v_snd_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
v_snd_4617_ = lean_ctor_get(v_a_4612_, 1);
lean_inc(v_snd_4617_);
lean_dec(v_a_4612_);
v___x_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4618_, 0, v_snd_4617_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v___x_4618_);
v___x_4620_ = v___x_4614_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4618_);
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
lean_inc_ref(v_fst_4616_);
lean_dec(v_a_4612_);
v_val_4622_ = lean_ctor_get(v_fst_4616_, 0);
lean_inc(v_val_4622_);
lean_dec_ref_known(v_fst_4616_, 1);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v_val_4622_);
v___x_4624_ = v___x_4614_;
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
v_a_4627_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4611_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4611_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4635_, lean_object* v_config_4636_, lean_object* v_mvarId_4637_, lean_object* v_as_4638_, size_t v_sz_4639_, size_t v_i_4640_, lean_object* v_b_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
uint8_t v___x_4647_; 
v___x_4647_ = lean_usize_dec_lt(v_i_4640_, v_sz_4639_);
if (v___x_4647_ == 0)
{
lean_object* v___x_4648_; 
lean_dec(v_mvarId_4637_);
lean_dec_ref(v_config_4636_);
v___x_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4648_, 0, v_b_4641_);
return v___x_4648_;
}
else
{
lean_object* v_snd_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4683_; 
v_snd_4649_ = lean_ctor_get(v_b_4641_, 1);
v_isSharedCheck_4683_ = !lean_is_exclusive(v_b_4641_);
if (v_isSharedCheck_4683_ == 0)
{
lean_object* v_unused_4684_; 
v_unused_4684_ = lean_ctor_get(v_b_4641_, 0);
lean_dec(v_unused_4684_);
v___x_4651_ = v_b_4641_;
v_isShared_4652_ = v_isSharedCheck_4683_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_snd_4649_);
lean_dec(v_b_4641_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4683_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4653_; lean_object* v_a_4654_; lean_object* v___x_4655_; 
v___x_4653_ = lean_box(0);
v_a_4654_ = lean_array_uget_borrowed(v_as_4638_, v_i_4640_);
lean_inc(v_snd_4649_);
lean_inc(v_mvarId_4637_);
lean_inc_ref(v_config_4636_);
v___x_4655_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4635_, v_config_4636_, v_mvarId_4637_, v_a_4654_, v_snd_4649_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4674_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4658_ = v___x_4655_;
v_isShared_4659_ = v_isSharedCheck_4674_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4655_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4674_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
if (lean_obj_tag(v_a_4656_) == 0)
{
lean_object* v___x_4660_; lean_object* v___x_4662_; 
lean_dec(v_mvarId_4637_);
lean_dec_ref(v_config_4636_);
v___x_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4660_, 0, v_a_4656_);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 0, v___x_4660_);
v___x_4662_ = v___x_4651_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v_snd_4649_);
v___x_4662_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4664_; 
if (v_isShared_4659_ == 0)
{
lean_ctor_set(v___x_4658_, 0, v___x_4662_);
v___x_4664_ = v___x_4658_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
else
{
lean_object* v_a_4667_; lean_object* v___x_4669_; 
lean_del_object(v___x_4658_);
lean_dec(v_snd_4649_);
v_a_4667_ = lean_ctor_get(v_a_4656_, 0);
lean_inc(v_a_4667_);
lean_dec_ref_known(v_a_4656_, 1);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 1, v_a_4667_);
lean_ctor_set(v___x_4651_, 0, v___x_4653_);
v___x_4669_ = v___x_4651_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4673_, 1, v_a_4667_);
v___x_4669_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
size_t v___x_4670_; size_t v___x_4671_; 
v___x_4670_ = ((size_t)1ULL);
v___x_4671_ = lean_usize_add(v_i_4640_, v___x_4670_);
v_i_4640_ = v___x_4671_;
v_b_4641_ = v___x_4669_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
lean_del_object(v___x_4651_);
lean_dec(v_snd_4649_);
lean_dec(v_mvarId_4637_);
lean_dec_ref(v_config_4636_);
v_a_4675_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4677_ = v___x_4655_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4655_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4675_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4685_, lean_object* v_config_4686_, lean_object* v_mvarId_4687_, lean_object* v_as_4688_, lean_object* v_sz_4689_, lean_object* v_i_4690_, lean_object* v_b_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
size_t v_sz_boxed_4697_; size_t v_i_boxed_4698_; lean_object* v_res_4699_; 
v_sz_boxed_4697_ = lean_unbox_usize(v_sz_4689_);
lean_dec(v_sz_4689_);
v_i_boxed_4698_ = lean_unbox_usize(v_i_4690_);
lean_dec(v_i_4690_);
v_res_4699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4685_, v_config_4686_, v_mvarId_4687_, v_as_4688_, v_sz_boxed_4697_, v_i_boxed_4698_, v_b_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec_ref(v_as_4688_);
lean_dec_ref(v_init_4685_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4700_, lean_object* v_config_4701_, lean_object* v_mvarId_4702_, lean_object* v_n_4703_, lean_object* v_b_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4700_, v_config_4701_, v_mvarId_4702_, v_n_4703_, v_b_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec_ref(v_n_4703_);
lean_dec_ref(v_init_4700_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4711_, lean_object* v_mvarId_4712_, lean_object* v_t_4713_, lean_object* v_init_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v_root_4720_; lean_object* v_tail_4721_; lean_object* v___x_4722_; 
v_root_4720_ = lean_ctor_get(v_t_4713_, 0);
v_tail_4721_ = lean_ctor_get(v_t_4713_, 1);
lean_inc(v_mvarId_4712_);
lean_inc_ref(v_config_4711_);
lean_inc_ref(v_init_4714_);
v___x_4722_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4714_, v_config_4711_, v_mvarId_4712_, v_root_4720_, v_init_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
lean_dec_ref(v_init_4714_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4759_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4725_ = v___x_4722_;
v_isShared_4726_ = v_isSharedCheck_4759_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_a_4723_);
lean_dec(v___x_4722_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4759_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
if (lean_obj_tag(v_a_4723_) == 0)
{
lean_object* v_a_4727_; lean_object* v___x_4729_; 
lean_dec(v_mvarId_4712_);
lean_dec_ref(v_config_4711_);
v_a_4727_ = lean_ctor_get(v_a_4723_, 0);
lean_inc(v_a_4727_);
lean_dec_ref_known(v_a_4723_, 1);
if (v_isShared_4726_ == 0)
{
lean_ctor_set(v___x_4725_, 0, v_a_4727_);
v___x_4729_ = v___x_4725_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4727_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; size_t v_sz_4734_; size_t v___x_4735_; lean_object* v___x_4736_; 
lean_del_object(v___x_4725_);
v_a_4731_ = lean_ctor_get(v_a_4723_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v_a_4723_, 1);
v___x_4732_ = lean_box(0);
v___x_4733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
lean_ctor_set(v___x_4733_, 1, v_a_4731_);
v_sz_4734_ = lean_array_size(v_tail_4721_);
v___x_4735_ = ((size_t)0ULL);
v___x_4736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4711_, v_mvarId_4712_, v_tail_4721_, v_sz_4734_, v___x_4735_, v___x_4733_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4750_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4739_ = v___x_4736_;
v_isShared_4740_ = v_isSharedCheck_4750_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4750_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v_fst_4741_; 
v_fst_4741_ = lean_ctor_get(v_a_4737_, 0);
if (lean_obj_tag(v_fst_4741_) == 0)
{
lean_object* v_snd_4742_; lean_object* v___x_4744_; 
v_snd_4742_ = lean_ctor_get(v_a_4737_, 1);
lean_inc(v_snd_4742_);
lean_dec(v_a_4737_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v_snd_4742_);
v___x_4744_ = v___x_4739_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_snd_4742_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
else
{
lean_object* v_val_4746_; lean_object* v___x_4748_; 
lean_inc_ref(v_fst_4741_);
lean_dec(v_a_4737_);
v_val_4746_ = lean_ctor_get(v_fst_4741_, 0);
lean_inc(v_val_4746_);
lean_dec_ref_known(v_fst_4741_, 1);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v_val_4746_);
v___x_4748_ = v___x_4739_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_val_4746_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
v_a_4751_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4736_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4736_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
}
}
else
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_dec(v_mvarId_4712_);
lean_dec_ref(v_config_4711_);
v_a_4760_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4722_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4722_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4768_, lean_object* v_mvarId_4769_, lean_object* v_t_4770_, lean_object* v_init_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4768_, v_mvarId_4769_, v_t_4770_, v_init_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4774_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec_ref(v_t_4770_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4778_, lean_object* v___x_4779_, lean_object* v_config_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
lean_object* v___x_4786_; 
lean_inc(v_mvarId_4778_);
v___x_4786_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4778_, v___x_4779_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v___x_4787_; 
lean_dec_ref_known(v___x_4786_, 1);
lean_inc(v_mvarId_4778_);
v___x_4787_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4778_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4821_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4790_ = v___x_4787_;
v_isShared_4791_ = v_isSharedCheck_4821_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4787_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4821_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
uint8_t v___x_4792_; 
v___x_4792_ = lean_unbox(v_a_4788_);
if (v___x_4792_ == 0)
{
lean_object* v_lctx_4793_; lean_object* v_decls_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_del_object(v___x_4790_);
v_lctx_4793_ = lean_ctor_get(v___y_4781_, 2);
v_decls_4794_ = lean_ctor_get(v_lctx_4793_, 1);
v___x_4795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4796_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4780_, v_mvarId_4778_, v_decls_4794_, v___x_4795_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4809_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4799_ = v___x_4796_;
v_isShared_4800_ = v_isSharedCheck_4809_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4796_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4809_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v_fst_4801_; 
v_fst_4801_ = lean_ctor_get(v_a_4797_, 0);
lean_inc(v_fst_4801_);
lean_dec(v_a_4797_);
if (lean_obj_tag(v_fst_4801_) == 0)
{
lean_object* v___x_4803_; 
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 0, v_a_4788_);
v___x_4803_ = v___x_4799_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4788_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
else
{
lean_object* v_val_4805_; lean_object* v___x_4807_; 
lean_dec(v_a_4788_);
v_val_4805_ = lean_ctor_get(v_fst_4801_, 0);
lean_inc(v_val_4805_);
lean_dec_ref_known(v_fst_4801_, 1);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 0, v_val_4805_);
v___x_4807_ = v___x_4799_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_val_4805_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
lean_dec(v_a_4788_);
v_a_4810_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4796_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4796_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
else
{
lean_object* v___x_4819_; 
lean_dec_ref(v_config_4780_);
lean_dec(v_mvarId_4778_);
if (v_isShared_4791_ == 0)
{
v___x_4819_ = v___x_4790_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4788_);
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
lean_dec_ref(v_config_4780_);
lean_dec(v_mvarId_4778_);
return v___x_4787_;
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec_ref(v_config_4780_);
lean_dec(v_mvarId_4778_);
v_a_4822_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4786_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4786_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4830_, lean_object* v___x_4831_, lean_object* v_config_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4830_, v___x_4831_, v_config_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4841_, lean_object* v_config_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_){
_start:
{
lean_object* v___x_4848_; lean_object* v___f_4849_; lean_object* v___x_4850_; 
v___x_4848_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4841_);
v___f_4849_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4849_, 0, v_mvarId_4841_);
lean_closure_set(v___f_4849_, 1, v___x_4848_);
lean_closure_set(v___f_4849_, 2, v_config_4842_);
v___x_4850_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4841_, v___f_4849_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4851_, lean_object* v_config_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l_Lean_MVarId_contradictionCore(v_mvarId_4851_, v_config_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4859_, lean_object* v_config_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_){
_start:
{
lean_object* v___x_4866_; 
lean_inc(v_mvarId_4859_);
v___x_4866_ = l_Lean_MVarId_contradictionCore(v_mvarId_4859_, v_config_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4879_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4869_ = v___x_4866_;
v_isShared_4870_ = v_isSharedCheck_4879_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4866_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4879_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
uint8_t v___x_4871_; 
v___x_4871_ = lean_unbox(v_a_4867_);
lean_dec(v_a_4867_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
lean_del_object(v___x_4869_);
v___x_4872_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4873_ = lean_box(0);
v___x_4874_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4872_, v_mvarId_4859_, v___x_4873_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
return v___x_4874_;
}
else
{
lean_object* v___x_4875_; lean_object* v___x_4877_; 
lean_dec(v_mvarId_4859_);
v___x_4875_ = lean_box(0);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v___x_4875_);
v___x_4877_ = v___x_4869_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
lean_dec(v_mvarId_4859_);
v_a_4880_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4866_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4866_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4888_, lean_object* v_config_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l_Lean_MVarId_contradiction(v_mvarId_4888_, v_config_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
lean_dec(v_a_4893_);
lean_dec_ref(v_a_4892_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4958_; uint8_t v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4958_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4959_ = 0;
v___x_4960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4961_ = l_Lean_registerTraceClass(v___x_4958_, v___x_4959_, v___x_4960_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4963_;
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
