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
lean_object* v_ref_599_; lean_object* v___x_600_; lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_646_; 
v_ref_599_ = lean_ctor_get(v___y_596_, 2);
v___x_600_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_646_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_646_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_646_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v_traceState_606_; lean_object* v_env_607_; lean_object* v_nextMacroScope_608_; lean_object* v_ngen_609_; lean_object* v_auxDeclNGen_610_; lean_object* v_cache_611_; lean_object* v_recordedDeps_612_; lean_object* v_messages_613_; lean_object* v_infoState_614_; lean_object* v_snapshotTasks_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_645_; 
v___x_605_ = lean_st_ref_take(v___y_597_);
v_traceState_606_ = lean_ctor_get(v___x_605_, 4);
v_env_607_ = lean_ctor_get(v___x_605_, 0);
v_nextMacroScope_608_ = lean_ctor_get(v___x_605_, 1);
v_ngen_609_ = lean_ctor_get(v___x_605_, 2);
v_auxDeclNGen_610_ = lean_ctor_get(v___x_605_, 3);
v_cache_611_ = lean_ctor_get(v___x_605_, 5);
v_recordedDeps_612_ = lean_ctor_get(v___x_605_, 6);
v_messages_613_ = lean_ctor_get(v___x_605_, 7);
v_infoState_614_ = lean_ctor_get(v___x_605_, 8);
v_snapshotTasks_615_ = lean_ctor_get(v___x_605_, 9);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_645_ == 0)
{
v___x_617_ = v___x_605_;
v_isShared_618_ = v_isSharedCheck_645_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snapshotTasks_615_);
lean_inc(v_infoState_614_);
lean_inc(v_messages_613_);
lean_inc(v_recordedDeps_612_);
lean_inc(v_cache_611_);
lean_inc(v_traceState_606_);
lean_inc(v_auxDeclNGen_610_);
lean_inc(v_ngen_609_);
lean_inc(v_nextMacroScope_608_);
lean_inc(v_env_607_);
lean_dec(v___x_605_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_645_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint64_t v_tid_619_; lean_object* v_traces_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_644_; 
v_tid_619_ = lean_ctor_get_uint64(v_traceState_606_, sizeof(void*)*1);
v_traces_620_ = lean_ctor_get(v_traceState_606_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_traceState_606_);
if (v_isSharedCheck_644_ == 0)
{
v___x_622_ = v_traceState_606_;
v_isShared_623_ = v_isSharedCheck_644_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_traces_620_);
lean_dec(v_traceState_606_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_644_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; double v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_624_ = lean_box(0);
v___x_625_ = lean_box(0);
v___x_626_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_627_ = 0;
v___x_628_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_629_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_629_, 0, v_cls_592_);
lean_ctor_set(v___x_629_, 1, v___x_625_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
lean_ctor_set_float(v___x_629_, sizeof(void*)*3, v___x_626_);
lean_ctor_set_float(v___x_629_, sizeof(void*)*3 + 8, v___x_626_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*3 + 16, v___x_627_);
v___x_630_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_631_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v_a_601_);
lean_ctor_set(v___x_631_, 2, v___x_630_);
lean_inc(v_ref_599_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_ref_599_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = l_Lean_PersistentArray_push___redArg(v_traces_620_, v___x_632_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_633_);
v___x_635_ = v___x_622_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_633_);
lean_ctor_set_uint64(v_reuseFailAlloc_643_, sizeof(void*)*1, v_tid_619_);
v___x_635_ = v_reuseFailAlloc_643_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v___x_635_);
v___x_637_ = v___x_617_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_env_607_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_nextMacroScope_608_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_ngen_609_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v_auxDeclNGen_610_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_642_, 5, v_cache_611_);
lean_ctor_set(v_reuseFailAlloc_642_, 6, v_recordedDeps_612_);
lean_ctor_set(v_reuseFailAlloc_642_, 7, v_messages_613_);
lean_ctor_set(v_reuseFailAlloc_642_, 8, v_infoState_614_);
lean_ctor_set(v_reuseFailAlloc_642_, 9, v_snapshotTasks_615_);
v___x_637_ = v_reuseFailAlloc_642_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_st_ref_put(v___y_597_, v___x_637_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_624_);
v___x_640_ = v___x_603_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_624_);
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
size_t v_sz_boxed_675_; size_t v___x_16033__boxed_676_; uint8_t v___x_16035__boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_675_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v___x_16033__boxed_676_ = lean_unbox_usize(v___x_666_);
lean_dec(v___x_666_);
v___x_16035__boxed_677_ = lean_unbox(v___x_668_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_662_, v_mvarId_663_, v_fields_664_, v_sz_boxed_675_, v___x_16033__boxed_676_, v___x_667_, v___x_16035__boxed_677_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
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
lean_object* v_a_766_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v_toCold_799_; lean_object* v_options_800_; uint8_t v_hasTrace_801_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v_toCold_799_ = lean_ctor_get(v___y_762_, 0);
v_options_800_ = lean_ctor_get(v_toCold_799_, 2);
v_hasTrace_801_ = lean_ctor_get_uint8(v_options_800_, sizeof(void*)*1);
if (v_hasTrace_801_ == 0)
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
lean_object* v_inheritedTraceOptions_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_inheritedTraceOptions_802_ = lean_ctor_get(v_toCold_799_, 11);
v___x_803_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_804_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_805_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_802_, v_options_800_, v___x_804_);
if (v___x_805_ == 0)
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
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_806_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_807_ = lean_array_get_size(v_a_766_);
v___x_808_ = l_Nat_reprFast(v___x_807_);
v___x_809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
v___x_810_ = l_Lean_MessageData_ofFormat(v___x_809_);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_806_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_803_, v___x_811_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_dec_ref_known(v___x_812_, 1);
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
goto v___jp_767_;
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v_a_766_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
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
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_866_; 
v_a_821_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_866_ == 0)
{
v___x_823_ = v___x_765_;
v_isShared_824_ = v_isSharedCheck_866_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_765_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_866_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___y_826_; uint8_t v___x_864_; 
v___x_864_ = l_Lean_Exception_isInterrupt(v_a_821_);
if (v___x_864_ == 0)
{
uint8_t v___x_865_; 
lean_inc(v_a_821_);
v___x_865_ = l_Lean_Exception_isRuntime(v_a_821_);
v___y_826_ = v___x_865_;
goto v___jp_825_;
}
else
{
v___y_826_ = v___x_864_;
goto v___jp_825_;
}
v___jp_825_:
{
if (v___y_826_ == 0)
{
lean_object* v_toCold_827_; lean_object* v_options_828_; uint8_t v_hasTrace_829_; 
v_toCold_827_ = lean_ctor_get(v___y_762_, 0);
v_options_828_ = lean_ctor_get(v_toCold_827_, 2);
v_hasTrace_829_ = lean_ctor_get_uint8(v_options_828_, sizeof(void*)*1);
if (v_hasTrace_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_832_; 
lean_dec(v_a_821_);
v___x_830_ = lean_box(v___x_755_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v___x_830_);
v___x_832_ = v___x_823_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
else
{
lean_object* v_inheritedTraceOptions_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_inheritedTraceOptions_834_ = lean_ctor_get(v_toCold_827_, 11);
v___x_835_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_836_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_837_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_834_, v_options_828_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_dec(v_a_821_);
v___x_838_ = lean_box(v___x_755_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v___x_838_);
v___x_840_ = v___x_823_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_del_object(v___x_823_);
v___x_842_ = l_Lean_Exception_toMessageData(v_a_821_);
v___x_843_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_835_, v___x_842_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_851_; 
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v___x_843_, 0);
lean_dec(v_unused_852_);
v___x_845_ = v___x_843_;
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
else
{
lean_dec(v___x_843_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = lean_box(v___x_755_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_843_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_843_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
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
else
{
lean_object* v___x_862_; 
if (v_isShared_824_ == 0)
{
v___x_862_ = v___x_823_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_821_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_867_, lean_object* v_fvarId_868_, lean_object* v___x_869_, lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v_val_872_, lean_object* v___x_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
uint8_t v___x_16155__boxed_880_; uint8_t v___x_16158__boxed_881_; lean_object* v_res_882_; 
v___x_16155__boxed_880_ = lean_unbox(v___x_870_);
v___x_16158__boxed_881_ = lean_unbox(v___x_873_);
v_res_882_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_867_, v_fvarId_868_, v___x_869_, v___x_16155__boxed_880_, v___x_871_, v_val_872_, v___x_16158__boxed_881_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
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
lean_object* v_a_1086_; lean_object* v___y_1088_; lean_object* v___y_1089_; uint8_t v___y_1090_; lean_object* v___y_1109_; lean_object* v_a_1110_; lean_object* v___x_1113_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
v___x_1113_ = lean_apply_5(v_x_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; uint8_t v___x_1115_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
v___x_1115_ = lean_unbox(v_a_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref_known(v___x_1113_, 1);
v___x_1116_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1086_, v___y_1081_, v___y_1083_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_a_1086_);
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
lean_ctor_set(v___x_1118_, 0, v_a_1114_);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1114_);
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
lean_dec(v_a_1114_);
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
lean_inc(v_a_1125_);
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
v___y_1109_ = v___x_1130_;
v_a_1110_ = v_a_1125_;
goto v___jp_1108_;
}
}
}
}
else
{
lean_dec(v_a_1114_);
lean_dec(v_a_1086_);
return v___x_1113_;
}
}
else
{
lean_object* v_a_1133_; 
v_a_1133_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1133_);
v___y_1109_ = v___x_1113_;
v_a_1110_ = v_a_1133_;
goto v___jp_1108_;
}
v___jp_1087_:
{
if (v___y_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_dec_ref(v___y_1089_);
v___x_1091_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1086_, v___y_1081_, v___y_1083_);
lean_dec(v_a_1086_);
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
lean_ctor_set(v___x_1093_, 0, v___y_1088_);
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___y_1088_);
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
lean_dec_ref(v___y_1088_);
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
lean_dec_ref(v___y_1088_);
lean_dec(v_a_1086_);
return v___y_1089_;
}
}
v___jp_1108_:
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Lean_Exception_isInterrupt(v_a_1110_);
if (v___x_1111_ == 0)
{
uint8_t v___x_1112_; 
lean_inc_ref(v_a_1110_);
v___x_1112_ = l_Lean_Exception_isRuntime(v_a_1110_);
v___y_1088_ = v_a_1110_;
v___y_1089_ = v___y_1109_;
v___y_1090_ = v___x_1112_;
goto v___jp_1087_;
}
else
{
v___y_1088_ = v_a_1110_;
v___y_1089_ = v___y_1109_;
v___y_1090_ = v___x_1111_;
goto v___jp_1087_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_x_1079_);
v_a_1134_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1085_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1085_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1149_, v_x_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1156_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1156_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1173_, lean_object* v_x_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1173_, v_x_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1181_, lean_object* v_mvarId_1182_, lean_object* v_x_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1182_, v_x_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_mvarId_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1190_, v_mvarId_1191_, v_x_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1199_, lean_object* v_fuel_1200_, lean_object* v_fvarId_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_MVarId_exfalso(v_mvarId_1199_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v___x_1209_ = lean_st_mk_ref(v_fuel_1200_);
v___x_1210_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1208_, v_fvarId_1201_, v___x_1209_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_st_ref_get(v___x_1209_);
lean_dec(v___x_1209_);
lean_dec(v___x_1215_);
if (v_isShared_1214_ == 0)
{
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1211_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_dec(v___x_1209_);
return v___x_1210_;
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_fvarId_1201_);
lean_dec(v_fuel_1200_);
v_a_1220_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1207_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1207_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1228_, lean_object* v_fuel_1229_, lean_object* v_fvarId_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1228_, v_fuel_1229_, v_fvarId_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1237_, lean_object* v___f_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1237_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; uint8_t v___x_1246_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
v___x_1246_ = lean_unbox(v_a_1245_);
lean_dec(v_a_1245_);
if (v___x_1246_ == 0)
{
lean_dec_ref(v___f_1238_);
return v___x_1244_;
}
else
{
lean_object* v___x_1247_; 
lean_dec_ref_known(v___x_1244_, 1);
v___x_1247_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v___x_1247_;
}
}
else
{
lean_dec_ref(v___f_1238_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1248_, lean_object* v___f_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1248_, v___f_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1256_, lean_object* v_fvarId_1257_, lean_object* v_fuel_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; 
lean_inc(v_fvarId_1257_);
lean_inc(v_mvarId_1256_);
v___f_1264_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1264_, 0, v_mvarId_1256_);
lean_closure_set(v___f_1264_, 1, v_fuel_1258_);
lean_closure_set(v___f_1264_, 2, v_fvarId_1257_);
v___f_1265_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1265_, 0, v_fvarId_1257_);
lean_closure_set(v___f_1265_, 1, v___f_1264_);
v___x_1266_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1256_, v___f_1265_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1267_, lean_object* v_fvarId_1268_, lean_object* v_fuel_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1267_, v_fvarId_1268_, v_fuel_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1276_){
_start:
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1278_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1281_, lean_object* v_acc_1282_){
_start:
{
if (lean_obj_tag(v_e_1281_) == 7)
{
lean_object* v_binderType_1283_; lean_object* v_body_1284_; uint8_t v___y_1286_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_binderType_1283_ = lean_ctor_get(v_e_1281_, 1);
v_body_1284_ = lean_ctor_get(v_e_1281_, 2);
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = lean_expr_has_loose_bvar(v_body_1284_, v___x_1290_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = l_Lean_Expr_isEq(v_binderType_1283_);
if (v___x_1292_ == 0)
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_Expr_isHEq(v_binderType_1283_);
v___y_1286_ = v___x_1293_;
goto v___jp_1285_;
}
else
{
v___y_1286_ = v___x_1292_;
goto v___jp_1285_;
}
}
else
{
uint8_t v___x_1294_; 
v___x_1294_ = 0;
v___y_1286_ = v___x_1294_;
goto v___jp_1285_;
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_box(v___y_1286_);
v___x_1288_ = lean_array_push(v_acc_1282_, v___x_1287_);
v_e_1281_ = v_body_1284_;
v_acc_1282_ = v___x_1288_;
goto _start;
}
}
else
{
return v_acc_1282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1295_, lean_object* v_acc_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1295_, v_acc_1296_);
lean_dec_ref(v_e_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1302_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1300_, v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Meta_mkGenDiseqMask(v_e_1303_);
lean_dec_ref(v_e_1303_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___f_1312_; lean_object* v___x_4344__overap_1313_; lean_object* v___x_1314_; 
v___f_1312_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1313_ = lean_panic_fn_borrowed(v___f_1312_, v_msg_1306_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
v___x_1314_ = lean_apply_5(v___x_4344__overap_1313_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, lean_box(0));
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1322_, lean_object* v___y_1323_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = l_Lean_Expr_hasMVar(v_e_1322_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v_e_1322_);
return v___x_1326_;
}
else
{
lean_object* v___x_1327_; lean_object* v_mctx_1328_; lean_object* v___x_1329_; lean_object* v_fst_1330_; lean_object* v_snd_1331_; lean_object* v___x_1332_; lean_object* v_cache_1333_; lean_object* v_zetaDeltaFVarIds_1334_; lean_object* v_postponed_1335_; lean_object* v_diag_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1345_; 
v___x_1327_ = lean_st_ref_get(v___y_1323_);
v_mctx_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc_ref(v_mctx_1328_);
lean_dec(v___x_1327_);
v___x_1329_ = l_Lean_instantiateMVarsCore(v_mctx_1328_, v_e_1322_);
v_fst_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_fst_1330_);
v_snd_1331_ = lean_ctor_get(v___x_1329_, 1);
lean_inc(v_snd_1331_);
lean_dec_ref(v___x_1329_);
v___x_1332_ = lean_st_ref_take(v___y_1323_);
v_cache_1333_ = lean_ctor_get(v___x_1332_, 1);
v_zetaDeltaFVarIds_1334_ = lean_ctor_get(v___x_1332_, 2);
v_postponed_1335_ = lean_ctor_get(v___x_1332_, 3);
v_diag_1336_ = lean_ctor_get(v___x_1332_, 4);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v___x_1332_, 0);
lean_dec(v_unused_1346_);
v___x_1338_ = v___x_1332_;
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_diag_1336_);
lean_inc(v_postponed_1335_);
lean_inc(v_zetaDeltaFVarIds_1334_);
lean_inc(v_cache_1333_);
lean_dec(v___x_1332_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v_snd_1331_);
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_snd_1331_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_cache_1333_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_zetaDeltaFVarIds_1334_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_postponed_1335_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_diag_1336_);
v___x_1341_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_st_ref_put(v___y_1323_, v___x_1341_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_fst_1330_);
return v___x_1343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1347_, v___y_1348_);
lean_dec(v___y_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1351_, v___y_1353_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1365_, uint8_t v_allowLevelAssignments_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1366_, v_k_1365_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1372_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1372_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1389_, lean_object* v_allowLevelAssignments_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1396_; lean_object* v_res_1397_; 
v_allowLevelAssignments_boxed_1396_ = lean_unbox(v_allowLevelAssignments_1390_);
v_res_1397_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1389_, v_allowLevelAssignments_boxed_1396_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1398_, lean_object* v_k_1399_, uint8_t v_allowLevelAssignments_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1399_, v_allowLevelAssignments_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1407_, lean_object* v_k_1408_, lean_object* v_allowLevelAssignments_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1415_; lean_object* v_res_1416_; 
v_allowLevelAssignments_boxed_1415_ = lean_unbox(v_allowLevelAssignments_1409_);
v_res_1416_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1407_, v_k_1408_, v_allowLevelAssignments_boxed_1415_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1419_, size_t v_sz_1420_, size_t v_i_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_a_1429_; uint8_t v___x_1433_; 
v___x_1433_ = lean_usize_dec_lt(v_i_1421_, v_sz_1420_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v_b_1422_);
return v___x_1434_;
}
else
{
lean_object* v_snd_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1597_; 
v_snd_1435_ = lean_ctor_get(v_b_1422_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_b_1422_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v_b_1422_, 0);
lean_dec(v_unused_1598_);
v___x_1437_ = v_b_1422_;
v_isShared_1438_ = v_isSharedCheck_1597_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_snd_1435_);
lean_dec(v_b_1422_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1597_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v_array_1439_; lean_object* v_start_1440_; lean_object* v_stop_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_array_1439_ = lean_ctor_get(v_snd_1435_, 0);
v_start_1440_ = lean_ctor_get(v_snd_1435_, 1);
v_stop_1441_ = lean_ctor_get(v_snd_1435_, 2);
v___x_1442_ = lean_box(0);
v___x_1443_ = lean_nat_dec_lt(v_start_1440_, v_stop_1441_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1445_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1442_);
v___x_1445_ = v___x_1437_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_snd_1435_);
v___x_1445_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
else
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1593_; 
lean_inc(v_stop_1441_);
lean_inc(v_start_1440_);
lean_inc_ref(v_array_1439_);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_snd_1435_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; lean_object* v_unused_1595_; lean_object* v_unused_1596_; 
v_unused_1594_ = lean_ctor_get(v_snd_1435_, 2);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_snd_1435_, 1);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_snd_1435_, 0);
lean_dec(v_unused_1596_);
v___x_1449_ = v_snd_1435_;
v_isShared_1450_ = v_isSharedCheck_1593_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v_snd_1435_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1593_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1451_ = lean_array_fget(v_array_1439_, v_start_1440_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_start_1440_, v___x_1452_);
lean_dec(v_start_1440_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 1, v___x_1453_);
v___x_1455_ = v___x_1449_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_array_1439_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_stop_1441_);
v___x_1455_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_unbox(v___x_1451_);
lean_dec(v___x_1451_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1458_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v___x_1455_);
lean_ctor_set(v___x_1437_, 0, v___x_1442_);
v___x_1458_ = v___x_1437_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1455_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
v_a_1429_ = v___x_1458_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1460_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___x_1532_; 
v_a_1460_ = lean_array_uget_borrowed(v_as_1419_, v_i_1421_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v_a_1460_);
v___x_1532_ = lean_infer_type(v_a_1460_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = l_Lean_Meta_matchEq_x3f(v_a_1533_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
if (lean_obj_tag(v_a_1535_) == 1)
{
lean_object* v_val_1536_; lean_object* v_snd_1537_; lean_object* v_fst_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1574_; 
v_val_1536_ = lean_ctor_get(v_a_1535_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v_a_1535_, 1);
v_snd_1537_ = lean_ctor_get(v_val_1536_, 1);
lean_inc(v_snd_1537_);
lean_dec(v_val_1536_);
v_fst_1538_ = lean_ctor_get(v_snd_1537_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_snd_1537_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v_snd_1537_, 1);
lean_dec(v_unused_1575_);
v___x_1540_ = v_snd_1537_;
v_isShared_1541_ = v_isSharedCheck_1574_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_fst_1538_);
lean_dec(v_snd_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1574_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Meta_mkEqRefl(v_fst_1538_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
lean_inc(v_a_1460_);
v___x_1544_ = l_Lean_Meta_isExprDefEq(v_a_1460_, v_a_1543_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1557_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1557_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1557_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
uint8_t v___x_1549_; 
v___x_1549_ = lean_unbox(v_a_1545_);
lean_dec(v_a_1545_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_del_object(v___x_1437_);
v___x_1550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 1, v___x_1455_);
lean_ctor_set(v___x_1540_, 0, v___x_1550_);
v___x_1552_ = v___x_1540_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1455_);
v___x_1552_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1552_);
v___x_1554_ = v___x_1547_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_del_object(v___x_1547_);
lean_del_object(v___x_1540_);
v___y_1462_ = v___y_1423_;
v___y_1463_ = v___y_1424_;
v___y_1464_ = v___y_1425_;
v___y_1465_ = v___y_1426_;
goto v___jp_1461_;
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1540_);
lean_dec_ref(v___x_1455_);
lean_del_object(v___x_1437_);
v_a_1558_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1544_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1544_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_del_object(v___x_1540_);
lean_dec_ref(v___x_1455_);
lean_del_object(v___x_1437_);
v_a_1566_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1542_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1542_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
else
{
lean_dec(v_a_1535_);
v___y_1462_ = v___y_1423_;
v___y_1463_ = v___y_1424_;
v___y_1464_ = v___y_1425_;
v___y_1465_ = v___y_1426_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v___x_1455_);
lean_del_object(v___x_1437_);
v_a_1576_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1534_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1534_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v___x_1455_);
lean_del_object(v___x_1437_);
v_a_1584_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1532_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1532_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
v___jp_1461_:
{
lean_object* v___x_1466_; 
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v_a_1460_);
v___x_1466_ = lean_infer_type(v_a_1460_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1468_ = l_Lean_Meta_matchHEq_x3f(v_a_1467_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
if (lean_obj_tag(v_a_1469_) == 1)
{
lean_object* v_val_1470_; lean_object* v_snd_1471_; lean_object* v_fst_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1511_; 
lean_del_object(v___x_1437_);
v_val_1470_ = lean_ctor_get(v_a_1469_, 0);
lean_inc(v_val_1470_);
lean_dec_ref_known(v_a_1469_, 1);
v_snd_1471_ = lean_ctor_get(v_val_1470_, 1);
lean_inc(v_snd_1471_);
lean_dec(v_val_1470_);
v_fst_1472_ = lean_ctor_get(v_snd_1471_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_snd_1471_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v_snd_1471_, 1);
lean_dec(v_unused_1512_);
v___x_1474_ = v_snd_1471_;
v_isShared_1475_ = v_isSharedCheck_1511_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_fst_1472_);
lean_dec(v_snd_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1511_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Meta_mkHEqRefl(v_fst_1472_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
lean_inc(v_a_1460_);
v___x_1478_ = l_Lean_Meta_isExprDefEq(v_a_1460_, v_a_1477_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1494_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1494_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1494_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_unbox(v_a_1479_);
lean_dec(v_a_1479_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1455_);
lean_ctor_set(v___x_1474_, 0, v___x_1484_);
v___x_1486_ = v___x_1474_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1455_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1486_);
v___x_1488_ = v___x_1481_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_object* v___x_1492_; 
lean_del_object(v___x_1481_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1455_);
lean_ctor_set(v___x_1474_, 0, v___x_1442_);
v___x_1492_ = v___x_1474_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1455_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
v_a_1429_ = v___x_1492_;
goto v___jp_1428_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_del_object(v___x_1474_);
lean_dec_ref(v___x_1455_);
v_a_1495_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1478_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1478_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_del_object(v___x_1474_);
lean_dec_ref(v___x_1455_);
v_a_1503_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1476_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1476_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
else
{
lean_object* v___x_1514_; 
lean_dec(v_a_1469_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v___x_1455_);
lean_ctor_set(v___x_1437_, 0, v___x_1442_);
v___x_1514_ = v___x_1437_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1455_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
v_a_1429_ = v___x_1514_;
goto v___jp_1428_;
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec_ref(v___x_1455_);
lean_del_object(v___x_1437_);
v_a_1516_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1468_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1468_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v___x_1455_);
lean_del_object(v___x_1437_);
v_a_1524_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1466_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1466_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
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
v___jp_1428_:
{
size_t v___x_1430_; size_t v___x_1431_; 
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_add(v_i_1421_, v___x_1430_);
v_i_1421_ = v___x_1431_;
v_b_1422_ = v_a_1429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1599_, lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1599_, v_sz_boxed_1608_, v_i_boxed_1609_, v_b_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_as_1599_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1611_, uint8_t v___x_1612_, lean_object* v_localDecl_1613_, lean_object* v_mvarId_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; 
lean_inc_ref(v___x_1611_);
v___x_1620_ = l_Lean_Meta_forallMetaTelescope(v___x_1611_, v___x_1612_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v_fst_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1711_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v_fst_1622_ = lean_ctor_get(v_a_1621_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_a_1621_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v_a_1621_, 1);
lean_dec(v_unused_1712_);
v___x_1624_ = v_a_1621_;
v_isShared_1625_ = v_isSharedCheck_1711_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_fst_1622_);
lean_dec(v_a_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1711_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1626_ = l_Lean_Meta_mkGenDiseqMask(v___x_1611_);
lean_dec_ref(v___x_1611_);
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = lean_array_get_size(v___x_1626_);
v___x_1629_ = l_Array_toSubarray___redArg(v___x_1626_, v___x_1627_, v___x_1628_);
v___x_1630_ = lean_box(0);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v___x_1629_);
lean_ctor_set(v___x_1624_, 0, v___x_1630_);
v___x_1632_ = v___x_1624_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1629_);
v___x_1632_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
size_t v_sz_1633_; size_t v___x_1634_; lean_object* v___x_1635_; 
v_sz_1633_ = lean_array_size(v_fst_1622_);
v___x_1634_ = ((size_t)0ULL);
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1622_, v_sz_1633_, v___x_1634_, v___x_1632_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1701_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1701_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1701_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_fst_1640_; 
v_fst_1640_ = lean_ctor_get(v_a_1636_, 0);
lean_inc(v_fst_1640_);
lean_dec(v_a_1636_);
if (lean_obj_tag(v_fst_1640_) == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1696_; 
lean_del_object(v___x_1638_);
v___x_1641_ = l_Lean_LocalDecl_toExpr(v_localDecl_1613_);
v___x_1642_ = l_Lean_mkAppN(v___x_1641_, v_fst_1622_);
lean_dec(v_fst_1622_);
v___x_1643_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1642_, v___y_1616_);
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1696_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1696_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; 
lean_inc(v_a_1644_);
v___x_1648_ = l_Lean_Meta_hasAssignableMVar(v_a_1644_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1687_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1687_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1687_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
lean_del_object(v___x_1651_);
v___x_1654_ = l_Lean_MVarId_getType(v_mvarId_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1656_ = l_Lean_Meta_mkFalseElim(v_a_1655_, v_a_1644_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1667_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1667_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1667_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 1);
lean_ctor_set(v___x_1646_, 0, v_a_1657_);
v___x_1662_ = v___x_1646_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1662_);
v___x_1664_ = v___x_1659_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_del_object(v___x_1646_);
v_a_1668_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1656_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1656_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_1646_);
lean_dec(v_a_1644_);
v_a_1676_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1654_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1654_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
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
lean_object* v___x_1685_; 
lean_del_object(v___x_1646_);
lean_dec(v_a_1644_);
lean_dec(v_mvarId_1614_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1630_);
v___x_1685_ = v___x_1651_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1630_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_del_object(v___x_1646_);
lean_dec(v_a_1644_);
lean_dec(v_mvarId_1614_);
v_a_1688_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1648_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1648_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
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
}
else
{
lean_object* v_val_1697_; lean_object* v___x_1699_; 
lean_dec(v_fst_1622_);
lean_dec(v_mvarId_1614_);
lean_dec_ref(v_localDecl_1613_);
v_val_1697_ = lean_ctor_get(v_fst_1640_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v_fst_1640_, 1);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v_val_1697_);
v___x_1699_ = v___x_1638_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_val_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_fst_1622_);
lean_dec(v_mvarId_1614_);
lean_dec_ref(v_localDecl_1613_);
v_a_1702_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1635_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1635_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_mvarId_1614_);
lean_dec_ref(v_localDecl_1613_);
lean_dec_ref(v___x_1611_);
v_a_1713_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1620_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1620_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v_localDecl_1723_, lean_object* v_mvarId_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v___x_6078__boxed_1730_; lean_object* v_res_1731_; 
v___x_6078__boxed_1730_ = lean_unbox(v___x_1722_);
v_res_1731_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1721_, v___x_6078__boxed_1730_, v_localDecl_1723_, v_mvarId_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v_res_1731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1736_ = lean_unsigned_to_nat(2u);
v___x_1737_ = lean_unsigned_to_nat(120u);
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1740_ = l_mkPanicMessageWithDecl(v___x_1739_, v___x_1738_, v___x_1737_, v___x_1736_, v___x_1735_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1741_, lean_object* v_localDecl_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = l_Lean_LocalDecl_type(v_localDecl_1742_);
lean_inc_ref(v___x_1748_);
v___x_1749_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec_ref(v___x_1748_);
lean_dec_ref(v_localDecl_1742_);
lean_dec(v_mvarId_1741_);
v___x_1750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1751_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1750_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
return v___x_1751_;
}
else
{
uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___f_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1752_ = 0;
v___x_1753_ = lean_box(v___x_1752_);
lean_inc(v_mvarId_1741_);
v___f_1754_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1754_, 0, v___x_1748_);
lean_closure_set(v___f_1754_, 1, v___x_1753_);
lean_closure_set(v___f_1754_, 2, v_localDecl_1742_);
lean_closure_set(v___f_1754_, 3, v_mvarId_1741_);
v___x_1755_ = 0;
v___x_1756_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1754_, v___x_1755_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1776_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1776_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1776_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
if (lean_obj_tag(v_a_1757_) == 1)
{
lean_object* v_val_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1770_; 
lean_del_object(v___x_1759_);
v_val_1761_ = lean_ctor_get(v_a_1757_, 0);
lean_inc(v_val_1761_);
lean_dec_ref_known(v_a_1757_, 1);
v___x_1762_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1741_, v_val_1761_, v_a_1744_);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v___x_1762_, 0);
lean_dec(v_unused_1771_);
v___x_1764_ = v___x_1762_;
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v___x_1762_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = lean_box(v___x_1749_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1768_ = v___x_1764_;
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
else
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
lean_dec(v_a_1757_);
lean_dec(v_mvarId_1741_);
v___x_1772_ = lean_box(v___x_1755_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1772_);
v___x_1774_ = v___x_1759_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
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
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_mvarId_1741_);
v_a_1777_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1756_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1756_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1785_, lean_object* v_localDecl_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1785_, v_localDecl_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
return v_res_1792_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_box(0);
v___x_1805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1806_ = l_Lean_mkConst(v___x_1805_, v___x_1804_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1807_; lean_object* v_dummy_1808_; 
v___x_1807_ = lean_box(0);
v_dummy_1808_ = l_Lean_Expr_sort___override(v___x_1807_);
return v_dummy_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1809_, lean_object* v_mvarId_1810_, lean_object* v_as_1811_, size_t v_sz_1812_, size_t v_i_1813_, lean_object* v_b_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_usize_dec_lt(v_i_1813_, v_sz_1812_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; 
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v_b_1814_);
return v___x_1821_;
}
else
{
lean_object* v_snd_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_2472_; 
v_snd_1822_ = lean_ctor_get(v_b_1814_, 1);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_b_1814_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; 
v_unused_2473_ = lean_ctor_get(v_b_1814_, 0);
lean_dec(v_unused_2473_);
v___x_1824_ = v_b_1814_;
v_isShared_1825_ = v_isSharedCheck_2472_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_snd_1822_);
lean_dec(v_b_1814_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_2472_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_a_1827_; lean_object* v___x_1833_; lean_object* v_a_1835_; lean_object* v_a_1840_; 
v___x_1833_ = lean_box(0);
v_a_1840_ = lean_array_uget(v_as_1811_, v_i_1813_);
if (lean_obj_tag(v_a_1840_) == 0)
{
lean_del_object(v___x_1824_);
v_a_1835_ = v_snd_1822_;
goto v___jp_1834_;
}
else
{
lean_object* v_val_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_2471_; 
v_val_1841_ = lean_ctor_get(v_a_1840_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_a_1840_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_1843_ = v_a_1840_;
v_isShared_1844_ = v_isSharedCheck_2471_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_val_1841_);
lean_dec(v_a_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_2471_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___x_1886_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v___y_1913_; uint8_t v___x_1914_; lean_object* v___y_1916_; uint8_t v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1922_; uint8_t v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; uint8_t v___y_1927_; uint8_t v___y_1929_; uint8_t v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; uint8_t v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; uint8_t v___y_1943_; 
v___x_1845_ = lean_box(0);
v___x_1886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1914_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1841_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1958_; uint8_t v___y_1960_; uint8_t v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1969_; lean_object* v___y_1970_; uint8_t v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; uint8_t v___y_1974_; lean_object* v___y_1975_; uint8_t v___y_1976_; lean_object* v___y_1979_; uint8_t v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; uint8_t v___y_1983_; lean_object* v___y_1984_; lean_object* v_a_1985_; lean_object* v___y_1989_; lean_object* v___y_1990_; uint8_t v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; uint8_t v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_2033_; uint8_t v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; uint8_t v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; uint8_t v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; lean_object* v___y_2070_; uint8_t v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; uint8_t v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; uint8_t v___y_2077_; lean_object* v___y_2080_; uint8_t v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; uint8_t v___y_2084_; lean_object* v___y_2085_; uint8_t v___y_2086_; lean_object* v___y_2099_; uint8_t v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; uint8_t v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; uint8_t v___y_2107_; uint8_t v_isHEq_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; uint8_t v___y_2122_; uint8_t v_isEq_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___x_2408_; 
v___x_1958_ = l_Lean_LocalDecl_type(v_val_1841_);
lean_inc_ref(v___x_1958_);
v___x_2408_ = l_Lean_Meta_matchNot_x3f(v___x_1958_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
if (lean_obj_tag(v_a_2409_) == 1)
{
lean_object* v_val_2410_; lean_object* v___x_2411_; 
v_val_2410_ = lean_ctor_get(v_a_2409_, 0);
lean_inc(v_val_2410_);
lean_dec_ref_known(v_a_2409_, 1);
v___x_2411_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2410_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
if (lean_obj_tag(v_a_2412_) == 1)
{
lean_object* v_val_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2454_; 
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec_ref(v_config_1809_);
v_val_2413_ = lean_ctor_get(v_a_2412_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_a_2412_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2415_ = v_a_2412_;
v_isShared_2416_ = v_isSharedCheck_2454_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_val_2413_);
lean_dec(v_a_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2454_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; 
lean_inc(v_mvarId_1810_);
v___x_2417_ = l_Lean_MVarId_getType(v_mvarId_1810_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = l_Lean_LocalDecl_toExpr(v_val_1841_);
v___x_2420_ = l_Lean_mkFVar(v_val_2413_);
v___x_2421_ = l_Lean_Expr_app___override(v___x_2419_, v___x_2420_);
v___x_2422_ = l_Lean_Meta_mkFalseElim(v_a_2418_, v___x_2421_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v___x_2424_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1810_, v_a_2423_, v___y_1816_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
lean_dec_ref_known(v___x_2424_, 1);
v___x_2425_ = lean_box(v___x_1820_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2425_);
v___x_2427_ = v___x_2415_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___x_1845_);
v_a_1827_ = v___x_2428_;
goto v___jp_1826_;
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_del_object(v___x_2415_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
v_a_2430_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2424_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2424_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_del_object(v___x_2415_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2438_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2422_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2422_);
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
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_del_object(v___x_2415_);
lean_dec(v_val_2413_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2446_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2417_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2417_);
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
}
}
else
{
lean_dec(v_a_2412_);
v___y_2274_ = v___y_1815_;
v___y_2275_ = v___y_1816_;
v___y_2276_ = v___y_1817_;
v___y_2277_ = v___y_1818_;
goto v___jp_2273_;
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2455_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2411_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2411_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_dec(v_a_2409_);
v___y_2274_ = v___y_1815_;
v___y_2275_ = v___y_1816_;
v___y_2276_ = v___y_1817_;
v___y_2277_ = v___y_1818_;
goto v___jp_2273_;
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2463_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2408_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2408_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
v___jp_1959_:
{
uint8_t v_genDiseq_1966_; 
v_genDiseq_1966_ = lean_ctor_get_uint8(v_config_1809_, sizeof(void*)*1 + 2);
if (v_genDiseq_1966_ == 0)
{
lean_dec_ref(v___x_1958_);
v___y_1937_ = v___y_1960_;
v___y_1938_ = v___y_1962_;
v___y_1939_ = v___y_1963_;
v___y_1940_ = v___y_1961_;
v___y_1941_ = v___y_1965_;
v___y_1942_ = v___y_1964_;
v___y_1943_ = v___x_1914_;
goto v___jp_1936_;
}
else
{
uint8_t v___x_1967_; 
v___x_1967_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1958_);
v___y_1937_ = v___y_1960_;
v___y_1938_ = v___y_1962_;
v___y_1939_ = v___y_1963_;
v___y_1940_ = v___y_1961_;
v___y_1941_ = v___y_1965_;
v___y_1942_ = v___y_1964_;
v___y_1943_ = v___x_1967_;
goto v___jp_1936_;
}
}
v___jp_1968_:
{
if (v___y_1976_ == 0)
{
lean_dec_ref(v___y_1970_);
v___y_1960_ = v___y_1971_;
v___y_1961_ = v___y_1974_;
v___y_1962_ = v___y_1973_;
v___y_1963_ = v___y_1972_;
v___y_1964_ = v___y_1975_;
v___y_1965_ = v___y_1969_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1977_; 
lean_dec_ref(v___x_1958_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___y_1970_);
return v___x_1977_;
}
}
v___jp_1978_:
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Lean_Exception_isInterrupt(v_a_1985_);
if (v___x_1986_ == 0)
{
uint8_t v___x_1987_; 
lean_inc_ref(v_a_1985_);
v___x_1987_ = l_Lean_Exception_isRuntime(v_a_1985_);
v___y_1969_ = v___y_1979_;
v___y_1970_ = v_a_1985_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1983_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___x_1987_;
goto v___jp_1968_;
}
else
{
v___y_1969_ = v___y_1979_;
v___y_1970_ = v_a_1985_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1983_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___x_1986_;
goto v___jp_1968_;
}
}
v___jp_1988_:
{
if (lean_obj_tag(v___y_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v_a_1997_ = lean_ctor_get(v___y_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___y_1996_, 1);
v___x_1998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_1999_ = l_Lean_Expr_isConstOf(v_a_1997_, v___x_1998_);
lean_dec(v_a_1997_);
if (v___x_1999_ == 0)
{
lean_dec_ref(v___y_1990_);
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1994_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1992_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1989_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_2000_; 
lean_inc_ref(v___y_1990_);
v___x_2000_ = l_Lean_Meta_mkEqRefl(v___y_1990_, v___y_1993_, v___y_1992_, v___y_1995_, v___y_1989_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; lean_object* v_dummy_2003_; lean_object* v_nargs_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2003_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2004_ = l_Lean_Expr_getAppNumArgs(v___y_1990_);
lean_inc(v_nargs_2004_);
v___x_2005_ = lean_mk_array(v_nargs_2004_, v_dummy_2003_);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_sub(v_nargs_2004_, v___x_2006_);
lean_dec(v_nargs_2004_);
v___x_2008_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1990_, v___x_2005_, v___x_2007_);
v___x_2009_ = lean_array_push(v___x_2008_, v_a_2001_);
v___x_2010_ = l_Lean_mkAppN(v___x_2002_, v___x_2009_);
lean_dec_ref(v___x_2009_);
lean_inc(v_mvarId_1810_);
v___x_2011_ = l_Lean_MVarId_getType(v_mvarId_1810_, v___y_1993_, v___y_1992_, v___y_1995_, v___y_1989_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
lean_inc(v_val_1841_);
v___x_2013_ = l_Lean_LocalDecl_toExpr(v_val_1841_);
v___x_2014_ = l_Lean_Meta_mkAbsurd(v_a_2012_, v___x_2013_, v___x_2010_, v___y_1993_, v___y_1992_, v___y_1995_, v___y_1989_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
lean_inc(v_mvarId_1810_);
v___x_2016_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1810_, v_a_2015_, v___y_1992_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v___x_1958_);
lean_dec(v_val_1841_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_2016_, 0);
lean_dec(v_unused_2026_);
v___x_2018_ = v___x_2016_;
v_isShared_2019_ = v_isSharedCheck_2025_;
goto v_resetjp_2017_;
}
else
{
lean_dec(v___x_2016_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2025_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_box(v___x_1820_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 1);
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v___x_1845_);
v_a_1827_ = v___x_2023_;
goto v___jp_1826_;
}
}
}
else
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2016_, 1);
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v_a_1985_ = v_a_2027_;
goto v___jp_1978_;
}
}
else
{
lean_object* v_a_2028_; 
v_a_2028_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2014_, 1);
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v_a_1985_ = v_a_2028_;
goto v___jp_1978_;
}
}
else
{
lean_object* v_a_2029_; 
lean_dec_ref(v___x_2010_);
v_a_2029_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v_a_1985_ = v_a_2029_;
goto v___jp_1978_;
}
}
else
{
lean_object* v_a_2030_; 
lean_dec_ref(v___y_1990_);
v_a_2030_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2000_, 1);
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v_a_1985_ = v_a_2030_;
goto v___jp_1978_;
}
}
}
else
{
lean_object* v_a_2031_; 
lean_dec_ref(v___y_1990_);
v_a_2031_ = lean_ctor_get(v___y_1996_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___y_1996_, 1);
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v_a_1985_ = v_a_2031_;
goto v___jp_1978_;
}
}
v___jp_2032_:
{
lean_object* v___x_2039_; 
lean_inc_ref(v___x_1958_);
v___x_2039_ = l_Lean_Meta_mkDecide(v___x_1958_, v___y_2036_, v___y_2035_, v___y_2038_, v___y_2033_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; uint8_t v_transparency_2042_; uint8_t v___x_2043_; uint8_t v___x_2044_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_Meta_Context_config(v___y_2036_);
v_transparency_2042_ = lean_ctor_get_uint8(v___x_2041_, 9);
lean_dec_ref(v___x_2041_);
v___x_2043_ = 1;
v___x_2044_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v_keyedConfig_2045_; uint8_t v_trackZetaDelta_2046_; lean_object* v_zetaDeltaSet_2047_; lean_object* v_lctx_2048_; lean_object* v_localInstances_2049_; lean_object* v_defEqCtx_x3f_2050_; lean_object* v_synthPendingDepth_2051_; lean_object* v_customCanUnfoldPredicate_x3f_2052_; uint8_t v_univApprox_2053_; uint8_t v_inTypeClassResolution_2054_; uint8_t v_cacheInferType_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_keyedConfig_2045_ = lean_ctor_get(v___y_2036_, 0);
v_trackZetaDelta_2046_ = lean_ctor_get_uint8(v___y_2036_, sizeof(void*)*7);
v_zetaDeltaSet_2047_ = lean_ctor_get(v___y_2036_, 1);
v_lctx_2048_ = lean_ctor_get(v___y_2036_, 2);
v_localInstances_2049_ = lean_ctor_get(v___y_2036_, 3);
v_defEqCtx_x3f_2050_ = lean_ctor_get(v___y_2036_, 4);
v_synthPendingDepth_2051_ = lean_ctor_get(v___y_2036_, 5);
v_customCanUnfoldPredicate_x3f_2052_ = lean_ctor_get(v___y_2036_, 6);
v_univApprox_2053_ = lean_ctor_get_uint8(v___y_2036_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2054_ = lean_ctor_get_uint8(v___y_2036_, sizeof(void*)*7 + 2);
v_cacheInferType_2055_ = lean_ctor_get_uint8(v___y_2036_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2045_);
v___x_2056_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2043_, v_keyedConfig_2045_);
lean_inc(v_customCanUnfoldPredicate_x3f_2052_);
lean_inc(v_synthPendingDepth_2051_);
lean_inc(v_defEqCtx_x3f_2050_);
lean_inc_ref(v_localInstances_2049_);
lean_inc_ref(v_lctx_2048_);
lean_inc(v_zetaDeltaSet_2047_);
v___x_2057_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
lean_ctor_set(v___x_2057_, 1, v_zetaDeltaSet_2047_);
lean_ctor_set(v___x_2057_, 2, v_lctx_2048_);
lean_ctor_set(v___x_2057_, 3, v_localInstances_2049_);
lean_ctor_set(v___x_2057_, 4, v_defEqCtx_x3f_2050_);
lean_ctor_set(v___x_2057_, 5, v_synthPendingDepth_2051_);
lean_ctor_set(v___x_2057_, 6, v_customCanUnfoldPredicate_x3f_2052_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*7, v_trackZetaDelta_2046_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*7 + 1, v_univApprox_2053_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2054_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*7 + 3, v_cacheInferType_2055_);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2038_);
lean_inc(v___y_2035_);
lean_inc(v_a_2040_);
v___x_2058_ = lean_whnf(v_a_2040_, v___x_2057_, v___y_2035_, v___y_2038_, v___y_2033_);
v___y_1989_ = v___y_2033_;
v___y_1990_ = v_a_2040_;
v___y_1991_ = v___y_2034_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___y_2036_;
v___y_1994_ = v___y_2037_;
v___y_1995_ = v___y_2038_;
v___y_1996_ = v___x_2058_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2059_; 
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2038_);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2036_);
lean_inc(v_a_2040_);
v___x_2059_ = lean_whnf(v_a_2040_, v___y_2036_, v___y_2035_, v___y_2038_, v___y_2033_);
v___y_1989_ = v___y_2033_;
v___y_1990_ = v_a_2040_;
v___y_1991_ = v___y_2034_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___y_2036_;
v___y_1994_ = v___y_2037_;
v___y_1995_ = v___y_2038_;
v___y_1996_ = v___x_2059_;
goto v___jp_1988_;
}
}
else
{
lean_object* v_a_2060_; 
v_a_2060_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2039_, 1);
v___y_1979_ = v___y_2033_;
v___y_1980_ = v___y_2034_;
v___y_1981_ = v___y_2035_;
v___y_1982_ = v___y_2036_;
v___y_1983_ = v___y_2037_;
v___y_1984_ = v___y_2038_;
v_a_1985_ = v_a_2060_;
goto v___jp_1978_;
}
}
v___jp_2061_:
{
if (v___y_2068_ == 0)
{
v___y_1960_ = v___y_2063_;
v___y_1961_ = v___y_2066_;
v___y_1962_ = v___y_2065_;
v___y_1963_ = v___y_2064_;
v___y_1964_ = v___y_2067_;
v___y_1965_ = v___y_2062_;
goto v___jp_1959_;
}
else
{
v___y_2033_ = v___y_2062_;
v___y_2034_ = v___y_2063_;
v___y_2035_ = v___y_2064_;
v___y_2036_ = v___y_2065_;
v___y_2037_ = v___y_2066_;
v___y_2038_ = v___y_2067_;
goto v___jp_2032_;
}
}
v___jp_2069_:
{
if (v___y_2077_ == 0)
{
lean_dec_ref(v___y_2075_);
v___y_2062_ = v___y_2070_;
v___y_2063_ = v___y_2071_;
v___y_2064_ = v___y_2072_;
v___y_2065_ = v___y_2073_;
v___y_2066_ = v___y_2074_;
v___y_2067_ = v___y_2076_;
v___y_2068_ = v___x_1914_;
goto v___jp_2061_;
}
else
{
uint8_t v___x_2078_; 
v___x_2078_ = l_Lean_Expr_hasFVar(v___y_2075_);
lean_dec_ref(v___y_2075_);
if (v___x_2078_ == 0)
{
v___y_2033_ = v___y_2070_;
v___y_2034_ = v___y_2071_;
v___y_2035_ = v___y_2072_;
v___y_2036_ = v___y_2073_;
v___y_2037_ = v___y_2074_;
v___y_2038_ = v___y_2076_;
goto v___jp_2032_;
}
else
{
v___y_2062_ = v___y_2070_;
v___y_2063_ = v___y_2071_;
v___y_2064_ = v___y_2072_;
v___y_2065_ = v___y_2073_;
v___y_2066_ = v___y_2074_;
v___y_2067_ = v___y_2076_;
v___y_2068_ = v___x_1914_;
goto v___jp_2061_;
}
}
}
v___jp_2079_:
{
lean_object* v___x_2087_; 
lean_inc_ref(v___x_1958_);
v___x_2087_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1958_, v___y_2082_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; uint8_t v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = l_Lean_Expr_hasMVar(v_a_2088_);
if (v___x_2089_ == 0)
{
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v___y_2082_;
v___y_2073_ = v___y_2083_;
v___y_2074_ = v___y_2084_;
v___y_2075_ = v_a_2088_;
v___y_2076_ = v___y_2085_;
v___y_2077_ = v___y_2086_;
goto v___jp_2069_;
}
else
{
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v___y_2082_;
v___y_2073_ = v___y_2083_;
v___y_2074_ = v___y_2084_;
v___y_2075_ = v_a_2088_;
v___y_2076_ = v___y_2085_;
v___y_2077_ = v___x_1914_;
goto v___jp_2069_;
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v___x_1958_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2090_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2087_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2087_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
v___jp_2098_:
{
if (v___y_2105_ == 0)
{
v___y_1960_ = v___y_2100_;
v___y_1961_ = v___y_2103_;
v___y_1962_ = v___y_2102_;
v___y_1963_ = v___y_2101_;
v___y_1964_ = v___y_2104_;
v___y_1965_ = v___y_2099_;
goto v___jp_1959_;
}
else
{
v___y_2080_ = v___y_2099_;
v___y_2081_ = v___y_2100_;
v___y_2082_ = v___y_2101_;
v___y_2083_ = v___y_2102_;
v___y_2084_ = v___y_2103_;
v___y_2085_ = v___y_2104_;
v___y_2086_ = v___y_2105_;
goto v___jp_2079_;
}
}
v___jp_2106_:
{
uint8_t v_useDecide_2113_; 
v_useDecide_2113_ = lean_ctor_get_uint8(v_config_1809_, sizeof(void*)*1);
if (v_useDecide_2113_ == 0)
{
v___y_2099_ = v___y_2112_;
v___y_2100_ = v_isHEq_2108_;
v___y_2101_ = v___y_2110_;
v___y_2102_ = v___y_2109_;
v___y_2103_ = v___y_2107_;
v___y_2104_ = v___y_2111_;
v___y_2105_ = v___x_1914_;
goto v___jp_2098_;
}
else
{
uint8_t v___x_2114_; 
v___x_2114_ = l_Lean_Expr_hasFVar(v___x_1958_);
if (v___x_2114_ == 0)
{
v___y_2080_ = v___y_2112_;
v___y_2081_ = v_isHEq_2108_;
v___y_2082_ = v___y_2110_;
v___y_2083_ = v___y_2109_;
v___y_2084_ = v___y_2107_;
v___y_2085_ = v___y_2111_;
v___y_2086_ = v_useDecide_2113_;
goto v___jp_2079_;
}
else
{
v___y_2099_ = v___y_2112_;
v___y_2100_ = v_isHEq_2108_;
v___y_2101_ = v___y_2110_;
v___y_2102_ = v___y_2109_;
v___y_2103_ = v___y_2107_;
v___y_2104_ = v___y_2111_;
v___y_2105_ = v___x_1914_;
goto v___jp_2098_;
}
}
}
v___jp_2115_:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Meta_isExprDefEq(v___y_2118_, v___y_2119_, v___y_2121_, v___y_2120_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; uint8_t v___x_2125_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = lean_unbox(v_a_2124_);
lean_dec(v_a_2124_);
if (v___x_2125_ == 0)
{
v___y_2107_ = v___y_2122_;
v_isHEq_2108_ = v___x_1820_;
v___y_2109_ = v___y_2121_;
v___y_2110_ = v___y_2120_;
v___y_2111_ = v___y_2116_;
v___y_2112_ = v___y_2117_;
goto v___jp_2106_;
}
else
{
lean_object* v___x_2126_; 
lean_dec_ref(v___x_1958_);
lean_dec_ref(v_config_1809_);
lean_inc(v_mvarId_1810_);
v___x_2126_ = l_Lean_MVarId_getType(v_mvarId_1810_, v___y_2121_, v___y_2120_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = l_Lean_LocalDecl_toExpr(v_val_1841_);
v___x_2129_ = l_Lean_Meta_mkEqOfHEq(v___x_2128_, v___x_1820_, v___y_2121_, v___y_2120_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l_Lean_Meta_mkNoConfusion(v_a_2127_, v_a_2130_, v___y_2121_, v___y_2120_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1810_, v_a_2132_, v___y_2120_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec_ref_known(v___x_2133_, 1);
v___x_2134_ = lean_box(v___x_1820_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_1845_);
v_a_1827_ = v___x_2136_;
goto v___jp_1826_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
v_a_2137_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2133_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2133_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2145_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2131_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2131_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_a_2127_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2153_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2129_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2129_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2161_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2126_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2126_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec_ref(v___x_1958_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2169_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2123_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2123_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
v___jp_2177_:
{
lean_object* v___x_2183_; 
lean_inc_ref(v___x_1958_);
v___x_2183_ = l_Lean_Meta_matchHEq_x3f(v___x_1958_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
if (lean_obj_tag(v_a_2184_) == 1)
{
lean_object* v_val_2185_; lean_object* v_snd_2186_; lean_object* v_snd_2187_; lean_object* v_fst_2188_; lean_object* v_fst_2189_; lean_object* v_fst_2190_; lean_object* v_snd_2191_; lean_object* v___x_2192_; 
v_val_2185_ = lean_ctor_get(v_a_2184_, 0);
lean_inc(v_val_2185_);
lean_dec_ref_known(v_a_2184_, 1);
v_snd_2186_ = lean_ctor_get(v_val_2185_, 1);
lean_inc(v_snd_2186_);
v_snd_2187_ = lean_ctor_get(v_snd_2186_, 1);
lean_inc(v_snd_2187_);
v_fst_2188_ = lean_ctor_get(v_val_2185_, 0);
lean_inc(v_fst_2188_);
lean_dec(v_val_2185_);
v_fst_2189_ = lean_ctor_get(v_snd_2186_, 0);
lean_inc(v_fst_2189_);
lean_dec(v_snd_2186_);
v_fst_2190_ = lean_ctor_get(v_snd_2187_, 0);
lean_inc(v_fst_2190_);
v_snd_2191_ = lean_ctor_get(v_snd_2187_, 1);
lean_inc(v_snd_2191_);
lean_dec(v_snd_2187_);
v___x_2192_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2189_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
if (lean_obj_tag(v_a_2193_) == 1)
{
lean_object* v_val_2194_; lean_object* v___x_2195_; 
v_val_2194_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_val_2194_);
lean_dec_ref_known(v_a_2193_, 1);
v___x_2195_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2191_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
if (lean_obj_tag(v_a_2196_) == 1)
{
lean_object* v_toConstantVal_2197_; lean_object* v_val_2198_; lean_object* v_toConstantVal_2199_; lean_object* v_name_2200_; lean_object* v_name_2201_; uint8_t v___x_2202_; 
v_toConstantVal_2197_ = lean_ctor_get(v_val_2194_, 0);
lean_inc_ref(v_toConstantVal_2197_);
lean_dec(v_val_2194_);
v_val_2198_ = lean_ctor_get(v_a_2196_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v_a_2196_, 1);
v_toConstantVal_2199_ = lean_ctor_get(v_val_2198_, 0);
lean_inc_ref(v_toConstantVal_2199_);
lean_dec(v_val_2198_);
v_name_2200_ = lean_ctor_get(v_toConstantVal_2197_, 0);
lean_inc(v_name_2200_);
lean_dec_ref(v_toConstantVal_2197_);
v_name_2201_ = lean_ctor_get(v_toConstantVal_2199_, 0);
lean_inc(v_name_2201_);
lean_dec_ref(v_toConstantVal_2199_);
v___x_2202_ = lean_name_eq(v_name_2200_, v_name_2201_);
lean_dec(v_name_2201_);
lean_dec(v_name_2200_);
if (v___x_2202_ == 0)
{
v___y_2116_ = v___y_2181_;
v___y_2117_ = v___y_2182_;
v___y_2118_ = v_fst_2188_;
v___y_2119_ = v_fst_2190_;
v___y_2120_ = v___y_2180_;
v___y_2121_ = v___y_2179_;
v___y_2122_ = v_isEq_2178_;
goto v___jp_2115_;
}
else
{
if (v___x_1914_ == 0)
{
lean_dec(v_fst_2190_);
lean_dec(v_fst_2188_);
v___y_2107_ = v_isEq_2178_;
v_isHEq_2108_ = v___x_1820_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
v___y_2111_ = v___y_2181_;
v___y_2112_ = v___y_2182_;
goto v___jp_2106_;
}
else
{
v___y_2116_ = v___y_2181_;
v___y_2117_ = v___y_2182_;
v___y_2118_ = v_fst_2188_;
v___y_2119_ = v_fst_2190_;
v___y_2120_ = v___y_2180_;
v___y_2121_ = v___y_2179_;
v___y_2122_ = v_isEq_2178_;
goto v___jp_2115_;
}
}
}
else
{
lean_dec(v_a_2196_);
lean_dec(v_val_2194_);
lean_dec(v_fst_2190_);
lean_dec(v_fst_2188_);
v___y_2107_ = v_isEq_2178_;
v_isHEq_2108_ = v___x_1820_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
v___y_2111_ = v___y_2181_;
v___y_2112_ = v___y_2182_;
goto v___jp_2106_;
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v_val_2194_);
lean_dec(v_fst_2190_);
lean_dec(v_fst_2188_);
lean_dec_ref(v___x_1958_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2203_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2195_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2195_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_dec(v_a_2193_);
lean_dec(v_snd_2191_);
lean_dec(v_fst_2190_);
lean_dec(v_fst_2188_);
v___y_2107_ = v_isEq_2178_;
v_isHEq_2108_ = v___x_1820_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
v___y_2111_ = v___y_2181_;
v___y_2112_ = v___y_2182_;
goto v___jp_2106_;
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_snd_2191_);
lean_dec(v_fst_2190_);
lean_dec(v_fst_2188_);
lean_dec_ref(v___x_1958_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2211_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2192_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2192_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_dec(v_a_2184_);
v___y_2107_ = v_isEq_2178_;
v_isHEq_2108_ = v___x_1914_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
v___y_2111_ = v___y_2181_;
v___y_2112_ = v___y_2182_;
goto v___jp_2106_;
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec_ref(v___x_1958_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2219_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2183_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2183_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
v___jp_2227_:
{
lean_object* v___x_2232_; 
lean_inc_ref(v___x_1958_);
v___x_2232_ = l_Lean_Meta_matchEq_x3f(v___x_1958_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
if (lean_obj_tag(v_a_2233_) == 1)
{
lean_object* v_val_2234_; lean_object* v_snd_2235_; lean_object* v_fst_2236_; lean_object* v_snd_2237_; lean_object* v___x_2238_; 
v_val_2234_ = lean_ctor_get(v_a_2233_, 0);
lean_inc(v_val_2234_);
lean_dec_ref_known(v_a_2233_, 1);
v_snd_2235_ = lean_ctor_get(v_val_2234_, 1);
lean_inc(v_snd_2235_);
lean_dec(v_val_2234_);
v_fst_2236_ = lean_ctor_get(v_snd_2235_, 0);
lean_inc(v_fst_2236_);
v_snd_2237_ = lean_ctor_get(v_snd_2235_, 1);
lean_inc(v_snd_2237_);
lean_dec(v_snd_2235_);
v___x_2238_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2236_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
if (lean_obj_tag(v_a_2239_) == 1)
{
lean_object* v_val_2240_; lean_object* v___x_2241_; 
v_val_2240_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_val_2240_);
lean_dec_ref_known(v_a_2239_, 1);
v___x_2241_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2237_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2241_, 1);
if (lean_obj_tag(v_a_2242_) == 1)
{
lean_object* v_toConstantVal_2243_; lean_object* v_val_2244_; lean_object* v_toConstantVal_2245_; lean_object* v_name_2246_; lean_object* v_name_2247_; uint8_t v___x_2248_; 
v_toConstantVal_2243_ = lean_ctor_get(v_val_2240_, 0);
lean_inc_ref(v_toConstantVal_2243_);
lean_dec(v_val_2240_);
v_val_2244_ = lean_ctor_get(v_a_2242_, 0);
lean_inc(v_val_2244_);
lean_dec_ref_known(v_a_2242_, 1);
v_toConstantVal_2245_ = lean_ctor_get(v_val_2244_, 0);
lean_inc_ref(v_toConstantVal_2245_);
lean_dec(v_val_2244_);
v_name_2246_ = lean_ctor_get(v_toConstantVal_2243_, 0);
lean_inc(v_name_2246_);
lean_dec_ref(v_toConstantVal_2243_);
v_name_2247_ = lean_ctor_get(v_toConstantVal_2245_, 0);
lean_inc(v_name_2247_);
lean_dec_ref(v_toConstantVal_2245_);
v___x_2248_ = lean_name_eq(v_name_2246_, v_name_2247_);
lean_dec(v_name_2247_);
lean_dec(v_name_2246_);
if (v___x_2248_ == 0)
{
lean_dec_ref(v___x_1958_);
lean_dec_ref(v_config_1809_);
v___y_1847_ = v___y_2231_;
v___y_1848_ = v___y_2230_;
v___y_1849_ = v___y_2229_;
v___y_1850_ = v___y_2228_;
goto v___jp_1846_;
}
else
{
if (v___x_1914_ == 0)
{
lean_del_object(v___x_1843_);
v_isEq_2178_ = v___x_1820_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
v___y_2181_ = v___y_2230_;
v___y_2182_ = v___y_2231_;
goto v___jp_2177_;
}
else
{
lean_dec_ref(v___x_1958_);
lean_dec_ref(v_config_1809_);
v___y_1847_ = v___y_2231_;
v___y_1848_ = v___y_2230_;
v___y_1849_ = v___y_2229_;
v___y_1850_ = v___y_2228_;
goto v___jp_1846_;
}
}
}
else
{
lean_dec(v_a_2242_);
lean_dec(v_val_2240_);
lean_del_object(v___x_1843_);
v_isEq_2178_ = v___x_1820_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
v___y_2181_ = v___y_2230_;
v___y_2182_ = v___y_2231_;
goto v___jp_2177_;
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_val_2240_);
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2249_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2241_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2241_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_dec(v_a_2239_);
lean_dec(v_snd_2237_);
lean_del_object(v___x_1843_);
v_isEq_2178_ = v___x_1820_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
v___y_2181_ = v___y_2230_;
v___y_2182_ = v___y_2231_;
goto v___jp_2177_;
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_snd_2237_);
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2257_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2238_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2238_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
else
{
lean_dec(v_a_2233_);
lean_del_object(v___x_1843_);
v_isEq_2178_ = v___x_1914_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
v___y_2181_ = v___y_2230_;
v___y_2182_ = v___y_2231_;
goto v___jp_2177_;
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2265_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2232_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2232_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
v___jp_2273_:
{
lean_object* v___x_2278_; 
lean_inc_ref(v___x_1958_);
v___x_2278_ = l_Lean_refutableHasNotBit_x3f(v___x_1958_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
if (lean_obj_tag(v_a_2279_) == 1)
{
lean_object* v_val_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec_ref(v_config_1809_);
v_val_2280_ = lean_ctor_get(v_a_2279_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_a_2279_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2282_ = v_a_2279_;
v_isShared_2283_ = v_isSharedCheck_2319_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_val_2280_);
lean_dec(v_a_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2319_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; 
lean_inc(v_mvarId_1810_);
v___x_2284_ = l_Lean_MVarId_getType(v_mvarId_1810_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = l_Lean_LocalDecl_toExpr(v_val_1841_);
v___x_2287_ = l_Lean_Meta_mkAbsurd(v_a_2285_, v_val_2280_, v___x_2286_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1810_, v_a_2288_, v___y_2275_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2292_; 
lean_dec_ref_known(v___x_2289_, 1);
v___x_2290_ = lean_box(v___x_1820_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2290_);
v___x_2292_ = v___x_2282_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v___x_1845_);
v_a_1827_ = v___x_2293_;
goto v___jp_1826_;
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_del_object(v___x_2282_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
v_a_2295_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2289_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2289_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_del_object(v___x_2282_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2303_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2287_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2287_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2311_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2284_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2284_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
else
{
lean_object* v___x_2320_; 
lean_dec(v_a_2279_);
lean_inc_ref(v___x_1958_);
v___x_2320_ = l_Lean_Meta_matchNe_x3f(v___x_1958_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
if (lean_obj_tag(v_a_2321_) == 1)
{
lean_object* v_val_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2391_; 
v_val_2322_ = lean_ctor_get(v_a_2321_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_a_2321_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2324_ = v_a_2321_;
v_isShared_2325_ = v_isSharedCheck_2391_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_val_2322_);
lean_dec(v_a_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2391_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v_snd_2326_; lean_object* v_fst_2327_; lean_object* v_snd_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2390_; 
v_snd_2326_ = lean_ctor_get(v_val_2322_, 1);
lean_inc(v_snd_2326_);
lean_dec(v_val_2322_);
v_fst_2327_ = lean_ctor_get(v_snd_2326_, 0);
v_snd_2328_ = lean_ctor_get(v_snd_2326_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_snd_2326_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2330_ = v_snd_2326_;
v_isShared_2331_ = v_isSharedCheck_2390_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_snd_2328_);
lean_inc(v_fst_2327_);
lean_dec(v_snd_2326_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2390_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; 
lean_inc(v_fst_2327_);
v___x_2332_ = l_Lean_Meta_isExprDefEq(v_fst_2327_, v_snd_2328_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint8_t v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = lean_unbox(v_a_2333_);
lean_dec(v_a_2333_);
if (v___x_2334_ == 0)
{
lean_del_object(v___x_2330_);
lean_dec(v_fst_2327_);
lean_del_object(v___x_2324_);
v___y_2228_ = v___y_2274_;
v___y_2229_ = v___y_2275_;
v___y_2230_ = v___y_2276_;
v___y_2231_ = v___y_2277_;
goto v___jp_2227_;
}
else
{
lean_object* v___x_2335_; 
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec_ref(v_config_1809_);
lean_inc(v_mvarId_1810_);
v___x_2335_ = l_Lean_MVarId_getType(v_mvarId_1810_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = l_Lean_Meta_mkEqRefl(v_fst_2327_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_LocalDecl_toExpr(v_val_1841_);
v___x_2340_ = l_Lean_Meta_mkAbsurd(v_a_2336_, v_a_2338_, v___x_2339_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1810_, v_a_2341_, v___y_2275_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2345_; 
lean_dec_ref_known(v___x_2342_, 1);
v___x_2343_ = lean_box(v___x_1820_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2343_);
v___x_2345_ = v___x_2324_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 1, v___x_1845_);
lean_ctor_set(v___x_2330_, 0, v___x_2345_);
v___x_2347_ = v___x_2330_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v___x_1845_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
v_a_1827_ = v___x_2347_;
goto v___jp_1826_;
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_del_object(v___x_2330_);
lean_del_object(v___x_2324_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
v_a_2350_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2342_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2342_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_del_object(v___x_2330_);
lean_del_object(v___x_2324_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2358_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2340_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2340_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2336_);
lean_del_object(v___x_2330_);
lean_del_object(v___x_2324_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2366_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2337_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2337_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_del_object(v___x_2330_);
lean_dec(v_fst_2327_);
lean_del_object(v___x_2324_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_2374_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2335_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2335_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_del_object(v___x_2330_);
lean_dec(v_fst_2327_);
lean_del_object(v___x_2324_);
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2382_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2332_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2332_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2321_);
v___y_2228_ = v___y_2274_;
v___y_2229_ = v___y_2275_;
v___y_2230_ = v___y_2276_;
v___y_2231_ = v___y_2277_;
goto v___jp_2227_;
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2392_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2320_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2320_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec_ref(v___x_1958_);
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_2400_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2278_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2278_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
else
{
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
v_a_1835_ = v___x_1886_;
goto v___jp_1834_;
}
v___jp_1846_:
{
lean_object* v___x_1851_; 
lean_inc(v_mvarId_1810_);
v___x_1851_ = l_Lean_MVarId_getType(v_mvarId_1810_, v___y_1850_, v___y_1849_, v___y_1848_, v___y_1847_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___x_1851_, 1);
v___x_1853_ = l_Lean_LocalDecl_toExpr(v_val_1841_);
v___x_1854_ = l_Lean_Meta_mkNoConfusion(v_a_1852_, v___x_1853_, v___y_1850_, v___y_1849_, v___y_1848_, v___y_1847_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___x_1856_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1810_, v_a_1855_, v___y_1849_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
lean_dec_ref_known(v___x_1856_, 1);
v___x_1857_ = lean_box(v___x_1820_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1857_);
v___x_1859_ = v___x_1843_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v___x_1845_);
v_a_1827_ = v___x_1860_;
goto v___jp_1826_;
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_del_object(v___x_1843_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
v_a_1862_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1856_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1856_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_del_object(v___x_1843_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_1870_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1854_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1854_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_del_object(v___x_1843_);
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
v_a_1878_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1851_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1851_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
v___jp_1887_:
{
lean_object* v_searchFuel_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_searchFuel_1892_ = lean_ctor_get(v_config_1809_, 0);
v___x_1893_ = l_Lean_LocalDecl_fvarId(v_val_1841_);
lean_dec(v_val_1841_);
lean_inc(v_searchFuel_1892_);
lean_inc(v_mvarId_1810_);
v___x_1894_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1810_, v___x_1893_, v_searchFuel_1892_, v___y_1890_, v___y_1888_, v___y_1891_, v___y_1889_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; uint8_t v___x_1896_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = lean_unbox(v_a_1895_);
lean_dec(v_a_1895_);
if (v___x_1896_ == 0)
{
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
v_a_1835_ = v___x_1886_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v___x_1897_ = lean_box(v___x_1820_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v___x_1845_);
v_a_1827_ = v___x_1899_;
goto v___jp_1826_;
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_1900_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1894_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1894_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
v___jp_1908_:
{
if (v___y_1913_ == 0)
{
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
v_a_1835_ = v___x_1886_;
goto v___jp_1834_;
}
else
{
v___y_1888_ = v___y_1909_;
v___y_1889_ = v___y_1910_;
v___y_1890_ = v___y_1911_;
v___y_1891_ = v___y_1912_;
goto v___jp_1887_;
}
}
v___jp_1915_:
{
if (v___y_1917_ == 0)
{
v___y_1888_ = v___y_1916_;
v___y_1889_ = v___y_1918_;
v___y_1890_ = v___y_1919_;
v___y_1891_ = v___y_1920_;
goto v___jp_1887_;
}
else
{
v___y_1909_ = v___y_1916_;
v___y_1910_ = v___y_1918_;
v___y_1911_ = v___y_1919_;
v___y_1912_ = v___y_1920_;
v___y_1913_ = v___x_1914_;
goto v___jp_1908_;
}
}
v___jp_1921_:
{
if (v___y_1927_ == 0)
{
v___y_1909_ = v___y_1922_;
v___y_1910_ = v___y_1924_;
v___y_1911_ = v___y_1925_;
v___y_1912_ = v___y_1926_;
v___y_1913_ = v___x_1914_;
goto v___jp_1908_;
}
else
{
v___y_1916_ = v___y_1922_;
v___y_1917_ = v___y_1923_;
v___y_1918_ = v___y_1924_;
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1926_;
goto v___jp_1915_;
}
}
v___jp_1928_:
{
uint8_t v_emptyType_1935_; 
v_emptyType_1935_ = lean_ctor_get_uint8(v_config_1809_, sizeof(void*)*1 + 1);
if (v_emptyType_1935_ == 0)
{
v___y_1922_ = v___y_1932_;
v___y_1923_ = v___y_1929_;
v___y_1924_ = v___y_1934_;
v___y_1925_ = v___y_1931_;
v___y_1926_ = v___y_1933_;
v___y_1927_ = v___x_1914_;
goto v___jp_1921_;
}
else
{
if (v___y_1930_ == 0)
{
v___y_1916_ = v___y_1932_;
v___y_1917_ = v___y_1929_;
v___y_1918_ = v___y_1934_;
v___y_1919_ = v___y_1931_;
v___y_1920_ = v___y_1933_;
goto v___jp_1915_;
}
else
{
v___y_1922_ = v___y_1932_;
v___y_1923_ = v___y_1929_;
v___y_1924_ = v___y_1934_;
v___y_1925_ = v___y_1931_;
v___y_1926_ = v___y_1933_;
v___y_1927_ = v___x_1914_;
goto v___jp_1921_;
}
}
}
v___jp_1936_:
{
if (v___y_1943_ == 0)
{
v___y_1929_ = v___y_1937_;
v___y_1930_ = v___y_1940_;
v___y_1931_ = v___y_1938_;
v___y_1932_ = v___y_1939_;
v___y_1933_ = v___y_1942_;
v___y_1934_ = v___y_1941_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1944_; 
lean_inc(v_val_1841_);
lean_inc(v_mvarId_1810_);
v___x_1944_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1810_, v_val_1841_, v___y_1938_, v___y_1939_, v___y_1942_, v___y_1941_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; uint8_t v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v___x_1946_ = lean_unbox(v_a_1945_);
lean_dec(v_a_1945_);
if (v___x_1946_ == 0)
{
v___y_1929_ = v___y_1937_;
v___y_1930_ = v___y_1940_;
v___y_1931_ = v___y_1938_;
v___y_1932_ = v___y_1939_;
v___y_1933_ = v___y_1942_;
v___y_1934_ = v___y_1941_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_val_1841_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v___x_1947_ = lean_box(v___x_1820_);
v___x_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v___x_1845_);
v_a_1827_ = v___x_1949_;
goto v___jp_1826_;
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_val_1841_);
lean_del_object(v___x_1824_);
lean_dec(v_snd_1822_);
lean_dec(v_mvarId_1810_);
lean_dec_ref(v_config_1809_);
v_a_1950_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1944_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1944_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
}
v___jp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_a_1827_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1828_);
v___x_1830_ = v___x_1824_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_snd_1822_);
v___x_1830_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
v___jp_1834_:
{
lean_object* v___x_1836_; size_t v___x_1837_; size_t v___x_1838_; 
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1833_);
lean_ctor_set(v___x_1836_, 1, v_a_1835_);
v___x_1837_ = ((size_t)1ULL);
v___x_1838_ = lean_usize_add(v_i_1813_, v___x_1837_);
v_i_1813_ = v___x_1838_;
v_b_1814_ = v___x_1836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2474_, lean_object* v_mvarId_2475_, lean_object* v_as_2476_, lean_object* v_sz_2477_, lean_object* v_i_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
size_t v_sz_boxed_2485_; size_t v_i_boxed_2486_; lean_object* v_res_2487_; 
v_sz_boxed_2485_ = lean_unbox_usize(v_sz_2477_);
lean_dec(v_sz_2477_);
v_i_boxed_2486_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_res_2487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2474_, v_mvarId_2475_, v_as_2476_, v_sz_boxed_2485_, v_i_boxed_2486_, v_b_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v_as_2476_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2488_, lean_object* v_mvarId_2489_, lean_object* v_as_2490_, size_t v_sz_2491_, size_t v_i_2492_, lean_object* v_b_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
uint8_t v___x_2499_; 
v___x_2499_ = lean_usize_dec_lt(v_i_2492_, v_sz_2491_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_b_2493_);
return v___x_2500_;
}
else
{
lean_object* v_snd_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_3151_; 
v_snd_2501_ = lean_ctor_get(v_b_2493_, 1);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_b_2493_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_b_2493_, 0);
lean_dec(v_unused_3152_);
v___x_2503_ = v_b_2493_;
v_isShared_2504_ = v_isSharedCheck_3151_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_snd_2501_);
lean_dec(v_b_2493_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_3151_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v_a_2506_; lean_object* v___x_2512_; lean_object* v_a_2514_; lean_object* v_a_2519_; 
v___x_2512_ = lean_box(0);
v_a_2519_ = lean_array_uget(v_as_2490_, v_i_2492_);
if (lean_obj_tag(v_a_2519_) == 0)
{
lean_del_object(v___x_2503_);
v_a_2514_ = v_snd_2501_;
goto v___jp_2513_;
}
else
{
lean_object* v_val_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_3150_; 
v_val_2520_ = lean_ctor_get(v_a_2519_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_a_2519_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_2522_ = v_a_2519_;
v_isShared_2523_ = v_isSharedCheck_3150_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_val_2520_);
lean_dec(v_a_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_3150_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___x_2565_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; uint8_t v___y_2592_; uint8_t v___x_2593_; lean_object* v___y_2595_; lean_object* v___y_2596_; uint8_t v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2601_; lean_object* v___y_2602_; uint8_t v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; uint8_t v___y_2606_; uint8_t v___y_2608_; uint8_t v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; uint8_t v___y_2616_; uint8_t v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; uint8_t v___y_2622_; 
v___x_2524_ = lean_box(0);
v___x_2565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2593_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2520_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2637_; uint8_t v___y_2639_; uint8_t v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2648_; uint8_t v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; uint8_t v___y_2655_; uint8_t v___y_2658_; uint8_t v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v_a_2664_; uint8_t v___y_2668_; uint8_t v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; uint8_t v___y_2712_; uint8_t v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; uint8_t v___y_2741_; uint8_t v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; uint8_t v___y_2747_; lean_object* v___y_2749_; uint8_t v___y_2750_; uint8_t v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; uint8_t v___y_2756_; uint8_t v___y_2759_; uint8_t v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; uint8_t v___y_2765_; uint8_t v___y_2778_; uint8_t v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; uint8_t v___y_2786_; uint8_t v_isHEq_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; uint8_t v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; uint8_t v_isEq_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___x_3087_; 
v___x_2637_ = l_Lean_LocalDecl_type(v_val_2520_);
lean_inc_ref(v___x_2637_);
v___x_3087_ = l_Lean_Meta_matchNot_x3f(v___x_2637_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
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
v___x_3090_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3089_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3090_, 1);
if (lean_obj_tag(v_a_3091_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec_ref(v_config_2488_);
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
lean_inc(v_mvarId_2489_);
v___x_3096_ = l_Lean_MVarId_getType(v_mvarId_2489_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3098_ = l_Lean_LocalDecl_toExpr(v_val_2520_);
v___x_3099_ = l_Lean_mkFVar(v_val_3092_);
v___x_3100_ = l_Lean_Expr_app___override(v___x_3098_, v___x_3099_);
v___x_3101_ = l_Lean_Meta_mkFalseElim(v_a_3097_, v___x_3100_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v___x_3103_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2489_, v_a_3102_, v___y_2495_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_dec_ref_known(v___x_3103_, 1);
v___x_3104_ = lean_box(v___x_2499_);
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
lean_ctor_set(v___x_3107_, 1, v___x_2524_);
v_a_2506_ = v___x_3107_;
goto v___jp_2505_;
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_del_object(v___x_3094_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
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
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
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
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
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
v___y_2953_ = v___y_2494_;
v___y_2954_ = v___y_2495_;
v___y_2955_ = v___y_2496_;
v___y_2956_ = v___y_2497_;
goto v___jp_2952_;
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
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
v___y_2953_ = v___y_2494_;
v___y_2954_ = v___y_2495_;
v___y_2955_ = v___y_2496_;
v___y_2956_ = v___y_2497_;
goto v___jp_2952_;
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
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
v___jp_2638_:
{
uint8_t v_genDiseq_2645_; 
v_genDiseq_2645_ = lean_ctor_get_uint8(v_config_2488_, sizeof(void*)*1 + 2);
if (v_genDiseq_2645_ == 0)
{
lean_dec_ref(v___x_2637_);
v___y_2616_ = v___y_2639_;
v___y_2617_ = v___y_2640_;
v___y_2618_ = v___y_2644_;
v___y_2619_ = v___y_2641_;
v___y_2620_ = v___y_2642_;
v___y_2621_ = v___y_2643_;
v___y_2622_ = v___x_2593_;
goto v___jp_2615_;
}
else
{
uint8_t v___x_2646_; 
v___x_2646_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2637_);
v___y_2616_ = v___y_2639_;
v___y_2617_ = v___y_2640_;
v___y_2618_ = v___y_2644_;
v___y_2619_ = v___y_2641_;
v___y_2620_ = v___y_2642_;
v___y_2621_ = v___y_2643_;
v___y_2622_ = v___x_2646_;
goto v___jp_2615_;
}
}
v___jp_2647_:
{
if (v___y_2655_ == 0)
{
lean_dec_ref(v___y_2648_);
v___y_2639_ = v___y_2649_;
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2652_;
v___y_2642_ = v___y_2651_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2654_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2656_; 
lean_dec_ref(v___x_2637_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___y_2648_);
return v___x_2656_;
}
}
v___jp_2657_:
{
uint8_t v___x_2665_; 
v___x_2665_ = l_Lean_Exception_isInterrupt(v_a_2664_);
if (v___x_2665_ == 0)
{
uint8_t v___x_2666_; 
lean_inc_ref(v_a_2664_);
v___x_2666_ = l_Lean_Exception_isRuntime(v_a_2664_);
v___y_2648_ = v_a_2664_;
v___y_2649_ = v___y_2658_;
v___y_2650_ = v___y_2659_;
v___y_2651_ = v___y_2661_;
v___y_2652_ = v___y_2660_;
v___y_2653_ = v___y_2662_;
v___y_2654_ = v___y_2663_;
v___y_2655_ = v___x_2666_;
goto v___jp_2647_;
}
else
{
v___y_2648_ = v_a_2664_;
v___y_2649_ = v___y_2658_;
v___y_2650_ = v___y_2659_;
v___y_2651_ = v___y_2661_;
v___y_2652_ = v___y_2660_;
v___y_2653_ = v___y_2662_;
v___y_2654_ = v___y_2663_;
v___y_2655_ = v___x_2665_;
goto v___jp_2647_;
}
}
v___jp_2667_:
{
if (lean_obj_tag(v___y_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_a_2676_ = lean_ctor_get(v___y_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___y_2675_, 1);
v___x_2677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2678_ = l_Lean_Expr_isConstOf(v_a_2676_, v___x_2677_);
lean_dec(v_a_2676_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v___y_2672_);
v___y_2639_ = v___y_2668_;
v___y_2640_ = v___y_2669_;
v___y_2641_ = v___y_2671_;
v___y_2642_ = v___y_2670_;
v___y_2643_ = v___y_2673_;
v___y_2644_ = v___y_2674_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2679_; 
lean_inc_ref(v___y_2672_);
v___x_2679_ = l_Lean_Meta_mkEqRefl(v___y_2672_, v___y_2671_, v___y_2670_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; lean_object* v_dummy_2682_; lean_object* v_nargs_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2682_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2683_ = l_Lean_Expr_getAppNumArgs(v___y_2672_);
lean_inc(v_nargs_2683_);
v___x_2684_ = lean_mk_array(v_nargs_2683_, v_dummy_2682_);
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_sub(v_nargs_2683_, v___x_2685_);
lean_dec(v_nargs_2683_);
v___x_2687_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2672_, v___x_2684_, v___x_2686_);
v___x_2688_ = lean_array_push(v___x_2687_, v_a_2680_);
v___x_2689_ = l_Lean_mkAppN(v___x_2681_, v___x_2688_);
lean_dec_ref(v___x_2688_);
lean_inc(v_mvarId_2489_);
v___x_2690_ = l_Lean_MVarId_getType(v_mvarId_2489_, v___y_2671_, v___y_2670_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
lean_inc(v_val_2520_);
v___x_2692_ = l_Lean_LocalDecl_toExpr(v_val_2520_);
v___x_2693_ = l_Lean_Meta_mkAbsurd(v_a_2691_, v___x_2692_, v___x_2689_, v___y_2671_, v___y_2670_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
lean_inc(v_mvarId_2489_);
v___x_2695_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2489_, v_a_2694_, v___y_2670_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v___x_2637_);
lean_dec(v_val_2520_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v___x_2695_, 0);
lean_dec(v_unused_2705_);
v___x_2697_ = v___x_2695_;
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
else
{
lean_dec(v___x_2695_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2699_ = lean_box(v___x_2499_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 1);
lean_ctor_set(v___x_2697_, 0, v___x_2699_);
v___x_2701_ = v___x_2697_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v___x_2524_);
v_a_2506_ = v___x_2702_;
goto v___jp_2505_;
}
}
}
else
{
lean_object* v_a_2706_; 
v_a_2706_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2695_, 1);
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2669_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2670_;
v___y_2662_ = v___y_2673_;
v___y_2663_ = v___y_2674_;
v_a_2664_ = v_a_2706_;
goto v___jp_2657_;
}
}
else
{
lean_object* v_a_2707_; 
v_a_2707_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2693_, 1);
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2669_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2670_;
v___y_2662_ = v___y_2673_;
v___y_2663_ = v___y_2674_;
v_a_2664_ = v_a_2707_;
goto v___jp_2657_;
}
}
else
{
lean_object* v_a_2708_; 
lean_dec_ref(v___x_2689_);
v_a_2708_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2690_, 1);
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2669_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2670_;
v___y_2662_ = v___y_2673_;
v___y_2663_ = v___y_2674_;
v_a_2664_ = v_a_2708_;
goto v___jp_2657_;
}
}
else
{
lean_object* v_a_2709_; 
lean_dec_ref(v___y_2672_);
v_a_2709_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2679_, 1);
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2669_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2670_;
v___y_2662_ = v___y_2673_;
v___y_2663_ = v___y_2674_;
v_a_2664_ = v_a_2709_;
goto v___jp_2657_;
}
}
}
else
{
lean_object* v_a_2710_; 
lean_dec_ref(v___y_2672_);
v_a_2710_ = lean_ctor_get(v___y_2675_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___y_2675_, 1);
v___y_2658_ = v___y_2668_;
v___y_2659_ = v___y_2669_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2670_;
v___y_2662_ = v___y_2673_;
v___y_2663_ = v___y_2674_;
v_a_2664_ = v_a_2710_;
goto v___jp_2657_;
}
}
v___jp_2711_:
{
lean_object* v___x_2718_; 
lean_inc_ref(v___x_2637_);
v___x_2718_ = l_Lean_Meta_mkDecide(v___x_2637_, v___y_2715_, v___y_2714_, v___y_2716_, v___y_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2720_; uint8_t v_transparency_2721_; uint8_t v___x_2722_; uint8_t v___x_2723_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2718_, 1);
v___x_2720_ = l_Lean_Meta_Context_config(v___y_2715_);
v_transparency_2721_ = lean_ctor_get_uint8(v___x_2720_, 9);
lean_dec_ref(v___x_2720_);
v___x_2722_ = 1;
v___x_2723_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2721_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v_keyedConfig_2724_; uint8_t v_trackZetaDelta_2725_; lean_object* v_zetaDeltaSet_2726_; lean_object* v_lctx_2727_; lean_object* v_localInstances_2728_; lean_object* v_defEqCtx_x3f_2729_; lean_object* v_synthPendingDepth_2730_; lean_object* v_customCanUnfoldPredicate_x3f_2731_; uint8_t v_univApprox_2732_; uint8_t v_inTypeClassResolution_2733_; uint8_t v_cacheInferType_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_keyedConfig_2724_ = lean_ctor_get(v___y_2715_, 0);
v_trackZetaDelta_2725_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*7);
v_zetaDeltaSet_2726_ = lean_ctor_get(v___y_2715_, 1);
v_lctx_2727_ = lean_ctor_get(v___y_2715_, 2);
v_localInstances_2728_ = lean_ctor_get(v___y_2715_, 3);
v_defEqCtx_x3f_2729_ = lean_ctor_get(v___y_2715_, 4);
v_synthPendingDepth_2730_ = lean_ctor_get(v___y_2715_, 5);
v_customCanUnfoldPredicate_x3f_2731_ = lean_ctor_get(v___y_2715_, 6);
v_univApprox_2732_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2733_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*7 + 2);
v_cacheInferType_2734_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2724_);
v___x_2735_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2722_, v_keyedConfig_2724_);
lean_inc(v_customCanUnfoldPredicate_x3f_2731_);
lean_inc(v_synthPendingDepth_2730_);
lean_inc(v_defEqCtx_x3f_2729_);
lean_inc_ref(v_localInstances_2728_);
lean_inc_ref(v_lctx_2727_);
lean_inc(v_zetaDeltaSet_2726_);
v___x_2736_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
lean_ctor_set(v___x_2736_, 1, v_zetaDeltaSet_2726_);
lean_ctor_set(v___x_2736_, 2, v_lctx_2727_);
lean_ctor_set(v___x_2736_, 3, v_localInstances_2728_);
lean_ctor_set(v___x_2736_, 4, v_defEqCtx_x3f_2729_);
lean_ctor_set(v___x_2736_, 5, v_synthPendingDepth_2730_);
lean_ctor_set(v___x_2736_, 6, v_customCanUnfoldPredicate_x3f_2731_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*7, v_trackZetaDelta_2725_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*7 + 1, v_univApprox_2732_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2733_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*7 + 3, v_cacheInferType_2734_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2714_);
lean_inc(v_a_2719_);
v___x_2737_ = lean_whnf(v_a_2719_, v___x_2736_, v___y_2714_, v___y_2716_, v___y_2717_);
v___y_2668_ = v___y_2712_;
v___y_2669_ = v___y_2713_;
v___y_2670_ = v___y_2714_;
v___y_2671_ = v___y_2715_;
v___y_2672_ = v_a_2719_;
v___y_2673_ = v___y_2716_;
v___y_2674_ = v___y_2717_;
v___y_2675_ = v___x_2737_;
goto v___jp_2667_;
}
else
{
lean_object* v___x_2738_; 
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2715_);
lean_inc(v_a_2719_);
v___x_2738_ = lean_whnf(v_a_2719_, v___y_2715_, v___y_2714_, v___y_2716_, v___y_2717_);
v___y_2668_ = v___y_2712_;
v___y_2669_ = v___y_2713_;
v___y_2670_ = v___y_2714_;
v___y_2671_ = v___y_2715_;
v___y_2672_ = v_a_2719_;
v___y_2673_ = v___y_2716_;
v___y_2674_ = v___y_2717_;
v___y_2675_ = v___x_2738_;
goto v___jp_2667_;
}
}
else
{
lean_object* v_a_2739_; 
v_a_2739_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2718_, 1);
v___y_2658_ = v___y_2712_;
v___y_2659_ = v___y_2713_;
v___y_2660_ = v___y_2715_;
v___y_2661_ = v___y_2714_;
v___y_2662_ = v___y_2716_;
v___y_2663_ = v___y_2717_;
v_a_2664_ = v_a_2739_;
goto v___jp_2657_;
}
}
v___jp_2740_:
{
if (v___y_2747_ == 0)
{
v___y_2639_ = v___y_2741_;
v___y_2640_ = v___y_2742_;
v___y_2641_ = v___y_2744_;
v___y_2642_ = v___y_2743_;
v___y_2643_ = v___y_2745_;
v___y_2644_ = v___y_2746_;
goto v___jp_2638_;
}
else
{
v___y_2712_ = v___y_2741_;
v___y_2713_ = v___y_2742_;
v___y_2714_ = v___y_2743_;
v___y_2715_ = v___y_2744_;
v___y_2716_ = v___y_2745_;
v___y_2717_ = v___y_2746_;
goto v___jp_2711_;
}
}
v___jp_2748_:
{
if (v___y_2756_ == 0)
{
lean_dec_ref(v___y_2749_);
v___y_2741_ = v___y_2750_;
v___y_2742_ = v___y_2751_;
v___y_2743_ = v___y_2753_;
v___y_2744_ = v___y_2752_;
v___y_2745_ = v___y_2754_;
v___y_2746_ = v___y_2755_;
v___y_2747_ = v___x_2593_;
goto v___jp_2740_;
}
else
{
uint8_t v___x_2757_; 
v___x_2757_ = l_Lean_Expr_hasFVar(v___y_2749_);
lean_dec_ref(v___y_2749_);
if (v___x_2757_ == 0)
{
v___y_2712_ = v___y_2750_;
v___y_2713_ = v___y_2751_;
v___y_2714_ = v___y_2753_;
v___y_2715_ = v___y_2752_;
v___y_2716_ = v___y_2754_;
v___y_2717_ = v___y_2755_;
goto v___jp_2711_;
}
else
{
v___y_2741_ = v___y_2750_;
v___y_2742_ = v___y_2751_;
v___y_2743_ = v___y_2753_;
v___y_2744_ = v___y_2752_;
v___y_2745_ = v___y_2754_;
v___y_2746_ = v___y_2755_;
v___y_2747_ = v___x_2593_;
goto v___jp_2740_;
}
}
}
v___jp_2758_:
{
lean_object* v___x_2766_; 
lean_inc_ref(v___x_2637_);
v___x_2766_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2637_, v___y_2762_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; uint8_t v___x_2768_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v___x_2768_ = l_Lean_Expr_hasMVar(v_a_2767_);
if (v___x_2768_ == 0)
{
v___y_2749_ = v_a_2767_;
v___y_2750_ = v___y_2759_;
v___y_2751_ = v___y_2760_;
v___y_2752_ = v___y_2761_;
v___y_2753_ = v___y_2762_;
v___y_2754_ = v___y_2763_;
v___y_2755_ = v___y_2764_;
v___y_2756_ = v___y_2765_;
goto v___jp_2748_;
}
else
{
v___y_2749_ = v_a_2767_;
v___y_2750_ = v___y_2759_;
v___y_2751_ = v___y_2760_;
v___y_2752_ = v___y_2761_;
v___y_2753_ = v___y_2762_;
v___y_2754_ = v___y_2763_;
v___y_2755_ = v___y_2764_;
v___y_2756_ = v___x_2593_;
goto v___jp_2748_;
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v___x_2637_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2769_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2766_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2766_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
v___jp_2777_:
{
if (v___y_2784_ == 0)
{
v___y_2639_ = v___y_2778_;
v___y_2640_ = v___y_2779_;
v___y_2641_ = v___y_2781_;
v___y_2642_ = v___y_2780_;
v___y_2643_ = v___y_2782_;
v___y_2644_ = v___y_2783_;
goto v___jp_2638_;
}
else
{
v___y_2759_ = v___y_2778_;
v___y_2760_ = v___y_2779_;
v___y_2761_ = v___y_2781_;
v___y_2762_ = v___y_2780_;
v___y_2763_ = v___y_2782_;
v___y_2764_ = v___y_2783_;
v___y_2765_ = v___y_2784_;
goto v___jp_2758_;
}
}
v___jp_2785_:
{
uint8_t v_useDecide_2792_; 
v_useDecide_2792_ = lean_ctor_get_uint8(v_config_2488_, sizeof(void*)*1);
if (v_useDecide_2792_ == 0)
{
v___y_2778_ = v_isHEq_2787_;
v___y_2779_ = v___y_2786_;
v___y_2780_ = v___y_2789_;
v___y_2781_ = v___y_2788_;
v___y_2782_ = v___y_2790_;
v___y_2783_ = v___y_2791_;
v___y_2784_ = v___x_2593_;
goto v___jp_2777_;
}
else
{
uint8_t v___x_2793_; 
v___x_2793_ = l_Lean_Expr_hasFVar(v___x_2637_);
if (v___x_2793_ == 0)
{
v___y_2759_ = v_isHEq_2787_;
v___y_2760_ = v___y_2786_;
v___y_2761_ = v___y_2788_;
v___y_2762_ = v___y_2789_;
v___y_2763_ = v___y_2790_;
v___y_2764_ = v___y_2791_;
v___y_2765_ = v_useDecide_2792_;
goto v___jp_2758_;
}
else
{
v___y_2778_ = v_isHEq_2787_;
v___y_2779_ = v___y_2786_;
v___y_2780_ = v___y_2789_;
v___y_2781_ = v___y_2788_;
v___y_2782_ = v___y_2790_;
v___y_2783_ = v___y_2791_;
v___y_2784_ = v___x_2593_;
goto v___jp_2777_;
}
}
}
v___jp_2794_:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_Meta_isExprDefEq(v___y_2799_, v___y_2801_, v___y_2795_, v___y_2800_, v___y_2797_, v___y_2796_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; uint8_t v___x_2804_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = lean_unbox(v_a_2803_);
lean_dec(v_a_2803_);
if (v___x_2804_ == 0)
{
v___y_2786_ = v___y_2798_;
v_isHEq_2787_ = v___x_2499_;
v___y_2788_ = v___y_2795_;
v___y_2789_ = v___y_2800_;
v___y_2790_ = v___y_2797_;
v___y_2791_ = v___y_2796_;
goto v___jp_2785_;
}
else
{
lean_object* v___x_2805_; 
lean_dec_ref(v___x_2637_);
lean_dec_ref(v_config_2488_);
lean_inc(v_mvarId_2489_);
v___x_2805_ = l_Lean_MVarId_getType(v_mvarId_2489_, v___y_2795_, v___y_2800_, v___y_2797_, v___y_2796_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = l_Lean_LocalDecl_toExpr(v_val_2520_);
v___x_2808_ = l_Lean_Meta_mkEqOfHEq(v___x_2807_, v___x_2499_, v___y_2795_, v___y_2800_, v___y_2797_, v___y_2796_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = l_Lean_Meta_mkNoConfusion(v_a_2806_, v_a_2809_, v___y_2795_, v___y_2800_, v___y_2797_, v___y_2796_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___x_2812_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2489_, v_a_2811_, v___y_2800_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec_ref_known(v___x_2812_, 1);
v___x_2813_ = lean_box(v___x_2499_);
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v___x_2524_);
v_a_2506_ = v___x_2815_;
goto v___jp_2505_;
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
v_a_2816_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2812_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2812_);
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
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
v_a_2824_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2810_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2810_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2806_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
v_a_2832_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2808_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2808_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
v_a_2840_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2805_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2805_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v___x_2637_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2848_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2802_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2802_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
v___jp_2856_:
{
lean_object* v___x_2862_; 
lean_inc_ref(v___x_2637_);
v___x_2862_ = l_Lean_Meta_matchHEq_x3f(v___x_2637_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
if (lean_obj_tag(v_a_2863_) == 1)
{
lean_object* v_val_2864_; lean_object* v_snd_2865_; lean_object* v_snd_2866_; lean_object* v_fst_2867_; lean_object* v_fst_2868_; lean_object* v_fst_2869_; lean_object* v_snd_2870_; lean_object* v___x_2871_; 
v_val_2864_ = lean_ctor_get(v_a_2863_, 0);
lean_inc(v_val_2864_);
lean_dec_ref_known(v_a_2863_, 1);
v_snd_2865_ = lean_ctor_get(v_val_2864_, 1);
lean_inc(v_snd_2865_);
v_snd_2866_ = lean_ctor_get(v_snd_2865_, 1);
lean_inc(v_snd_2866_);
v_fst_2867_ = lean_ctor_get(v_val_2864_, 0);
lean_inc(v_fst_2867_);
lean_dec(v_val_2864_);
v_fst_2868_ = lean_ctor_get(v_snd_2865_, 0);
lean_inc(v_fst_2868_);
lean_dec(v_snd_2865_);
v_fst_2869_ = lean_ctor_get(v_snd_2866_, 0);
lean_inc(v_fst_2869_);
v_snd_2870_ = lean_ctor_get(v_snd_2866_, 1);
lean_inc(v_snd_2870_);
lean_dec(v_snd_2866_);
v___x_2871_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2868_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
if (lean_obj_tag(v_a_2872_) == 1)
{
lean_object* v_val_2873_; lean_object* v___x_2874_; 
v_val_2873_ = lean_ctor_get(v_a_2872_, 0);
lean_inc(v_val_2873_);
lean_dec_ref_known(v_a_2872_, 1);
v___x_2874_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2870_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
if (lean_obj_tag(v_a_2875_) == 1)
{
lean_object* v_toConstantVal_2876_; lean_object* v_val_2877_; lean_object* v_toConstantVal_2878_; lean_object* v_name_2879_; lean_object* v_name_2880_; uint8_t v___x_2881_; 
v_toConstantVal_2876_ = lean_ctor_get(v_val_2873_, 0);
lean_inc_ref(v_toConstantVal_2876_);
lean_dec(v_val_2873_);
v_val_2877_ = lean_ctor_get(v_a_2875_, 0);
lean_inc(v_val_2877_);
lean_dec_ref_known(v_a_2875_, 1);
v_toConstantVal_2878_ = lean_ctor_get(v_val_2877_, 0);
lean_inc_ref(v_toConstantVal_2878_);
lean_dec(v_val_2877_);
v_name_2879_ = lean_ctor_get(v_toConstantVal_2876_, 0);
lean_inc(v_name_2879_);
lean_dec_ref(v_toConstantVal_2876_);
v_name_2880_ = lean_ctor_get(v_toConstantVal_2878_, 0);
lean_inc(v_name_2880_);
lean_dec_ref(v_toConstantVal_2878_);
v___x_2881_ = lean_name_eq(v_name_2879_, v_name_2880_);
lean_dec(v_name_2880_);
lean_dec(v_name_2879_);
if (v___x_2881_ == 0)
{
v___y_2795_ = v___y_2858_;
v___y_2796_ = v___y_2861_;
v___y_2797_ = v___y_2860_;
v___y_2798_ = v_isEq_2857_;
v___y_2799_ = v_fst_2867_;
v___y_2800_ = v___y_2859_;
v___y_2801_ = v_fst_2869_;
goto v___jp_2794_;
}
else
{
if (v___x_2593_ == 0)
{
lean_dec(v_fst_2869_);
lean_dec(v_fst_2867_);
v___y_2786_ = v_isEq_2857_;
v_isHEq_2787_ = v___x_2499_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
v___y_2790_ = v___y_2860_;
v___y_2791_ = v___y_2861_;
goto v___jp_2785_;
}
else
{
v___y_2795_ = v___y_2858_;
v___y_2796_ = v___y_2861_;
v___y_2797_ = v___y_2860_;
v___y_2798_ = v_isEq_2857_;
v___y_2799_ = v_fst_2867_;
v___y_2800_ = v___y_2859_;
v___y_2801_ = v_fst_2869_;
goto v___jp_2794_;
}
}
}
else
{
lean_dec(v_a_2875_);
lean_dec(v_val_2873_);
lean_dec(v_fst_2869_);
lean_dec(v_fst_2867_);
v___y_2786_ = v_isEq_2857_;
v_isHEq_2787_ = v___x_2499_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
v___y_2790_ = v___y_2860_;
v___y_2791_ = v___y_2861_;
goto v___jp_2785_;
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_val_2873_);
lean_dec(v_fst_2869_);
lean_dec(v_fst_2867_);
lean_dec_ref(v___x_2637_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2882_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2874_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2874_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_dec(v_a_2872_);
lean_dec(v_snd_2870_);
lean_dec(v_fst_2869_);
lean_dec(v_fst_2867_);
v___y_2786_ = v_isEq_2857_;
v_isHEq_2787_ = v___x_2499_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
v___y_2790_ = v___y_2860_;
v___y_2791_ = v___y_2861_;
goto v___jp_2785_;
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_snd_2870_);
lean_dec(v_fst_2869_);
lean_dec(v_fst_2867_);
lean_dec_ref(v___x_2637_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2890_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2871_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2871_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_dec(v_a_2863_);
v___y_2786_ = v_isEq_2857_;
v_isHEq_2787_ = v___x_2593_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
v___y_2790_ = v___y_2860_;
v___y_2791_ = v___y_2861_;
goto v___jp_2785_;
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v___x_2637_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2898_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2862_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2862_);
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
v___jp_2906_:
{
lean_object* v___x_2911_; 
lean_inc_ref(v___x_2637_);
v___x_2911_ = l_Lean_Meta_matchEq_x3f(v___x_2637_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
if (lean_obj_tag(v_a_2912_) == 1)
{
lean_object* v_val_2913_; lean_object* v_snd_2914_; lean_object* v_fst_2915_; lean_object* v_snd_2916_; lean_object* v___x_2917_; 
v_val_2913_ = lean_ctor_get(v_a_2912_, 0);
lean_inc(v_val_2913_);
lean_dec_ref_known(v_a_2912_, 1);
v_snd_2914_ = lean_ctor_get(v_val_2913_, 1);
lean_inc(v_snd_2914_);
lean_dec(v_val_2913_);
v_fst_2915_ = lean_ctor_get(v_snd_2914_, 0);
lean_inc(v_fst_2915_);
v_snd_2916_ = lean_ctor_get(v_snd_2914_, 1);
lean_inc(v_snd_2916_);
lean_dec(v_snd_2914_);
v___x_2917_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2915_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
if (lean_obj_tag(v_a_2918_) == 1)
{
lean_object* v_val_2919_; lean_object* v___x_2920_; 
v_val_2919_ = lean_ctor_get(v_a_2918_, 0);
lean_inc(v_val_2919_);
lean_dec_ref_known(v_a_2918_, 1);
v___x_2920_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2916_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
if (lean_obj_tag(v_a_2921_) == 1)
{
lean_object* v_toConstantVal_2922_; lean_object* v_val_2923_; lean_object* v_toConstantVal_2924_; lean_object* v_name_2925_; lean_object* v_name_2926_; uint8_t v___x_2927_; 
v_toConstantVal_2922_ = lean_ctor_get(v_val_2919_, 0);
lean_inc_ref(v_toConstantVal_2922_);
lean_dec(v_val_2919_);
v_val_2923_ = lean_ctor_get(v_a_2921_, 0);
lean_inc(v_val_2923_);
lean_dec_ref_known(v_a_2921_, 1);
v_toConstantVal_2924_ = lean_ctor_get(v_val_2923_, 0);
lean_inc_ref(v_toConstantVal_2924_);
lean_dec(v_val_2923_);
v_name_2925_ = lean_ctor_get(v_toConstantVal_2922_, 0);
lean_inc(v_name_2925_);
lean_dec_ref(v_toConstantVal_2922_);
v_name_2926_ = lean_ctor_get(v_toConstantVal_2924_, 0);
lean_inc(v_name_2926_);
lean_dec_ref(v_toConstantVal_2924_);
v___x_2927_ = lean_name_eq(v_name_2925_, v_name_2926_);
lean_dec(v_name_2926_);
lean_dec(v_name_2925_);
if (v___x_2927_ == 0)
{
lean_dec_ref(v___x_2637_);
lean_dec_ref(v_config_2488_);
v___y_2526_ = v___y_2909_;
v___y_2527_ = v___y_2910_;
v___y_2528_ = v___y_2908_;
v___y_2529_ = v___y_2907_;
goto v___jp_2525_;
}
else
{
if (v___x_2593_ == 0)
{
lean_del_object(v___x_2522_);
v_isEq_2857_ = v___x_2499_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
v___y_2860_ = v___y_2909_;
v___y_2861_ = v___y_2910_;
goto v___jp_2856_;
}
else
{
lean_dec_ref(v___x_2637_);
lean_dec_ref(v_config_2488_);
v___y_2526_ = v___y_2909_;
v___y_2527_ = v___y_2910_;
v___y_2528_ = v___y_2908_;
v___y_2529_ = v___y_2907_;
goto v___jp_2525_;
}
}
}
else
{
lean_dec(v_a_2921_);
lean_dec(v_val_2919_);
lean_del_object(v___x_2522_);
v_isEq_2857_ = v___x_2499_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
v___y_2860_ = v___y_2909_;
v___y_2861_ = v___y_2910_;
goto v___jp_2856_;
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_val_2919_);
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2928_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2920_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2920_);
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
lean_dec(v_a_2918_);
lean_dec(v_snd_2916_);
lean_del_object(v___x_2522_);
v_isEq_2857_ = v___x_2499_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
v___y_2860_ = v___y_2909_;
v___y_2861_ = v___y_2910_;
goto v___jp_2856_;
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_snd_2916_);
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2936_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2917_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2917_);
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
else
{
lean_dec(v_a_2912_);
lean_del_object(v___x_2522_);
v_isEq_2857_ = v___x_2593_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
v___y_2860_ = v___y_2909_;
v___y_2861_ = v___y_2910_;
goto v___jp_2856_;
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2944_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2911_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2911_);
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
lean_inc_ref(v___x_2637_);
v___x_2957_ = l_Lean_refutableHasNotBit_x3f(v___x_2637_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
if (lean_obj_tag(v_a_2958_) == 1)
{
lean_object* v_val_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec_ref(v_config_2488_);
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
lean_inc(v_mvarId_2489_);
v___x_2963_ = l_Lean_MVarId_getType(v_mvarId_2489_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = l_Lean_LocalDecl_toExpr(v_val_2520_);
v___x_2966_ = l_Lean_Meta_mkAbsurd(v_a_2964_, v_val_2959_, v___x_2965_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2968_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2489_, v_a_2967_, v___y_2954_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
lean_dec_ref_known(v___x_2968_, 1);
v___x_2969_ = lean_box(v___x_2499_);
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
lean_ctor_set(v___x_2972_, 1, v___x_2524_);
v_a_2506_ = v___x_2972_;
goto v___jp_2505_;
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_del_object(v___x_2961_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
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
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
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
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
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
lean_inc_ref(v___x_2637_);
v___x_2999_ = l_Lean_Meta_matchNe_x3f(v___x_2637_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
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
v___y_2907_ = v___y_2953_;
v___y_2908_ = v___y_2954_;
v___y_2909_ = v___y_2955_;
v___y_2910_ = v___y_2956_;
goto v___jp_2906_;
}
else
{
lean_object* v___x_3014_; 
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec_ref(v_config_2488_);
lean_inc(v_mvarId_2489_);
v___x_3014_ = l_Lean_MVarId_getType(v_mvarId_2489_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
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
v___x_3018_ = l_Lean_LocalDecl_toExpr(v_val_2520_);
v___x_3019_ = l_Lean_Meta_mkAbsurd(v_a_3015_, v_a_3017_, v___x_3018_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2489_, v_a_3020_, v___y_2954_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_dec_ref_known(v___x_3021_, 1);
v___x_3022_ = lean_box(v___x_2499_);
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
lean_ctor_set(v___x_3009_, 1, v___x_2524_);
lean_ctor_set(v___x_3009_, 0, v___x_3024_);
v___x_3026_ = v___x_3009_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_2524_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
v_a_2506_ = v___x_3026_;
goto v___jp_2505_;
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_del_object(v___x_3009_);
lean_del_object(v___x_3003_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
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
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
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
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
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
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
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
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
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
v___y_2907_ = v___y_2953_;
v___y_2908_ = v___y_2954_;
v___y_2909_ = v___y_2955_;
v___y_2910_ = v___y_2956_;
goto v___jp_2906_;
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
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
lean_dec_ref(v___x_2637_);
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
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
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
v_a_2514_ = v___x_2565_;
goto v___jp_2513_;
}
v___jp_2525_:
{
lean_object* v___x_2530_; 
lean_inc(v_mvarId_2489_);
v___x_2530_ = l_Lean_MVarId_getType(v_mvarId_2489_, v___y_2529_, v___y_2528_, v___y_2526_, v___y_2527_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = l_Lean_LocalDecl_toExpr(v_val_2520_);
v___x_2533_ = l_Lean_Meta_mkNoConfusion(v_a_2531_, v___x_2532_, v___y_2529_, v___y_2528_, v___y_2526_, v___y_2527_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2535_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2489_, v_a_2534_, v___y_2528_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_dec_ref_known(v___x_2535_, 1);
v___x_2536_ = lean_box(v___x_2499_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v___x_2536_);
v___x_2538_ = v___x_2522_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v___x_2524_);
v_a_2506_ = v___x_2539_;
goto v___jp_2505_;
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_del_object(v___x_2522_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
v_a_2541_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2535_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2535_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_del_object(v___x_2522_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
v_a_2549_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2533_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2533_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_del_object(v___x_2522_);
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
v_a_2557_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2530_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2530_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
v___jp_2566_:
{
lean_object* v_searchFuel_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v_searchFuel_2571_ = lean_ctor_get(v_config_2488_, 0);
v___x_2572_ = l_Lean_LocalDecl_fvarId(v_val_2520_);
lean_dec(v_val_2520_);
lean_inc(v_searchFuel_2571_);
lean_inc(v_mvarId_2489_);
v___x_2573_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2489_, v___x_2572_, v_searchFuel_2571_, v___y_2568_, v___y_2567_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; uint8_t v___x_2575_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = lean_unbox(v_a_2574_);
lean_dec(v_a_2574_);
if (v___x_2575_ == 0)
{
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
v_a_2514_ = v___x_2565_;
goto v___jp_2513_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v___x_2576_ = lean_box(v___x_2499_);
v___x_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
lean_ctor_set(v___x_2578_, 1, v___x_2524_);
v_a_2506_ = v___x_2578_;
goto v___jp_2505_;
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2579_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2573_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2573_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
v___jp_2587_:
{
if (v___y_2592_ == 0)
{
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
v_a_2514_ = v___x_2565_;
goto v___jp_2513_;
}
else
{
v___y_2567_ = v___y_2588_;
v___y_2568_ = v___y_2589_;
v___y_2569_ = v___y_2590_;
v___y_2570_ = v___y_2591_;
goto v___jp_2566_;
}
}
v___jp_2594_:
{
if (v___y_2597_ == 0)
{
v___y_2567_ = v___y_2595_;
v___y_2568_ = v___y_2596_;
v___y_2569_ = v___y_2598_;
v___y_2570_ = v___y_2599_;
goto v___jp_2566_;
}
else
{
v___y_2588_ = v___y_2595_;
v___y_2589_ = v___y_2596_;
v___y_2590_ = v___y_2598_;
v___y_2591_ = v___y_2599_;
v___y_2592_ = v___x_2593_;
goto v___jp_2587_;
}
}
v___jp_2600_:
{
if (v___y_2606_ == 0)
{
v___y_2588_ = v___y_2601_;
v___y_2589_ = v___y_2602_;
v___y_2590_ = v___y_2604_;
v___y_2591_ = v___y_2605_;
v___y_2592_ = v___x_2593_;
goto v___jp_2587_;
}
else
{
v___y_2595_ = v___y_2601_;
v___y_2596_ = v___y_2602_;
v___y_2597_ = v___y_2603_;
v___y_2598_ = v___y_2604_;
v___y_2599_ = v___y_2605_;
goto v___jp_2594_;
}
}
v___jp_2607_:
{
uint8_t v_emptyType_2614_; 
v_emptyType_2614_ = lean_ctor_get_uint8(v_config_2488_, sizeof(void*)*1 + 1);
if (v_emptyType_2614_ == 0)
{
v___y_2601_ = v___y_2611_;
v___y_2602_ = v___y_2610_;
v___y_2603_ = v___y_2608_;
v___y_2604_ = v___y_2612_;
v___y_2605_ = v___y_2613_;
v___y_2606_ = v___x_2593_;
goto v___jp_2600_;
}
else
{
if (v___y_2609_ == 0)
{
v___y_2595_ = v___y_2611_;
v___y_2596_ = v___y_2610_;
v___y_2597_ = v___y_2608_;
v___y_2598_ = v___y_2612_;
v___y_2599_ = v___y_2613_;
goto v___jp_2594_;
}
else
{
v___y_2601_ = v___y_2611_;
v___y_2602_ = v___y_2610_;
v___y_2603_ = v___y_2608_;
v___y_2604_ = v___y_2612_;
v___y_2605_ = v___y_2613_;
v___y_2606_ = v___x_2593_;
goto v___jp_2600_;
}
}
}
v___jp_2615_:
{
if (v___y_2622_ == 0)
{
v___y_2608_ = v___y_2616_;
v___y_2609_ = v___y_2617_;
v___y_2610_ = v___y_2619_;
v___y_2611_ = v___y_2620_;
v___y_2612_ = v___y_2621_;
v___y_2613_ = v___y_2618_;
goto v___jp_2607_;
}
else
{
lean_object* v___x_2623_; 
lean_inc(v_val_2520_);
lean_inc(v_mvarId_2489_);
v___x_2623_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2489_, v_val_2520_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2618_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; uint8_t v___x_2625_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = lean_unbox(v_a_2624_);
lean_dec(v_a_2624_);
if (v___x_2625_ == 0)
{
v___y_2608_ = v___y_2616_;
v___y_2609_ = v___y_2617_;
v___y_2610_ = v___y_2619_;
v___y_2611_ = v___y_2620_;
v___y_2612_ = v___y_2621_;
v___y_2613_ = v___y_2618_;
goto v___jp_2607_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec(v_val_2520_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v___x_2626_ = lean_box(v___x_2499_);
v___x_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
lean_ctor_set(v___x_2628_, 1, v___x_2524_);
v_a_2506_ = v___x_2628_;
goto v___jp_2505_;
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_val_2520_);
lean_del_object(v___x_2503_);
lean_dec(v_snd_2501_);
lean_dec(v_mvarId_2489_);
lean_dec_ref(v_config_2488_);
v_a_2629_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2623_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2623_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
}
}
v___jp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_a_2506_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2507_);
v___x_2509_ = v___x_2503_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_snd_2501_);
v___x_2509_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
}
v___jp_2513_:
{
lean_object* v___x_2515_; size_t v___x_2516_; size_t v___x_2517_; lean_object* v___x_2518_; 
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2512_);
lean_ctor_set(v___x_2515_, 1, v_a_2514_);
v___x_2516_ = ((size_t)1ULL);
v___x_2517_ = lean_usize_add(v_i_2492_, v___x_2516_);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2488_, v_mvarId_2489_, v_as_2490_, v_sz_2491_, v___x_2517_, v___x_2515_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2518_;
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
lean_object* v_snd_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3853_; 
v_snd_3183_ = lean_ctor_get(v_b_3175_, 1);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_b_3175_);
if (v_isSharedCheck_3853_ == 0)
{
lean_object* v_unused_3854_; 
v_unused_3854_ = lean_ctor_get(v_b_3175_, 0);
lean_dec(v_unused_3854_);
v___x_3185_ = v_b_3175_;
v_isShared_3186_ = v_isSharedCheck_3853_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_snd_3183_);
lean_dec(v_b_3175_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3853_;
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
lean_object* v_val_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3852_; 
v_val_3202_ = lean_ctor_get(v_a_3201_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_a_3201_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3204_ = v_a_3201_;
v_isShared_3205_ = v_isSharedCheck_3852_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_val_3202_);
lean_dec(v_a_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3852_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___x_3248_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; uint8_t v___y_3276_; uint8_t v___x_3277_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; uint8_t v___y_3283_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; uint8_t v___y_3289_; uint8_t v___y_3290_; uint8_t v___y_3292_; uint8_t v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3300_; uint8_t v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; uint8_t v___y_3305_; uint8_t v___y_3306_; 
v___x_3206_ = lean_box(0);
v___x_3248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3277_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3202_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3322_; uint8_t v___y_3324_; uint8_t v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3333_; lean_object* v___y_3334_; uint8_t v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; uint8_t v___y_3338_; lean_object* v___y_3339_; uint8_t v___y_3340_; lean_object* v___y_3343_; lean_object* v___y_3344_; uint8_t v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; uint8_t v___y_3348_; lean_object* v_a_3349_; lean_object* v___y_3353_; lean_object* v___y_3354_; uint8_t v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; uint8_t v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3404_; lean_object* v___y_3405_; uint8_t v___y_3406_; lean_object* v___y_3407_; uint8_t v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3433_; lean_object* v___y_3434_; uint8_t v___y_3435_; lean_object* v___y_3436_; uint8_t v___y_3437_; lean_object* v___y_3438_; uint8_t v___y_3439_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; uint8_t v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; uint8_t v___y_3448_; lean_object* v___y_3451_; lean_object* v___y_3452_; uint8_t v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3456_; uint8_t v___y_3457_; lean_object* v___y_3470_; lean_object* v___y_3471_; uint8_t v___y_3472_; lean_object* v___y_3473_; uint8_t v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; uint8_t v___y_3478_; uint8_t v_isHEq_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; uint8_t v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; uint8_t v_isEq_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___x_3782_; 
v___x_3322_ = l_Lean_LocalDecl_type(v_val_3202_);
lean_inc_ref(v___x_3322_);
v___x_3782_ = l_Lean_Meta_matchNot_x3f(v___x_3322_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
if (lean_obj_tag(v_a_3783_) == 1)
{
lean_object* v_val_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3843_; 
v_val_3784_ = lean_ctor_get(v_a_3783_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_a_3783_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3786_ = v_a_3783_;
v_isShared_3787_ = v_isSharedCheck_3843_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_val_3784_);
lean_dec(v_a_3783_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3843_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3784_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
if (lean_obj_tag(v_a_3789_) == 1)
{
lean_object* v_val_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
v_val_3790_ = lean_ctor_get(v_a_3789_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_a_3789_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3792_ = v_a_3789_;
v_isShared_3793_ = v_isSharedCheck_3834_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_val_3790_);
lean_dec(v_a_3789_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3834_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3794_; 
lean_inc(v_mvarId_3171_);
v___x_3794_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3794_, 1);
v___x_3796_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3797_ = l_Lean_mkFVar(v_val_3790_);
v___x_3798_ = l_Lean_Expr_app___override(v___x_3796_, v___x_3797_);
v___x_3799_ = l_Lean_Meta_mkFalseElim(v_a_3795_, v___x_3798_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3801_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v___x_3799_, 1);
v___x_3801_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3800_, v___y_3177_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v___x_3802_; lean_object* v___x_3804_; 
lean_dec_ref_known(v___x_3801_, 1);
v___x_3802_ = lean_box(v___x_3181_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3802_);
v___x_3804_ = v___x_3792_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
lean_ctor_set(v___x_3805_, 1, v___x_3206_);
if (v_isShared_3787_ == 0)
{
lean_ctor_set_tag(v___x_3786_, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3805_);
v___x_3807_ = v___x_3786_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
v_a_3188_ = v___x_3807_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_del_object(v___x_3792_);
lean_del_object(v___x_3786_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3810_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3801_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3801_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_del_object(v___x_3792_);
lean_del_object(v___x_3786_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3818_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3799_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3799_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_del_object(v___x_3792_);
lean_dec(v_val_3790_);
lean_del_object(v___x_3786_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3826_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3794_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3794_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
else
{
lean_dec(v_a_3789_);
lean_del_object(v___x_3786_);
v___y_3646_ = v___y_3176_;
v___y_3647_ = v___y_3177_;
v___y_3648_ = v___y_3178_;
v___y_3649_ = v___y_3179_;
goto v___jp_3645_;
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
lean_del_object(v___x_3786_);
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3835_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3788_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3788_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
else
{
lean_dec(v_a_3783_);
v___y_3646_ = v___y_3176_;
v___y_3647_ = v___y_3177_;
v___y_3648_ = v___y_3178_;
v___y_3649_ = v___y_3179_;
goto v___jp_3645_;
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3844_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3782_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3782_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
v___jp_3323_:
{
uint8_t v_genDiseq_3330_; 
v_genDiseq_3330_ = lean_ctor_get_uint8(v_config_3170_, sizeof(void*)*1 + 2);
if (v_genDiseq_3330_ == 0)
{
lean_dec_ref(v___x_3322_);
v___y_3300_ = v___y_3328_;
v___y_3301_ = v___y_3324_;
v___y_3302_ = v___y_3329_;
v___y_3303_ = v___y_3327_;
v___y_3304_ = v___y_3326_;
v___y_3305_ = v___y_3325_;
v___y_3306_ = v___x_3277_;
goto v___jp_3299_;
}
else
{
uint8_t v___x_3331_; 
v___x_3331_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3322_);
v___y_3300_ = v___y_3328_;
v___y_3301_ = v___y_3324_;
v___y_3302_ = v___y_3329_;
v___y_3303_ = v___y_3327_;
v___y_3304_ = v___y_3326_;
v___y_3305_ = v___y_3325_;
v___y_3306_ = v___x_3331_;
goto v___jp_3299_;
}
}
v___jp_3332_:
{
if (v___y_3340_ == 0)
{
lean_dec_ref(v___y_3337_);
v___y_3324_ = v___y_3335_;
v___y_3325_ = v___y_3338_;
v___y_3326_ = v___y_3336_;
v___y_3327_ = v___y_3334_;
v___y_3328_ = v___y_3339_;
v___y_3329_ = v___y_3333_;
goto v___jp_3323_;
}
else
{
lean_object* v___x_3341_; 
lean_dec_ref(v___x_3322_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___y_3337_);
return v___x_3341_;
}
}
v___jp_3342_:
{
uint8_t v___x_3350_; 
v___x_3350_ = l_Lean_Exception_isInterrupt(v_a_3349_);
if (v___x_3350_ == 0)
{
uint8_t v___x_3351_; 
lean_inc_ref(v_a_3349_);
v___x_3351_ = l_Lean_Exception_isRuntime(v_a_3349_);
v___y_3333_ = v___y_3343_;
v___y_3334_ = v___y_3344_;
v___y_3335_ = v___y_3345_;
v___y_3336_ = v___y_3346_;
v___y_3337_ = v_a_3349_;
v___y_3338_ = v___y_3348_;
v___y_3339_ = v___y_3347_;
v___y_3340_ = v___x_3351_;
goto v___jp_3332_;
}
else
{
v___y_3333_ = v___y_3343_;
v___y_3334_ = v___y_3344_;
v___y_3335_ = v___y_3345_;
v___y_3336_ = v___y_3346_;
v___y_3337_ = v_a_3349_;
v___y_3338_ = v___y_3348_;
v___y_3339_ = v___y_3347_;
v___y_3340_ = v___x_3350_;
goto v___jp_3332_;
}
}
v___jp_3352_:
{
if (lean_obj_tag(v___y_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_a_3361_ = lean_ctor_get(v___y_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___y_3360_, 1);
v___x_3362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3363_ = l_Lean_Expr_isConstOf(v_a_3361_, v___x_3362_);
lean_dec(v_a_3361_);
if (v___x_3363_ == 0)
{
lean_dec_ref(v___y_3357_);
v___y_3324_ = v___y_3355_;
v___y_3325_ = v___y_3358_;
v___y_3326_ = v___y_3356_;
v___y_3327_ = v___y_3354_;
v___y_3328_ = v___y_3359_;
v___y_3329_ = v___y_3353_;
goto v___jp_3323_;
}
else
{
lean_object* v___x_3364_; 
lean_inc_ref(v___y_3357_);
v___x_3364_ = l_Lean_Meta_mkEqRefl(v___y_3357_, v___y_3356_, v___y_3354_, v___y_3359_, v___y_3353_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; lean_object* v_dummy_3367_; lean_object* v_nargs_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v___x_3366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3367_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3368_ = l_Lean_Expr_getAppNumArgs(v___y_3357_);
lean_inc(v_nargs_3368_);
v___x_3369_ = lean_mk_array(v_nargs_3368_, v_dummy_3367_);
v___x_3370_ = lean_unsigned_to_nat(1u);
v___x_3371_ = lean_nat_sub(v_nargs_3368_, v___x_3370_);
lean_dec(v_nargs_3368_);
v___x_3372_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3357_, v___x_3369_, v___x_3371_);
v___x_3373_ = lean_array_push(v___x_3372_, v_a_3365_);
v___x_3374_ = l_Lean_mkAppN(v___x_3366_, v___x_3373_);
lean_dec_ref(v___x_3373_);
lean_inc(v_mvarId_3171_);
v___x_3375_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3356_, v___y_3354_, v___y_3359_, v___y_3353_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
lean_inc(v_val_3202_);
v___x_3377_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3378_ = l_Lean_Meta_mkAbsurd(v_a_3376_, v___x_3377_, v___x_3374_, v___y_3356_, v___y_3354_, v___y_3359_, v___y_3353_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3398_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3398_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3398_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; 
lean_inc(v_mvarId_3171_);
v___x_3383_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3379_, v___y_3354_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v___x_3322_);
lean_dec(v_val_3202_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; 
v_unused_3396_ = lean_ctor_get(v___x_3383_, 0);
lean_dec(v_unused_3396_);
v___x_3385_ = v___x_3383_;
v_isShared_3386_ = v_isSharedCheck_3395_;
goto v_resetjp_3384_;
}
else
{
lean_dec(v___x_3383_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3395_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3387_ = lean_box(v___x_3181_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set_tag(v___x_3385_, 1);
lean_ctor_set(v___x_3385_, 0, v___x_3387_);
v___x_3389_ = v___x_3385_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v___x_3206_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3390_);
v___x_3392_ = v___x_3381_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
v_a_3188_ = v___x_3392_;
goto v___jp_3187_;
}
}
}
}
else
{
lean_object* v_a_3397_; 
lean_del_object(v___x_3381_);
v_a_3397_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3383_, 1);
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v_a_3349_ = v_a_3397_;
goto v___jp_3342_;
}
}
}
else
{
lean_object* v_a_3399_; 
v_a_3399_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3378_, 1);
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v_a_3349_ = v_a_3399_;
goto v___jp_3342_;
}
}
else
{
lean_object* v_a_3400_; 
lean_dec_ref(v___x_3374_);
v_a_3400_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3375_, 1);
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v_a_3349_ = v_a_3400_;
goto v___jp_3342_;
}
}
else
{
lean_object* v_a_3401_; 
lean_dec_ref(v___y_3357_);
v_a_3401_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3364_, 1);
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v_a_3349_ = v_a_3401_;
goto v___jp_3342_;
}
}
}
else
{
lean_object* v_a_3402_; 
lean_dec_ref(v___y_3357_);
v_a_3402_ = lean_ctor_get(v___y_3360_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___y_3360_, 1);
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v_a_3349_ = v_a_3402_;
goto v___jp_3342_;
}
}
v___jp_3403_:
{
lean_object* v___x_3410_; 
lean_inc_ref(v___x_3322_);
v___x_3410_ = l_Lean_Meta_mkDecide(v___x_3322_, v___y_3407_, v___y_3405_, v___y_3409_, v___y_3404_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3412_; uint8_t v_transparency_3413_; uint8_t v___x_3414_; uint8_t v___x_3415_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v___x_3412_ = l_Lean_Meta_Context_config(v___y_3407_);
v_transparency_3413_ = lean_ctor_get_uint8(v___x_3412_, 9);
lean_dec_ref(v___x_3412_);
v___x_3414_ = 1;
v___x_3415_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3413_, v___x_3414_);
if (v___x_3415_ == 0)
{
lean_object* v_keyedConfig_3416_; uint8_t v_trackZetaDelta_3417_; lean_object* v_zetaDeltaSet_3418_; lean_object* v_lctx_3419_; lean_object* v_localInstances_3420_; lean_object* v_defEqCtx_x3f_3421_; lean_object* v_synthPendingDepth_3422_; lean_object* v_customCanUnfoldPredicate_x3f_3423_; uint8_t v_univApprox_3424_; uint8_t v_inTypeClassResolution_3425_; uint8_t v_cacheInferType_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v_keyedConfig_3416_ = lean_ctor_get(v___y_3407_, 0);
v_trackZetaDelta_3417_ = lean_ctor_get_uint8(v___y_3407_, sizeof(void*)*7);
v_zetaDeltaSet_3418_ = lean_ctor_get(v___y_3407_, 1);
v_lctx_3419_ = lean_ctor_get(v___y_3407_, 2);
v_localInstances_3420_ = lean_ctor_get(v___y_3407_, 3);
v_defEqCtx_x3f_3421_ = lean_ctor_get(v___y_3407_, 4);
v_synthPendingDepth_3422_ = lean_ctor_get(v___y_3407_, 5);
v_customCanUnfoldPredicate_x3f_3423_ = lean_ctor_get(v___y_3407_, 6);
v_univApprox_3424_ = lean_ctor_get_uint8(v___y_3407_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3425_ = lean_ctor_get_uint8(v___y_3407_, sizeof(void*)*7 + 2);
v_cacheInferType_3426_ = lean_ctor_get_uint8(v___y_3407_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3416_);
v___x_3427_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3414_, v_keyedConfig_3416_);
lean_inc(v_customCanUnfoldPredicate_x3f_3423_);
lean_inc(v_synthPendingDepth_3422_);
lean_inc(v_defEqCtx_x3f_3421_);
lean_inc_ref(v_localInstances_3420_);
lean_inc_ref(v_lctx_3419_);
lean_inc(v_zetaDeltaSet_3418_);
v___x_3428_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v_zetaDeltaSet_3418_);
lean_ctor_set(v___x_3428_, 2, v_lctx_3419_);
lean_ctor_set(v___x_3428_, 3, v_localInstances_3420_);
lean_ctor_set(v___x_3428_, 4, v_defEqCtx_x3f_3421_);
lean_ctor_set(v___x_3428_, 5, v_synthPendingDepth_3422_);
lean_ctor_set(v___x_3428_, 6, v_customCanUnfoldPredicate_x3f_3423_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7, v_trackZetaDelta_3417_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7 + 1, v_univApprox_3424_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3425_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*7 + 3, v_cacheInferType_3426_);
lean_inc(v___y_3404_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3405_);
lean_inc(v_a_3411_);
v___x_3429_ = lean_whnf(v_a_3411_, v___x_3428_, v___y_3405_, v___y_3409_, v___y_3404_);
v___y_3353_ = v___y_3404_;
v___y_3354_ = v___y_3405_;
v___y_3355_ = v___y_3406_;
v___y_3356_ = v___y_3407_;
v___y_3357_ = v_a_3411_;
v___y_3358_ = v___y_3408_;
v___y_3359_ = v___y_3409_;
v___y_3360_ = v___x_3429_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3430_; 
lean_inc(v___y_3404_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3405_);
lean_inc_ref(v___y_3407_);
lean_inc(v_a_3411_);
v___x_3430_ = lean_whnf(v_a_3411_, v___y_3407_, v___y_3405_, v___y_3409_, v___y_3404_);
v___y_3353_ = v___y_3404_;
v___y_3354_ = v___y_3405_;
v___y_3355_ = v___y_3406_;
v___y_3356_ = v___y_3407_;
v___y_3357_ = v_a_3411_;
v___y_3358_ = v___y_3408_;
v___y_3359_ = v___y_3409_;
v___y_3360_ = v___x_3430_;
goto v___jp_3352_;
}
}
else
{
lean_object* v_a_3431_; 
v_a_3431_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3410_, 1);
v___y_3343_ = v___y_3404_;
v___y_3344_ = v___y_3405_;
v___y_3345_ = v___y_3406_;
v___y_3346_ = v___y_3407_;
v___y_3347_ = v___y_3409_;
v___y_3348_ = v___y_3408_;
v_a_3349_ = v_a_3431_;
goto v___jp_3342_;
}
}
v___jp_3432_:
{
if (v___y_3439_ == 0)
{
v___y_3324_ = v___y_3435_;
v___y_3325_ = v___y_3437_;
v___y_3326_ = v___y_3436_;
v___y_3327_ = v___y_3434_;
v___y_3328_ = v___y_3438_;
v___y_3329_ = v___y_3433_;
goto v___jp_3323_;
}
else
{
v___y_3404_ = v___y_3433_;
v___y_3405_ = v___y_3434_;
v___y_3406_ = v___y_3435_;
v___y_3407_ = v___y_3436_;
v___y_3408_ = v___y_3437_;
v___y_3409_ = v___y_3438_;
goto v___jp_3403_;
}
}
v___jp_3440_:
{
if (v___y_3448_ == 0)
{
lean_dec_ref(v___y_3441_);
v___y_3433_ = v___y_3442_;
v___y_3434_ = v___y_3443_;
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3445_;
v___y_3437_ = v___y_3447_;
v___y_3438_ = v___y_3446_;
v___y_3439_ = v___x_3277_;
goto v___jp_3432_;
}
else
{
uint8_t v___x_3449_; 
v___x_3449_ = l_Lean_Expr_hasFVar(v___y_3441_);
lean_dec_ref(v___y_3441_);
if (v___x_3449_ == 0)
{
v___y_3404_ = v___y_3442_;
v___y_3405_ = v___y_3443_;
v___y_3406_ = v___y_3444_;
v___y_3407_ = v___y_3445_;
v___y_3408_ = v___y_3447_;
v___y_3409_ = v___y_3446_;
goto v___jp_3403_;
}
else
{
v___y_3433_ = v___y_3442_;
v___y_3434_ = v___y_3443_;
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3445_;
v___y_3437_ = v___y_3447_;
v___y_3438_ = v___y_3446_;
v___y_3439_ = v___x_3277_;
goto v___jp_3432_;
}
}
}
v___jp_3450_:
{
lean_object* v___x_3458_; 
lean_inc_ref(v___x_3322_);
v___x_3458_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3322_, v___y_3452_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; uint8_t v___x_3460_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
v___x_3460_ = l_Lean_Expr_hasMVar(v_a_3459_);
if (v___x_3460_ == 0)
{
v___y_3441_ = v_a_3459_;
v___y_3442_ = v___y_3451_;
v___y_3443_ = v___y_3452_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3454_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___y_3456_;
v___y_3448_ = v___y_3457_;
goto v___jp_3440_;
}
else
{
v___y_3441_ = v_a_3459_;
v___y_3442_ = v___y_3451_;
v___y_3443_ = v___y_3452_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3454_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___y_3456_;
v___y_3448_ = v___x_3277_;
goto v___jp_3440_;
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref(v___x_3322_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3461_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3458_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3458_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
v___jp_3469_:
{
if (v___y_3476_ == 0)
{
v___y_3324_ = v___y_3472_;
v___y_3325_ = v___y_3474_;
v___y_3326_ = v___y_3473_;
v___y_3327_ = v___y_3471_;
v___y_3328_ = v___y_3475_;
v___y_3329_ = v___y_3470_;
goto v___jp_3323_;
}
else
{
v___y_3451_ = v___y_3470_;
v___y_3452_ = v___y_3471_;
v___y_3453_ = v___y_3472_;
v___y_3454_ = v___y_3473_;
v___y_3455_ = v___y_3475_;
v___y_3456_ = v___y_3474_;
v___y_3457_ = v___y_3476_;
goto v___jp_3450_;
}
}
v___jp_3477_:
{
uint8_t v_useDecide_3484_; 
v_useDecide_3484_ = lean_ctor_get_uint8(v_config_3170_, sizeof(void*)*1);
if (v_useDecide_3484_ == 0)
{
v___y_3470_ = v___y_3483_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___y_3478_;
v___y_3473_ = v___y_3480_;
v___y_3474_ = v_isHEq_3479_;
v___y_3475_ = v___y_3482_;
v___y_3476_ = v___x_3277_;
goto v___jp_3469_;
}
else
{
uint8_t v___x_3485_; 
v___x_3485_ = l_Lean_Expr_hasFVar(v___x_3322_);
if (v___x_3485_ == 0)
{
v___y_3451_ = v___y_3483_;
v___y_3452_ = v___y_3481_;
v___y_3453_ = v___y_3478_;
v___y_3454_ = v___y_3480_;
v___y_3455_ = v___y_3482_;
v___y_3456_ = v_isHEq_3479_;
v___y_3457_ = v_useDecide_3484_;
goto v___jp_3450_;
}
else
{
v___y_3470_ = v___y_3483_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___y_3478_;
v___y_3473_ = v___y_3480_;
v___y_3474_ = v_isHEq_3479_;
v___y_3475_ = v___y_3482_;
v___y_3476_ = v___x_3277_;
goto v___jp_3469_;
}
}
}
v___jp_3486_:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_Meta_isExprDefEq(v___y_3488_, v___y_3489_, v___y_3491_, v___y_3487_, v___y_3493_, v___y_3492_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; uint8_t v___x_3496_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
v___x_3496_ = lean_unbox(v_a_3495_);
lean_dec(v_a_3495_);
if (v___x_3496_ == 0)
{
v___y_3478_ = v___y_3490_;
v_isHEq_3479_ = v___x_3181_;
v___y_3480_ = v___y_3491_;
v___y_3481_ = v___y_3487_;
v___y_3482_ = v___y_3493_;
v___y_3483_ = v___y_3492_;
goto v___jp_3477_;
}
else
{
lean_object* v___x_3497_; 
lean_dec_ref(v___x_3322_);
lean_dec_ref(v_config_3170_);
lean_inc(v_mvarId_3171_);
v___x_3497_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3491_, v___y_3487_, v___y_3493_, v___y_3492_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3500_ = l_Lean_Meta_mkEqOfHEq(v___x_3499_, v___x_3181_, v___y_3491_, v___y_3487_, v___y_3493_, v___y_3492_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = l_Lean_Meta_mkNoConfusion(v_a_3498_, v_a_3501_, v___y_3491_, v___y_3487_, v___y_3493_, v___y_3492_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3504_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___x_3504_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3503_, v___y_3487_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_dec_ref_known(v___x_3504_, 1);
v___x_3505_ = lean_box(v___x_3181_);
v___x_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v___x_3206_);
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
v_a_3188_ = v___x_3508_;
goto v___jp_3187_;
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3509_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3504_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3504_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3517_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3502_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3502_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v_a_3498_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3525_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3500_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3500_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3533_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3497_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3497_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec_ref(v___x_3322_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3541_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3494_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3494_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
v___jp_3549_:
{
lean_object* v___x_3555_; 
lean_inc_ref(v___x_3322_);
v___x_3555_ = l_Lean_Meta_matchHEq_x3f(v___x_3322_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3555_, 1);
if (lean_obj_tag(v_a_3556_) == 1)
{
lean_object* v_val_3557_; lean_object* v_snd_3558_; lean_object* v_snd_3559_; lean_object* v_fst_3560_; lean_object* v_fst_3561_; lean_object* v_fst_3562_; lean_object* v_snd_3563_; lean_object* v___x_3564_; 
v_val_3557_ = lean_ctor_get(v_a_3556_, 0);
lean_inc(v_val_3557_);
lean_dec_ref_known(v_a_3556_, 1);
v_snd_3558_ = lean_ctor_get(v_val_3557_, 1);
lean_inc(v_snd_3558_);
v_snd_3559_ = lean_ctor_get(v_snd_3558_, 1);
lean_inc(v_snd_3559_);
v_fst_3560_ = lean_ctor_get(v_val_3557_, 0);
lean_inc(v_fst_3560_);
lean_dec(v_val_3557_);
v_fst_3561_ = lean_ctor_get(v_snd_3558_, 0);
lean_inc(v_fst_3561_);
lean_dec(v_snd_3558_);
v_fst_3562_ = lean_ctor_get(v_snd_3559_, 0);
lean_inc(v_fst_3562_);
v_snd_3563_ = lean_ctor_get(v_snd_3559_, 1);
lean_inc(v_snd_3563_);
lean_dec(v_snd_3559_);
v___x_3564_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3561_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
if (lean_obj_tag(v_a_3565_) == 1)
{
lean_object* v_val_3566_; lean_object* v___x_3567_; 
v_val_3566_ = lean_ctor_get(v_a_3565_, 0);
lean_inc(v_val_3566_);
lean_dec_ref_known(v_a_3565_, 1);
v___x_3567_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3563_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
if (lean_obj_tag(v_a_3568_) == 1)
{
lean_object* v_toConstantVal_3569_; lean_object* v_val_3570_; lean_object* v_toConstantVal_3571_; lean_object* v_name_3572_; lean_object* v_name_3573_; uint8_t v___x_3574_; 
v_toConstantVal_3569_ = lean_ctor_get(v_val_3566_, 0);
lean_inc_ref(v_toConstantVal_3569_);
lean_dec(v_val_3566_);
v_val_3570_ = lean_ctor_get(v_a_3568_, 0);
lean_inc(v_val_3570_);
lean_dec_ref_known(v_a_3568_, 1);
v_toConstantVal_3571_ = lean_ctor_get(v_val_3570_, 0);
lean_inc_ref(v_toConstantVal_3571_);
lean_dec(v_val_3570_);
v_name_3572_ = lean_ctor_get(v_toConstantVal_3569_, 0);
lean_inc(v_name_3572_);
lean_dec_ref(v_toConstantVal_3569_);
v_name_3573_ = lean_ctor_get(v_toConstantVal_3571_, 0);
lean_inc(v_name_3573_);
lean_dec_ref(v_toConstantVal_3571_);
v___x_3574_ = lean_name_eq(v_name_3572_, v_name_3573_);
lean_dec(v_name_3573_);
lean_dec(v_name_3572_);
if (v___x_3574_ == 0)
{
v___y_3487_ = v___y_3552_;
v___y_3488_ = v_fst_3560_;
v___y_3489_ = v_fst_3562_;
v___y_3490_ = v_isEq_3550_;
v___y_3491_ = v___y_3551_;
v___y_3492_ = v___y_3554_;
v___y_3493_ = v___y_3553_;
goto v___jp_3486_;
}
else
{
if (v___x_3277_ == 0)
{
lean_dec(v_fst_3562_);
lean_dec(v_fst_3560_);
v___y_3478_ = v_isEq_3550_;
v_isHEq_3479_ = v___x_3181_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
v___y_3482_ = v___y_3553_;
v___y_3483_ = v___y_3554_;
goto v___jp_3477_;
}
else
{
v___y_3487_ = v___y_3552_;
v___y_3488_ = v_fst_3560_;
v___y_3489_ = v_fst_3562_;
v___y_3490_ = v_isEq_3550_;
v___y_3491_ = v___y_3551_;
v___y_3492_ = v___y_3554_;
v___y_3493_ = v___y_3553_;
goto v___jp_3486_;
}
}
}
else
{
lean_dec(v_a_3568_);
lean_dec(v_val_3566_);
lean_dec(v_fst_3562_);
lean_dec(v_fst_3560_);
v___y_3478_ = v_isEq_3550_;
v_isHEq_3479_ = v___x_3181_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
v___y_3482_ = v___y_3553_;
v___y_3483_ = v___y_3554_;
goto v___jp_3477_;
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v_val_3566_);
lean_dec(v_fst_3562_);
lean_dec(v_fst_3560_);
lean_dec_ref(v___x_3322_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3575_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3567_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3567_);
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
else
{
lean_dec(v_a_3565_);
lean_dec(v_snd_3563_);
lean_dec(v_fst_3562_);
lean_dec(v_fst_3560_);
v___y_3478_ = v_isEq_3550_;
v_isHEq_3479_ = v___x_3181_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
v___y_3482_ = v___y_3553_;
v___y_3483_ = v___y_3554_;
goto v___jp_3477_;
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v_snd_3563_);
lean_dec(v_fst_3562_);
lean_dec(v_fst_3560_);
lean_dec_ref(v___x_3322_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3583_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3564_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3564_);
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
else
{
lean_dec(v_a_3556_);
v___y_3478_ = v_isEq_3550_;
v_isHEq_3479_ = v___x_3277_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
v___y_3482_ = v___y_3553_;
v___y_3483_ = v___y_3554_;
goto v___jp_3477_;
}
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref(v___x_3322_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3591_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3555_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3555_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
v___jp_3599_:
{
lean_object* v___x_3604_; 
lean_inc_ref(v___x_3322_);
v___x_3604_ = l_Lean_Meta_matchEq_x3f(v___x_3322_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref_known(v___x_3604_, 1);
if (lean_obj_tag(v_a_3605_) == 1)
{
lean_object* v_val_3606_; lean_object* v_snd_3607_; lean_object* v_fst_3608_; lean_object* v_snd_3609_; lean_object* v___x_3610_; 
v_val_3606_ = lean_ctor_get(v_a_3605_, 0);
lean_inc(v_val_3606_);
lean_dec_ref_known(v_a_3605_, 1);
v_snd_3607_ = lean_ctor_get(v_val_3606_, 1);
lean_inc(v_snd_3607_);
lean_dec(v_val_3606_);
v_fst_3608_ = lean_ctor_get(v_snd_3607_, 0);
lean_inc(v_fst_3608_);
v_snd_3609_ = lean_ctor_get(v_snd_3607_, 1);
lean_inc(v_snd_3609_);
lean_dec(v_snd_3607_);
v___x_3610_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3608_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
if (lean_obj_tag(v_a_3611_) == 1)
{
lean_object* v_val_3612_; lean_object* v___x_3613_; 
v_val_3612_ = lean_ctor_get(v_a_3611_, 0);
lean_inc(v_val_3612_);
lean_dec_ref_known(v_a_3611_, 1);
v___x_3613_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3609_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
if (lean_obj_tag(v_a_3614_) == 1)
{
lean_object* v_toConstantVal_3615_; lean_object* v_val_3616_; lean_object* v_toConstantVal_3617_; lean_object* v_name_3618_; lean_object* v_name_3619_; uint8_t v___x_3620_; 
v_toConstantVal_3615_ = lean_ctor_get(v_val_3612_, 0);
lean_inc_ref(v_toConstantVal_3615_);
lean_dec(v_val_3612_);
v_val_3616_ = lean_ctor_get(v_a_3614_, 0);
lean_inc(v_val_3616_);
lean_dec_ref_known(v_a_3614_, 1);
v_toConstantVal_3617_ = lean_ctor_get(v_val_3616_, 0);
lean_inc_ref(v_toConstantVal_3617_);
lean_dec(v_val_3616_);
v_name_3618_ = lean_ctor_get(v_toConstantVal_3615_, 0);
lean_inc(v_name_3618_);
lean_dec_ref(v_toConstantVal_3615_);
v_name_3619_ = lean_ctor_get(v_toConstantVal_3617_, 0);
lean_inc(v_name_3619_);
lean_dec_ref(v_toConstantVal_3617_);
v___x_3620_ = lean_name_eq(v_name_3618_, v_name_3619_);
lean_dec(v_name_3619_);
lean_dec(v_name_3618_);
if (v___x_3620_ == 0)
{
lean_dec_ref(v___x_3322_);
lean_dec_ref(v_config_3170_);
v___y_3208_ = v___y_3602_;
v___y_3209_ = v___y_3603_;
v___y_3210_ = v___y_3600_;
v___y_3211_ = v___y_3601_;
goto v___jp_3207_;
}
else
{
if (v___x_3277_ == 0)
{
lean_del_object(v___x_3204_);
v_isEq_3550_ = v___x_3181_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3602_;
v___y_3554_ = v___y_3603_;
goto v___jp_3549_;
}
else
{
lean_dec_ref(v___x_3322_);
lean_dec_ref(v_config_3170_);
v___y_3208_ = v___y_3602_;
v___y_3209_ = v___y_3603_;
v___y_3210_ = v___y_3600_;
v___y_3211_ = v___y_3601_;
goto v___jp_3207_;
}
}
}
else
{
lean_dec(v_a_3614_);
lean_dec(v_val_3612_);
lean_del_object(v___x_3204_);
v_isEq_3550_ = v___x_3181_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3602_;
v___y_3554_ = v___y_3603_;
goto v___jp_3549_;
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v_val_3612_);
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3621_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3613_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3613_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
else
{
lean_dec(v_a_3611_);
lean_dec(v_snd_3609_);
lean_del_object(v___x_3204_);
v_isEq_3550_ = v___x_3181_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3602_;
v___y_3554_ = v___y_3603_;
goto v___jp_3549_;
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_dec(v_snd_3609_);
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3629_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3610_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3610_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
else
{
lean_dec(v_a_3605_);
lean_del_object(v___x_3204_);
v_isEq_3550_ = v___x_3277_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3602_;
v___y_3554_ = v___y_3603_;
goto v___jp_3549_;
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3637_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3604_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3604_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
v___jp_3645_:
{
lean_object* v___x_3650_; 
lean_inc_ref(v___x_3322_);
v___x_3650_ = l_Lean_refutableHasNotBit_x3f(v___x_3322_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3650_, 1);
if (lean_obj_tag(v_a_3651_) == 1)
{
lean_object* v_val_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3692_; 
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
v_val_3652_ = lean_ctor_get(v_a_3651_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_a_3651_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3654_ = v_a_3651_;
v_isShared_3655_ = v_isSharedCheck_3692_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_val_3652_);
lean_dec(v_a_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3692_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; 
lean_inc(v_mvarId_3171_);
v___x_3656_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___x_3656_, 1);
v___x_3658_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3659_ = l_Lean_Meta_mkAbsurd(v_a_3657_, v_val_3652_, v___x_3658_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3659_, 1);
v___x_3661_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3660_, v___y_3647_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_dec_ref_known(v___x_3661_, 1);
v___x_3662_ = lean_box(v___x_3181_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3662_);
v___x_3664_ = v___x_3654_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
lean_ctor_set(v___x_3665_, 1, v___x_3206_);
v___x_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
v_a_3188_ = v___x_3666_;
goto v___jp_3187_;
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_del_object(v___x_3654_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3668_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3661_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3661_);
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
lean_del_object(v___x_3654_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3676_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3659_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3659_);
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
lean_del_object(v___x_3654_);
lean_dec(v_val_3652_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3684_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3656_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3656_);
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
}
else
{
lean_object* v___x_3693_; 
lean_dec(v_a_3651_);
lean_inc_ref(v___x_3322_);
v___x_3693_ = l_Lean_Meta_matchNe_x3f(v___x_3322_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
if (lean_obj_tag(v_a_3694_) == 1)
{
lean_object* v_val_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3765_; 
v_val_3695_ = lean_ctor_get(v_a_3694_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_a_3694_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3697_ = v_a_3694_;
v_isShared_3698_ = v_isSharedCheck_3765_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_val_3695_);
lean_dec(v_a_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3765_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v_snd_3699_; lean_object* v_fst_3700_; lean_object* v_snd_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3764_; 
v_snd_3699_ = lean_ctor_get(v_val_3695_, 1);
lean_inc(v_snd_3699_);
lean_dec(v_val_3695_);
v_fst_3700_ = lean_ctor_get(v_snd_3699_, 0);
v_snd_3701_ = lean_ctor_get(v_snd_3699_, 1);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_snd_3699_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3703_ = v_snd_3699_;
v_isShared_3704_ = v_isSharedCheck_3764_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_snd_3701_);
lean_inc(v_fst_3700_);
lean_dec(v_snd_3699_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3764_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; 
lean_inc(v_fst_3700_);
v___x_3705_ = l_Lean_Meta_isExprDefEq(v_fst_3700_, v_snd_3701_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; uint8_t v___x_3707_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref_known(v___x_3705_, 1);
v___x_3707_ = lean_unbox(v_a_3706_);
lean_dec(v_a_3706_);
if (v___x_3707_ == 0)
{
lean_del_object(v___x_3703_);
lean_dec(v_fst_3700_);
lean_del_object(v___x_3697_);
v___y_3600_ = v___y_3646_;
v___y_3601_ = v___y_3647_;
v___y_3602_ = v___y_3648_;
v___y_3603_ = v___y_3649_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3708_; 
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
lean_inc(v_mvarId_3171_);
v___x_3708_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3710_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3710_ = l_Lean_Meta_mkEqRefl(v_fst_3700_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v___x_3712_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3713_ = l_Lean_Meta_mkAbsurd(v_a_3709_, v_a_3711_, v___x_3712_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___x_3715_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3714_, v___y_3647_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_dec_ref_known(v___x_3715_, 1);
v___x_3716_ = lean_box(v___x_3181_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3716_);
v___x_3718_ = v___x_3697_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3720_; 
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 1, v___x_3206_);
lean_ctor_set(v___x_3703_, 0, v___x_3718_);
v___x_3720_ = v___x_3703_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v___x_3206_);
v___x_3720_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
v_a_3188_ = v___x_3721_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_del_object(v___x_3703_);
lean_del_object(v___x_3697_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3724_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3715_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3715_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_del_object(v___x_3703_);
lean_del_object(v___x_3697_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3732_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3713_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3713_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec(v_a_3709_);
lean_del_object(v___x_3703_);
lean_del_object(v___x_3697_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3740_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3710_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3710_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_del_object(v___x_3703_);
lean_dec(v_fst_3700_);
lean_del_object(v___x_3697_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3748_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3708_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3708_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_del_object(v___x_3703_);
lean_dec(v_fst_3700_);
lean_del_object(v___x_3697_);
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3756_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3705_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3705_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3694_);
v___y_3600_ = v___y_3646_;
v___y_3601_ = v___y_3647_;
v___y_3602_ = v___y_3648_;
v___y_3603_ = v___y_3649_;
goto v___jp_3599_;
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3766_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3693_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3693_);
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
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_dec_ref(v___x_3322_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3774_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3650_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3650_);
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
}
else
{
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3196_ = v___x_3248_;
goto v___jp_3195_;
}
v___jp_3207_:
{
lean_object* v___x_3212_; 
lean_inc(v_mvarId_3171_);
v___x_3212_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3210_, v___y_3211_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref_known(v___x_3212_, 1);
v___x_3214_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3215_ = l_Lean_Meta_mkNoConfusion(v_a_3213_, v___x_3214_, v___y_3210_, v___y_3211_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3217_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3215_, 1);
v___x_3217_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3216_, v___y_3211_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
lean_dec_ref_known(v___x_3217_, 1);
v___x_3218_ = lean_box(v___x_3181_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3218_);
v___x_3220_ = v___x_3204_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v___x_3206_);
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
v_a_3188_ = v___x_3222_;
goto v___jp_3187_;
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_del_object(v___x_3204_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3224_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3217_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3217_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_del_object(v___x_3204_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3232_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3215_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3215_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3240_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3212_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3212_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
v___jp_3249_:
{
lean_object* v_searchFuel_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_searchFuel_3254_ = lean_ctor_get(v_config_3170_, 0);
v___x_3255_ = l_Lean_LocalDecl_fvarId(v_val_3202_);
lean_dec(v_val_3202_);
lean_inc(v_searchFuel_3254_);
lean_inc(v_mvarId_3171_);
v___x_3256_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3171_, v___x_3255_, v_searchFuel_3254_, v___y_3252_, v___y_3250_, v___y_3253_, v___y_3251_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; uint8_t v___x_3258_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3256_, 1);
v___x_3258_ = lean_unbox(v_a_3257_);
lean_dec(v_a_3257_);
if (v___x_3258_ == 0)
{
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3196_ = v___x_3248_;
goto v___jp_3195_;
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3259_ = lean_box(v___x_3181_);
v___x_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
v___x_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
lean_ctor_set(v___x_3261_, 1, v___x_3206_);
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
v_a_3188_ = v___x_3262_;
goto v___jp_3187_;
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3263_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3256_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3256_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
v___jp_3271_:
{
if (v___y_3276_ == 0)
{
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3196_ = v___x_3248_;
goto v___jp_3195_;
}
else
{
v___y_3250_ = v___y_3272_;
v___y_3251_ = v___y_3273_;
v___y_3252_ = v___y_3274_;
v___y_3253_ = v___y_3275_;
goto v___jp_3249_;
}
}
v___jp_3278_:
{
if (v___y_3283_ == 0)
{
v___y_3250_ = v___y_3279_;
v___y_3251_ = v___y_3280_;
v___y_3252_ = v___y_3281_;
v___y_3253_ = v___y_3282_;
goto v___jp_3249_;
}
else
{
v___y_3272_ = v___y_3279_;
v___y_3273_ = v___y_3280_;
v___y_3274_ = v___y_3281_;
v___y_3275_ = v___y_3282_;
v___y_3276_ = v___x_3277_;
goto v___jp_3271_;
}
}
v___jp_3284_:
{
if (v___y_3290_ == 0)
{
v___y_3272_ = v___y_3285_;
v___y_3273_ = v___y_3286_;
v___y_3274_ = v___y_3287_;
v___y_3275_ = v___y_3288_;
v___y_3276_ = v___x_3277_;
goto v___jp_3271_;
}
else
{
v___y_3279_ = v___y_3285_;
v___y_3280_ = v___y_3286_;
v___y_3281_ = v___y_3287_;
v___y_3282_ = v___y_3288_;
v___y_3283_ = v___y_3289_;
goto v___jp_3278_;
}
}
v___jp_3291_:
{
uint8_t v_emptyType_3298_; 
v_emptyType_3298_ = lean_ctor_get_uint8(v_config_3170_, sizeof(void*)*1 + 1);
if (v_emptyType_3298_ == 0)
{
v___y_3285_ = v___y_3295_;
v___y_3286_ = v___y_3297_;
v___y_3287_ = v___y_3294_;
v___y_3288_ = v___y_3296_;
v___y_3289_ = v___y_3293_;
v___y_3290_ = v___x_3277_;
goto v___jp_3284_;
}
else
{
if (v___y_3292_ == 0)
{
v___y_3279_ = v___y_3295_;
v___y_3280_ = v___y_3297_;
v___y_3281_ = v___y_3294_;
v___y_3282_ = v___y_3296_;
v___y_3283_ = v___y_3293_;
goto v___jp_3278_;
}
else
{
v___y_3285_ = v___y_3295_;
v___y_3286_ = v___y_3297_;
v___y_3287_ = v___y_3294_;
v___y_3288_ = v___y_3296_;
v___y_3289_ = v___y_3293_;
v___y_3290_ = v___x_3277_;
goto v___jp_3284_;
}
}
}
v___jp_3299_:
{
if (v___y_3306_ == 0)
{
v___y_3292_ = v___y_3301_;
v___y_3293_ = v___y_3305_;
v___y_3294_ = v___y_3304_;
v___y_3295_ = v___y_3303_;
v___y_3296_ = v___y_3300_;
v___y_3297_ = v___y_3302_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3307_; 
lean_inc(v_val_3202_);
lean_inc(v_mvarId_3171_);
v___x_3307_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3171_, v_val_3202_, v___y_3304_, v___y_3303_, v___y_3300_, v___y_3302_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; uint8_t v___x_3309_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v___x_3307_, 1);
v___x_3309_ = lean_unbox(v_a_3308_);
lean_dec(v_a_3308_);
if (v___x_3309_ == 0)
{
v___y_3292_ = v___y_3301_;
v___y_3293_ = v___y_3305_;
v___y_3294_ = v___y_3304_;
v___y_3295_ = v___y_3303_;
v___y_3296_ = v___y_3300_;
v___y_3297_ = v___y_3302_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec(v_val_3202_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3310_ = lean_box(v___x_3181_);
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
v___x_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v___x_3206_);
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
v_a_3188_ = v___x_3313_;
goto v___jp_3187_;
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3314_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3307_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3307_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3855_, lean_object* v_mvarId_3856_, lean_object* v_as_3857_, lean_object* v_sz_3858_, lean_object* v_i_3859_, lean_object* v_b_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
size_t v_sz_boxed_3866_; size_t v_i_boxed_3867_; lean_object* v_res_3868_; 
v_sz_boxed_3866_ = lean_unbox_usize(v_sz_3858_);
lean_dec(v_sz_3858_);
v_i_boxed_3867_ = lean_unbox_usize(v_i_3859_);
lean_dec(v_i_3859_);
v_res_3868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3855_, v_mvarId_3856_, v_as_3857_, v_sz_boxed_3866_, v_i_boxed_3867_, v_b_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec_ref(v_as_3857_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3869_, lean_object* v_mvarId_3870_, lean_object* v_as_3871_, size_t v_sz_3872_, size_t v_i_3873_, lean_object* v_b_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
uint8_t v___x_3880_; 
v___x_3880_ = lean_usize_dec_lt(v_i_3873_, v_sz_3872_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; 
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v___x_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3881_, 0, v_b_3874_);
return v___x_3881_;
}
else
{
lean_object* v_snd_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_4552_; 
v_snd_3882_ = lean_ctor_get(v_b_3874_, 1);
v_isSharedCheck_4552_ = !lean_is_exclusive(v_b_3874_);
if (v_isSharedCheck_4552_ == 0)
{
lean_object* v_unused_4553_; 
v_unused_4553_ = lean_ctor_get(v_b_3874_, 0);
lean_dec(v_unused_4553_);
v___x_3884_ = v_b_3874_;
v_isShared_3885_ = v_isSharedCheck_4552_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_snd_3882_);
lean_dec(v_b_3874_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_4552_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v_a_3887_; lean_object* v___x_3893_; lean_object* v_a_3895_; lean_object* v_a_3900_; 
v___x_3893_ = lean_box(0);
v_a_3900_ = lean_array_uget(v_as_3871_, v_i_3873_);
if (lean_obj_tag(v_a_3900_) == 0)
{
lean_del_object(v___x_3884_);
v_a_3895_ = v_snd_3882_;
goto v___jp_3894_;
}
else
{
lean_object* v_val_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_4551_; 
v_val_3901_ = lean_ctor_get(v_a_3900_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v_a_3900_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_3903_ = v_a_3900_;
v_isShared_3904_ = v_isSharedCheck_4551_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_val_3901_);
lean_dec(v_a_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_4551_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___x_3947_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; uint8_t v___y_3975_; uint8_t v___x_3976_; lean_object* v___y_3978_; lean_object* v___y_3979_; uint8_t v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; uint8_t v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; uint8_t v___y_3989_; uint8_t v___y_3991_; uint8_t v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; uint8_t v___y_4003_; uint8_t v___y_4004_; uint8_t v___y_4005_; 
v___x_3905_ = lean_box(0);
v___x_3947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3976_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3901_);
if (v___x_3976_ == 0)
{
lean_object* v___x_4021_; uint8_t v___y_4023_; uint8_t v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4032_; lean_object* v___y_4033_; uint8_t v___y_4034_; lean_object* v___y_4035_; uint8_t v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; uint8_t v___y_4039_; lean_object* v___y_4042_; lean_object* v___y_4043_; uint8_t v___y_4044_; lean_object* v___y_4045_; uint8_t v___y_4046_; lean_object* v___y_4047_; lean_object* v_a_4048_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; uint8_t v___y_4055_; uint8_t v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4103_; lean_object* v___y_4104_; uint8_t v___y_4105_; uint8_t v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4132_; lean_object* v___y_4133_; uint8_t v___y_4134_; uint8_t v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; uint8_t v___y_4138_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; uint8_t v___y_4143_; lean_object* v___y_4144_; uint8_t v___y_4145_; lean_object* v___y_4146_; uint8_t v___y_4147_; lean_object* v___y_4150_; lean_object* v___y_4151_; uint8_t v___y_4152_; uint8_t v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; uint8_t v___y_4156_; lean_object* v___y_4169_; lean_object* v___y_4170_; uint8_t v___y_4171_; uint8_t v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; uint8_t v___y_4175_; uint8_t v___y_4177_; uint8_t v_isHEq_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; uint8_t v___y_4192_; uint8_t v_isEq_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___x_4481_; 
v___x_4021_ = l_Lean_LocalDecl_type(v_val_3901_);
lean_inc_ref(v___x_4021_);
v___x_4481_ = l_Lean_Meta_matchNot_x3f(v___x_4021_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
if (lean_obj_tag(v_a_4482_) == 1)
{
lean_object* v_val_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4542_; 
v_val_4483_ = lean_ctor_get(v_a_4482_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v_a_4482_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4485_ = v_a_4482_;
v_isShared_4486_ = v_isSharedCheck_4542_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_val_4483_);
lean_dec(v_a_4482_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4542_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; 
v___x_4487_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4483_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4488_);
lean_dec_ref_known(v___x_4487_, 1);
if (lean_obj_tag(v_a_4488_) == 1)
{
lean_object* v_val_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4533_; 
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec_ref(v_config_3869_);
v_val_4489_ = lean_ctor_get(v_a_4488_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_a_4488_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4491_ = v_a_4488_;
v_isShared_4492_ = v_isSharedCheck_4533_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_val_4489_);
lean_dec(v_a_4488_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4533_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4493_; 
lean_inc(v_mvarId_3870_);
v___x_4493_ = l_Lean_MVarId_getType(v_mvarId_3870_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4494_);
lean_dec_ref_known(v___x_4493_, 1);
v___x_4495_ = l_Lean_LocalDecl_toExpr(v_val_3901_);
v___x_4496_ = l_Lean_mkFVar(v_val_4489_);
v___x_4497_ = l_Lean_Expr_app___override(v___x_4495_, v___x_4496_);
v___x_4498_ = l_Lean_Meta_mkFalseElim(v_a_4494_, v___x_4497_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4500_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref_known(v___x_4498_, 1);
v___x_4500_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3870_, v_a_4499_, v___y_3876_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v___x_4501_; lean_object* v___x_4503_; 
lean_dec_ref_known(v___x_4500_, 1);
v___x_4501_ = lean_box(v___x_3880_);
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 0, v___x_4501_);
v___x_4503_ = v___x_4491_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v___x_4504_; lean_object* v___x_4506_; 
v___x_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
lean_ctor_set(v___x_4504_, 1, v___x_3905_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set_tag(v___x_4485_, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4504_);
v___x_4506_ = v___x_4485_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
v_a_3887_ = v___x_4506_;
goto v___jp_3886_;
}
}
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_del_object(v___x_4491_);
lean_del_object(v___x_4485_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
v_a_4509_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4500_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4500_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_del_object(v___x_4491_);
lean_del_object(v___x_4485_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_4517_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4498_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4498_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
else
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4532_; 
lean_del_object(v___x_4491_);
lean_dec(v_val_4489_);
lean_del_object(v___x_4485_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_4525_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4527_ = v___x_4493_;
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4493_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
}
else
{
lean_dec(v_a_4488_);
lean_del_object(v___x_4485_);
v___y_4345_ = v___y_3875_;
v___y_4346_ = v___y_3876_;
v___y_4347_ = v___y_3877_;
v___y_4348_ = v___y_3878_;
goto v___jp_4344_;
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_del_object(v___x_4485_);
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4534_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4487_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4487_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
}
else
{
lean_dec(v_a_4482_);
v___y_4345_ = v___y_3875_;
v___y_4346_ = v___y_3876_;
v___y_4347_ = v___y_3877_;
v___y_4348_ = v___y_3878_;
goto v___jp_4344_;
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4543_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4481_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4481_);
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
v___jp_4022_:
{
uint8_t v_genDiseq_4029_; 
v_genDiseq_4029_ = lean_ctor_get_uint8(v_config_3869_, sizeof(void*)*1 + 2);
if (v_genDiseq_4029_ == 0)
{
lean_dec_ref(v___x_4021_);
v___y_3999_ = v___y_4028_;
v___y_4000_ = v___y_4027_;
v___y_4001_ = v___y_4026_;
v___y_4002_ = v___y_4025_;
v___y_4003_ = v___y_4023_;
v___y_4004_ = v___y_4024_;
v___y_4005_ = v___x_3976_;
goto v___jp_3998_;
}
else
{
uint8_t v___x_4030_; 
v___x_4030_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4021_);
v___y_3999_ = v___y_4028_;
v___y_4000_ = v___y_4027_;
v___y_4001_ = v___y_4026_;
v___y_4002_ = v___y_4025_;
v___y_4003_ = v___y_4023_;
v___y_4004_ = v___y_4024_;
v___y_4005_ = v___x_4030_;
goto v___jp_3998_;
}
}
v___jp_4031_:
{
if (v___y_4039_ == 0)
{
lean_dec_ref(v___y_4035_);
v___y_4023_ = v___y_4034_;
v___y_4024_ = v___y_4036_;
v___y_4025_ = v___y_4033_;
v___y_4026_ = v___y_4037_;
v___y_4027_ = v___y_4038_;
v___y_4028_ = v___y_4032_;
goto v___jp_4022_;
}
else
{
lean_object* v___x_4040_; 
lean_dec_ref(v___x_4021_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v___x_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4040_, 0, v___y_4035_);
return v___x_4040_;
}
}
v___jp_4041_:
{
uint8_t v___x_4049_; 
v___x_4049_ = l_Lean_Exception_isInterrupt(v_a_4048_);
if (v___x_4049_ == 0)
{
uint8_t v___x_4050_; 
lean_inc_ref(v_a_4048_);
v___x_4050_ = l_Lean_Exception_isRuntime(v_a_4048_);
v___y_4032_ = v___y_4042_;
v___y_4033_ = v___y_4043_;
v___y_4034_ = v___y_4044_;
v___y_4035_ = v_a_4048_;
v___y_4036_ = v___y_4046_;
v___y_4037_ = v___y_4045_;
v___y_4038_ = v___y_4047_;
v___y_4039_ = v___x_4050_;
goto v___jp_4031_;
}
else
{
v___y_4032_ = v___y_4042_;
v___y_4033_ = v___y_4043_;
v___y_4034_ = v___y_4044_;
v___y_4035_ = v_a_4048_;
v___y_4036_ = v___y_4046_;
v___y_4037_ = v___y_4045_;
v___y_4038_ = v___y_4047_;
v___y_4039_ = v___x_4049_;
goto v___jp_4031_;
}
}
v___jp_4051_:
{
if (lean_obj_tag(v___y_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; 
v_a_4060_ = lean_ctor_get(v___y_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v___y_4059_, 1);
v___x_4061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4062_ = l_Lean_Expr_isConstOf(v_a_4060_, v___x_4061_);
lean_dec(v_a_4060_);
if (v___x_4062_ == 0)
{
lean_dec_ref(v___y_4053_);
v___y_4023_ = v___y_4055_;
v___y_4024_ = v___y_4056_;
v___y_4025_ = v___y_4054_;
v___y_4026_ = v___y_4057_;
v___y_4027_ = v___y_4058_;
v___y_4028_ = v___y_4052_;
goto v___jp_4022_;
}
else
{
lean_object* v___x_4063_; 
lean_inc_ref(v___y_4053_);
v___x_4063_ = l_Lean_Meta_mkEqRefl(v___y_4053_, v___y_4054_, v___y_4057_, v___y_4058_, v___y_4052_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4065_; lean_object* v_dummy_4066_; lean_object* v_nargs_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4065_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4066_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_4067_ = l_Lean_Expr_getAppNumArgs(v___y_4053_);
lean_inc(v_nargs_4067_);
v___x_4068_ = lean_mk_array(v_nargs_4067_, v_dummy_4066_);
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4070_ = lean_nat_sub(v_nargs_4067_, v___x_4069_);
lean_dec(v_nargs_4067_);
v___x_4071_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_4053_, v___x_4068_, v___x_4070_);
v___x_4072_ = lean_array_push(v___x_4071_, v_a_4064_);
v___x_4073_ = l_Lean_mkAppN(v___x_4065_, v___x_4072_);
lean_dec_ref(v___x_4072_);
lean_inc(v_mvarId_3870_);
v___x_4074_ = l_Lean_MVarId_getType(v_mvarId_3870_, v___y_4054_, v___y_4057_, v___y_4058_, v___y_4052_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4074_, 1);
lean_inc(v_val_3901_);
v___x_4076_ = l_Lean_LocalDecl_toExpr(v_val_3901_);
v___x_4077_ = l_Lean_Meta_mkAbsurd(v_a_4075_, v___x_4076_, v___x_4073_, v___y_4054_, v___y_4057_, v___y_4058_, v___y_4052_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4097_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4097_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4097_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; 
lean_inc(v_mvarId_3870_);
v___x_4082_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3870_, v_a_4078_, v___y_4057_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4094_; 
lean_dec_ref(v___x_4021_);
lean_dec(v_val_3901_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4094_ == 0)
{
lean_object* v_unused_4095_; 
v_unused_4095_ = lean_ctor_get(v___x_4082_, 0);
lean_dec(v_unused_4095_);
v___x_4084_ = v___x_4082_;
v_isShared_4085_ = v_isSharedCheck_4094_;
goto v_resetjp_4083_;
}
else
{
lean_dec(v___x_4082_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4094_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4086_ = lean_box(v___x_3880_);
if (v_isShared_4085_ == 0)
{
lean_ctor_set_tag(v___x_4084_, 1);
lean_ctor_set(v___x_4084_, 0, v___x_4086_);
v___x_4088_ = v___x_4084_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4089_; lean_object* v___x_4091_; 
v___x_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set(v___x_4089_, 1, v___x_3905_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4089_);
v___x_4091_ = v___x_4080_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4089_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
v_a_3887_ = v___x_4091_;
goto v___jp_3886_;
}
}
}
}
else
{
lean_object* v_a_4096_; 
lean_del_object(v___x_4080_);
v_a_4096_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4082_, 1);
v___y_4042_ = v___y_4052_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4055_;
v___y_4045_ = v___y_4057_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4058_;
v_a_4048_ = v_a_4096_;
goto v___jp_4041_;
}
}
}
else
{
lean_object* v_a_4098_; 
v_a_4098_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4077_, 1);
v___y_4042_ = v___y_4052_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4055_;
v___y_4045_ = v___y_4057_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4058_;
v_a_4048_ = v_a_4098_;
goto v___jp_4041_;
}
}
else
{
lean_object* v_a_4099_; 
lean_dec_ref(v___x_4073_);
v_a_4099_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4074_, 1);
v___y_4042_ = v___y_4052_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4055_;
v___y_4045_ = v___y_4057_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4058_;
v_a_4048_ = v_a_4099_;
goto v___jp_4041_;
}
}
else
{
lean_object* v_a_4100_; 
lean_dec_ref(v___y_4053_);
v_a_4100_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v___x_4063_, 1);
v___y_4042_ = v___y_4052_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4055_;
v___y_4045_ = v___y_4057_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4058_;
v_a_4048_ = v_a_4100_;
goto v___jp_4041_;
}
}
}
else
{
lean_object* v_a_4101_; 
lean_dec_ref(v___y_4053_);
v_a_4101_ = lean_ctor_get(v___y_4059_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___y_4059_, 1);
v___y_4042_ = v___y_4052_;
v___y_4043_ = v___y_4054_;
v___y_4044_ = v___y_4055_;
v___y_4045_ = v___y_4057_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4058_;
v_a_4048_ = v_a_4101_;
goto v___jp_4041_;
}
}
v___jp_4102_:
{
lean_object* v___x_4109_; 
lean_inc_ref(v___x_4021_);
v___x_4109_ = l_Lean_Meta_mkDecide(v___x_4021_, v___y_4104_, v___y_4107_, v___y_4108_, v___y_4103_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4111_; uint8_t v_transparency_4112_; uint8_t v___x_4113_; uint8_t v___x_4114_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
v___x_4111_ = l_Lean_Meta_Context_config(v___y_4104_);
v_transparency_4112_ = lean_ctor_get_uint8(v___x_4111_, 9);
lean_dec_ref(v___x_4111_);
v___x_4113_ = 1;
v___x_4114_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4112_, v___x_4113_);
if (v___x_4114_ == 0)
{
lean_object* v_keyedConfig_4115_; uint8_t v_trackZetaDelta_4116_; lean_object* v_zetaDeltaSet_4117_; lean_object* v_lctx_4118_; lean_object* v_localInstances_4119_; lean_object* v_defEqCtx_x3f_4120_; lean_object* v_synthPendingDepth_4121_; lean_object* v_customCanUnfoldPredicate_x3f_4122_; uint8_t v_univApprox_4123_; uint8_t v_inTypeClassResolution_4124_; uint8_t v_cacheInferType_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v_keyedConfig_4115_ = lean_ctor_get(v___y_4104_, 0);
v_trackZetaDelta_4116_ = lean_ctor_get_uint8(v___y_4104_, sizeof(void*)*7);
v_zetaDeltaSet_4117_ = lean_ctor_get(v___y_4104_, 1);
v_lctx_4118_ = lean_ctor_get(v___y_4104_, 2);
v_localInstances_4119_ = lean_ctor_get(v___y_4104_, 3);
v_defEqCtx_x3f_4120_ = lean_ctor_get(v___y_4104_, 4);
v_synthPendingDepth_4121_ = lean_ctor_get(v___y_4104_, 5);
v_customCanUnfoldPredicate_x3f_4122_ = lean_ctor_get(v___y_4104_, 6);
v_univApprox_4123_ = lean_ctor_get_uint8(v___y_4104_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4124_ = lean_ctor_get_uint8(v___y_4104_, sizeof(void*)*7 + 2);
v_cacheInferType_4125_ = lean_ctor_get_uint8(v___y_4104_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4115_);
v___x_4126_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4113_, v_keyedConfig_4115_);
lean_inc(v_customCanUnfoldPredicate_x3f_4122_);
lean_inc(v_synthPendingDepth_4121_);
lean_inc(v_defEqCtx_x3f_4120_);
lean_inc_ref(v_localInstances_4119_);
lean_inc_ref(v_lctx_4118_);
lean_inc(v_zetaDeltaSet_4117_);
v___x_4127_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
lean_ctor_set(v___x_4127_, 1, v_zetaDeltaSet_4117_);
lean_ctor_set(v___x_4127_, 2, v_lctx_4118_);
lean_ctor_set(v___x_4127_, 3, v_localInstances_4119_);
lean_ctor_set(v___x_4127_, 4, v_defEqCtx_x3f_4120_);
lean_ctor_set(v___x_4127_, 5, v_synthPendingDepth_4121_);
lean_ctor_set(v___x_4127_, 6, v_customCanUnfoldPredicate_x3f_4122_);
lean_ctor_set_uint8(v___x_4127_, sizeof(void*)*7, v_trackZetaDelta_4116_);
lean_ctor_set_uint8(v___x_4127_, sizeof(void*)*7 + 1, v_univApprox_4123_);
lean_ctor_set_uint8(v___x_4127_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4124_);
lean_ctor_set_uint8(v___x_4127_, sizeof(void*)*7 + 3, v_cacheInferType_4125_);
lean_inc(v___y_4103_);
lean_inc_ref(v___y_4108_);
lean_inc(v___y_4107_);
lean_inc(v_a_4110_);
v___x_4128_ = lean_whnf(v_a_4110_, v___x_4127_, v___y_4107_, v___y_4108_, v___y_4103_);
v___y_4052_ = v___y_4103_;
v___y_4053_ = v_a_4110_;
v___y_4054_ = v___y_4104_;
v___y_4055_ = v___y_4105_;
v___y_4056_ = v___y_4106_;
v___y_4057_ = v___y_4107_;
v___y_4058_ = v___y_4108_;
v___y_4059_ = v___x_4128_;
goto v___jp_4051_;
}
else
{
lean_object* v___x_4129_; 
lean_inc(v___y_4103_);
lean_inc_ref(v___y_4108_);
lean_inc(v___y_4107_);
lean_inc_ref(v___y_4104_);
lean_inc(v_a_4110_);
v___x_4129_ = lean_whnf(v_a_4110_, v___y_4104_, v___y_4107_, v___y_4108_, v___y_4103_);
v___y_4052_ = v___y_4103_;
v___y_4053_ = v_a_4110_;
v___y_4054_ = v___y_4104_;
v___y_4055_ = v___y_4105_;
v___y_4056_ = v___y_4106_;
v___y_4057_ = v___y_4107_;
v___y_4058_ = v___y_4108_;
v___y_4059_ = v___x_4129_;
goto v___jp_4051_;
}
}
else
{
lean_object* v_a_4130_; 
v_a_4130_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___x_4109_, 1);
v___y_4042_ = v___y_4103_;
v___y_4043_ = v___y_4104_;
v___y_4044_ = v___y_4105_;
v___y_4045_ = v___y_4107_;
v___y_4046_ = v___y_4106_;
v___y_4047_ = v___y_4108_;
v_a_4048_ = v_a_4130_;
goto v___jp_4041_;
}
}
v___jp_4131_:
{
if (v___y_4138_ == 0)
{
v___y_4023_ = v___y_4134_;
v___y_4024_ = v___y_4135_;
v___y_4025_ = v___y_4133_;
v___y_4026_ = v___y_4136_;
v___y_4027_ = v___y_4137_;
v___y_4028_ = v___y_4132_;
goto v___jp_4022_;
}
else
{
v___y_4103_ = v___y_4132_;
v___y_4104_ = v___y_4133_;
v___y_4105_ = v___y_4134_;
v___y_4106_ = v___y_4135_;
v___y_4107_ = v___y_4136_;
v___y_4108_ = v___y_4137_;
goto v___jp_4102_;
}
}
v___jp_4139_:
{
if (v___y_4147_ == 0)
{
lean_dec_ref(v___y_4141_);
v___y_4132_ = v___y_4140_;
v___y_4133_ = v___y_4142_;
v___y_4134_ = v___y_4143_;
v___y_4135_ = v___y_4145_;
v___y_4136_ = v___y_4144_;
v___y_4137_ = v___y_4146_;
v___y_4138_ = v___x_3976_;
goto v___jp_4131_;
}
else
{
uint8_t v___x_4148_; 
v___x_4148_ = l_Lean_Expr_hasFVar(v___y_4141_);
lean_dec_ref(v___y_4141_);
if (v___x_4148_ == 0)
{
v___y_4103_ = v___y_4140_;
v___y_4104_ = v___y_4142_;
v___y_4105_ = v___y_4143_;
v___y_4106_ = v___y_4145_;
v___y_4107_ = v___y_4144_;
v___y_4108_ = v___y_4146_;
goto v___jp_4102_;
}
else
{
v___y_4132_ = v___y_4140_;
v___y_4133_ = v___y_4142_;
v___y_4134_ = v___y_4143_;
v___y_4135_ = v___y_4145_;
v___y_4136_ = v___y_4144_;
v___y_4137_ = v___y_4146_;
v___y_4138_ = v___x_3976_;
goto v___jp_4131_;
}
}
}
v___jp_4149_:
{
lean_object* v___x_4157_; 
lean_inc_ref(v___x_4021_);
v___x_4157_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4021_, v___y_4154_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; uint8_t v___x_4159_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4157_, 1);
v___x_4159_ = l_Lean_Expr_hasMVar(v_a_4158_);
if (v___x_4159_ == 0)
{
v___y_4140_ = v___y_4150_;
v___y_4141_ = v_a_4158_;
v___y_4142_ = v___y_4151_;
v___y_4143_ = v___y_4152_;
v___y_4144_ = v___y_4154_;
v___y_4145_ = v___y_4153_;
v___y_4146_ = v___y_4155_;
v___y_4147_ = v___y_4156_;
goto v___jp_4139_;
}
else
{
v___y_4140_ = v___y_4150_;
v___y_4141_ = v_a_4158_;
v___y_4142_ = v___y_4151_;
v___y_4143_ = v___y_4152_;
v___y_4144_ = v___y_4154_;
v___y_4145_ = v___y_4153_;
v___y_4146_ = v___y_4155_;
v___y_4147_ = v___x_3976_;
goto v___jp_4139_;
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec_ref(v___x_4021_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4160_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4157_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4157_);
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
v___jp_4168_:
{
if (v___y_4175_ == 0)
{
v___y_4023_ = v___y_4171_;
v___y_4024_ = v___y_4172_;
v___y_4025_ = v___y_4170_;
v___y_4026_ = v___y_4173_;
v___y_4027_ = v___y_4174_;
v___y_4028_ = v___y_4169_;
goto v___jp_4022_;
}
else
{
v___y_4150_ = v___y_4169_;
v___y_4151_ = v___y_4170_;
v___y_4152_ = v___y_4171_;
v___y_4153_ = v___y_4172_;
v___y_4154_ = v___y_4173_;
v___y_4155_ = v___y_4174_;
v___y_4156_ = v___y_4175_;
goto v___jp_4149_;
}
}
v___jp_4176_:
{
uint8_t v_useDecide_4183_; 
v_useDecide_4183_ = lean_ctor_get_uint8(v_config_3869_, sizeof(void*)*1);
if (v_useDecide_4183_ == 0)
{
v___y_4169_ = v___y_4182_;
v___y_4170_ = v___y_4179_;
v___y_4171_ = v_isHEq_4178_;
v___y_4172_ = v___y_4177_;
v___y_4173_ = v___y_4180_;
v___y_4174_ = v___y_4181_;
v___y_4175_ = v___x_3976_;
goto v___jp_4168_;
}
else
{
uint8_t v___x_4184_; 
v___x_4184_ = l_Lean_Expr_hasFVar(v___x_4021_);
if (v___x_4184_ == 0)
{
v___y_4150_ = v___y_4182_;
v___y_4151_ = v___y_4179_;
v___y_4152_ = v_isHEq_4178_;
v___y_4153_ = v___y_4177_;
v___y_4154_ = v___y_4180_;
v___y_4155_ = v___y_4181_;
v___y_4156_ = v_useDecide_4183_;
goto v___jp_4149_;
}
else
{
v___y_4169_ = v___y_4182_;
v___y_4170_ = v___y_4179_;
v___y_4171_ = v_isHEq_4178_;
v___y_4172_ = v___y_4177_;
v___y_4173_ = v___y_4180_;
v___y_4174_ = v___y_4181_;
v___y_4175_ = v___x_3976_;
goto v___jp_4168_;
}
}
}
v___jp_4185_:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_Meta_isExprDefEq(v___y_4191_, v___y_4190_, v___y_4189_, v___y_4188_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; uint8_t v___x_4195_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
lean_dec_ref_known(v___x_4193_, 1);
v___x_4195_ = lean_unbox(v_a_4194_);
lean_dec(v_a_4194_);
if (v___x_4195_ == 0)
{
v___y_4177_ = v___y_4192_;
v_isHEq_4178_ = v___x_3880_;
v___y_4179_ = v___y_4189_;
v___y_4180_ = v___y_4188_;
v___y_4181_ = v___y_4186_;
v___y_4182_ = v___y_4187_;
goto v___jp_4176_;
}
else
{
lean_object* v___x_4196_; 
lean_dec_ref(v___x_4021_);
lean_dec_ref(v_config_3869_);
lean_inc(v_mvarId_3870_);
v___x_4196_ = l_Lean_MVarId_getType(v_mvarId_3870_, v___y_4189_, v___y_4188_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___x_4198_ = l_Lean_LocalDecl_toExpr(v_val_3901_);
v___x_4199_ = l_Lean_Meta_mkEqOfHEq(v___x_4198_, v___x_3880_, v___y_4189_, v___y_4188_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = l_Lean_Meta_mkNoConfusion(v_a_4197_, v_a_4200_, v___y_4189_, v___y_4188_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4203_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
lean_dec_ref_known(v___x_4201_, 1);
v___x_4203_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3870_, v_a_4202_, v___y_4188_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
lean_dec_ref_known(v___x_4203_, 1);
v___x_4204_ = lean_box(v___x_3880_);
v___x_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
v___x_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
lean_ctor_set(v___x_4206_, 1, v___x_3905_);
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
v_a_3887_ = v___x_4207_;
goto v___jp_3886_;
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
v_a_4208_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4203_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4203_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_4216_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4201_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4201_);
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
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec(v_a_4197_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_4224_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4199_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4199_);
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
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
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
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec_ref(v___x_4021_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4240_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4193_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4193_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
v___jp_4248_:
{
lean_object* v___x_4254_; 
lean_inc_ref(v___x_4021_);
v___x_4254_ = l_Lean_Meta_matchHEq_x3f(v___x_4021_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
lean_dec_ref_known(v___x_4254_, 1);
if (lean_obj_tag(v_a_4255_) == 1)
{
lean_object* v_val_4256_; lean_object* v_snd_4257_; lean_object* v_snd_4258_; lean_object* v_fst_4259_; lean_object* v_fst_4260_; lean_object* v_fst_4261_; lean_object* v_snd_4262_; lean_object* v___x_4263_; 
v_val_4256_ = lean_ctor_get(v_a_4255_, 0);
lean_inc(v_val_4256_);
lean_dec_ref_known(v_a_4255_, 1);
v_snd_4257_ = lean_ctor_get(v_val_4256_, 1);
lean_inc(v_snd_4257_);
v_snd_4258_ = lean_ctor_get(v_snd_4257_, 1);
lean_inc(v_snd_4258_);
v_fst_4259_ = lean_ctor_get(v_val_4256_, 0);
lean_inc(v_fst_4259_);
lean_dec(v_val_4256_);
v_fst_4260_ = lean_ctor_get(v_snd_4257_, 0);
lean_inc(v_fst_4260_);
lean_dec(v_snd_4257_);
v_fst_4261_ = lean_ctor_get(v_snd_4258_, 0);
lean_inc(v_fst_4261_);
v_snd_4262_ = lean_ctor_get(v_snd_4258_, 1);
lean_inc(v_snd_4262_);
lean_dec(v_snd_4258_);
v___x_4263_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4260_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
lean_dec_ref_known(v___x_4263_, 1);
if (lean_obj_tag(v_a_4264_) == 1)
{
lean_object* v_val_4265_; lean_object* v___x_4266_; 
v_val_4265_ = lean_ctor_get(v_a_4264_, 0);
lean_inc(v_val_4265_);
lean_dec_ref_known(v_a_4264_, 1);
v___x_4266_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4262_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
if (lean_obj_tag(v_a_4267_) == 1)
{
lean_object* v_toConstantVal_4268_; lean_object* v_val_4269_; lean_object* v_toConstantVal_4270_; lean_object* v_name_4271_; lean_object* v_name_4272_; uint8_t v___x_4273_; 
v_toConstantVal_4268_ = lean_ctor_get(v_val_4265_, 0);
lean_inc_ref(v_toConstantVal_4268_);
lean_dec(v_val_4265_);
v_val_4269_ = lean_ctor_get(v_a_4267_, 0);
lean_inc(v_val_4269_);
lean_dec_ref_known(v_a_4267_, 1);
v_toConstantVal_4270_ = lean_ctor_get(v_val_4269_, 0);
lean_inc_ref(v_toConstantVal_4270_);
lean_dec(v_val_4269_);
v_name_4271_ = lean_ctor_get(v_toConstantVal_4268_, 0);
lean_inc(v_name_4271_);
lean_dec_ref(v_toConstantVal_4268_);
v_name_4272_ = lean_ctor_get(v_toConstantVal_4270_, 0);
lean_inc(v_name_4272_);
lean_dec_ref(v_toConstantVal_4270_);
v___x_4273_ = lean_name_eq(v_name_4271_, v_name_4272_);
lean_dec(v_name_4272_);
lean_dec(v_name_4271_);
if (v___x_4273_ == 0)
{
v___y_4186_ = v___y_4252_;
v___y_4187_ = v___y_4253_;
v___y_4188_ = v___y_4251_;
v___y_4189_ = v___y_4250_;
v___y_4190_ = v_fst_4261_;
v___y_4191_ = v_fst_4259_;
v___y_4192_ = v_isEq_4249_;
goto v___jp_4185_;
}
else
{
if (v___x_3976_ == 0)
{
lean_dec(v_fst_4261_);
lean_dec(v_fst_4259_);
v___y_4177_ = v_isEq_4249_;
v_isHEq_4178_ = v___x_3880_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
v___y_4181_ = v___y_4252_;
v___y_4182_ = v___y_4253_;
goto v___jp_4176_;
}
else
{
v___y_4186_ = v___y_4252_;
v___y_4187_ = v___y_4253_;
v___y_4188_ = v___y_4251_;
v___y_4189_ = v___y_4250_;
v___y_4190_ = v_fst_4261_;
v___y_4191_ = v_fst_4259_;
v___y_4192_ = v_isEq_4249_;
goto v___jp_4185_;
}
}
}
else
{
lean_dec(v_a_4267_);
lean_dec(v_val_4265_);
lean_dec(v_fst_4261_);
lean_dec(v_fst_4259_);
v___y_4177_ = v_isEq_4249_;
v_isHEq_4178_ = v___x_3880_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
v___y_4181_ = v___y_4252_;
v___y_4182_ = v___y_4253_;
goto v___jp_4176_;
}
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
lean_dec(v_val_4265_);
lean_dec(v_fst_4261_);
lean_dec(v_fst_4259_);
lean_dec_ref(v___x_4021_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4274_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4266_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4266_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
else
{
lean_dec(v_a_4264_);
lean_dec(v_snd_4262_);
lean_dec(v_fst_4261_);
lean_dec(v_fst_4259_);
v___y_4177_ = v_isEq_4249_;
v_isHEq_4178_ = v___x_3880_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
v___y_4181_ = v___y_4252_;
v___y_4182_ = v___y_4253_;
goto v___jp_4176_;
}
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
lean_dec(v_snd_4262_);
lean_dec(v_fst_4261_);
lean_dec(v_fst_4259_);
lean_dec_ref(v___x_4021_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4282_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4263_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4263_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
else
{
lean_dec(v_a_4255_);
v___y_4177_ = v_isEq_4249_;
v_isHEq_4178_ = v___x_3976_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
v___y_4181_ = v___y_4252_;
v___y_4182_ = v___y_4253_;
goto v___jp_4176_;
}
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
lean_dec_ref(v___x_4021_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4290_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4254_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4254_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
v___jp_4298_:
{
lean_object* v___x_4303_; 
lean_inc_ref(v___x_4021_);
v___x_4303_ = l_Lean_Meta_matchEq_x3f(v___x_4021_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___x_4303_, 1);
if (lean_obj_tag(v_a_4304_) == 1)
{
lean_object* v_val_4305_; lean_object* v_snd_4306_; lean_object* v_fst_4307_; lean_object* v_snd_4308_; lean_object* v___x_4309_; 
v_val_4305_ = lean_ctor_get(v_a_4304_, 0);
lean_inc(v_val_4305_);
lean_dec_ref_known(v_a_4304_, 1);
v_snd_4306_ = lean_ctor_get(v_val_4305_, 1);
lean_inc(v_snd_4306_);
lean_dec(v_val_4305_);
v_fst_4307_ = lean_ctor_get(v_snd_4306_, 0);
lean_inc(v_fst_4307_);
v_snd_4308_ = lean_ctor_get(v_snd_4306_, 1);
lean_inc(v_snd_4308_);
lean_dec(v_snd_4306_);
v___x_4309_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4307_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4309_, 1);
if (lean_obj_tag(v_a_4310_) == 1)
{
lean_object* v_val_4311_; lean_object* v___x_4312_; 
v_val_4311_ = lean_ctor_get(v_a_4310_, 0);
lean_inc(v_val_4311_);
lean_dec_ref_known(v_a_4310_, 1);
v___x_4312_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4308_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
if (lean_obj_tag(v_a_4313_) == 1)
{
lean_object* v_toConstantVal_4314_; lean_object* v_val_4315_; lean_object* v_toConstantVal_4316_; lean_object* v_name_4317_; lean_object* v_name_4318_; uint8_t v___x_4319_; 
v_toConstantVal_4314_ = lean_ctor_get(v_val_4311_, 0);
lean_inc_ref(v_toConstantVal_4314_);
lean_dec(v_val_4311_);
v_val_4315_ = lean_ctor_get(v_a_4313_, 0);
lean_inc(v_val_4315_);
lean_dec_ref_known(v_a_4313_, 1);
v_toConstantVal_4316_ = lean_ctor_get(v_val_4315_, 0);
lean_inc_ref(v_toConstantVal_4316_);
lean_dec(v_val_4315_);
v_name_4317_ = lean_ctor_get(v_toConstantVal_4314_, 0);
lean_inc(v_name_4317_);
lean_dec_ref(v_toConstantVal_4314_);
v_name_4318_ = lean_ctor_get(v_toConstantVal_4316_, 0);
lean_inc(v_name_4318_);
lean_dec_ref(v_toConstantVal_4316_);
v___x_4319_ = lean_name_eq(v_name_4317_, v_name_4318_);
lean_dec(v_name_4318_);
lean_dec(v_name_4317_);
if (v___x_4319_ == 0)
{
lean_dec_ref(v___x_4021_);
lean_dec_ref(v_config_3869_);
v___y_3907_ = v___y_4301_;
v___y_3908_ = v___y_4299_;
v___y_3909_ = v___y_4300_;
v___y_3910_ = v___y_4302_;
goto v___jp_3906_;
}
else
{
if (v___x_3976_ == 0)
{
lean_del_object(v___x_3903_);
v_isEq_4249_ = v___x_3880_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
v___y_4252_ = v___y_4301_;
v___y_4253_ = v___y_4302_;
goto v___jp_4248_;
}
else
{
lean_dec_ref(v___x_4021_);
lean_dec_ref(v_config_3869_);
v___y_3907_ = v___y_4301_;
v___y_3908_ = v___y_4299_;
v___y_3909_ = v___y_4300_;
v___y_3910_ = v___y_4302_;
goto v___jp_3906_;
}
}
}
else
{
lean_dec(v_a_4313_);
lean_dec(v_val_4311_);
lean_del_object(v___x_3903_);
v_isEq_4249_ = v___x_3880_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
v___y_4252_ = v___y_4301_;
v___y_4253_ = v___y_4302_;
goto v___jp_4248_;
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v_val_4311_);
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4320_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4312_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4312_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
else
{
lean_dec(v_a_4310_);
lean_dec(v_snd_4308_);
lean_del_object(v___x_3903_);
v_isEq_4249_ = v___x_3880_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
v___y_4252_ = v___y_4301_;
v___y_4253_ = v___y_4302_;
goto v___jp_4248_;
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_snd_4308_);
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4328_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4309_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4309_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
else
{
lean_dec(v_a_4304_);
lean_del_object(v___x_3903_);
v_isEq_4249_ = v___x_3976_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
v___y_4252_ = v___y_4301_;
v___y_4253_ = v___y_4302_;
goto v___jp_4248_;
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4336_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4303_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4303_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
v___jp_4344_:
{
lean_object* v___x_4349_; 
lean_inc_ref(v___x_4021_);
v___x_4349_ = l_Lean_refutableHasNotBit_x3f(v___x_4021_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
if (lean_obj_tag(v_a_4350_) == 1)
{
lean_object* v_val_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4391_; 
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec_ref(v_config_3869_);
v_val_4351_ = lean_ctor_get(v_a_4350_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v_a_4350_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4353_ = v_a_4350_;
v_isShared_4354_ = v_isSharedCheck_4391_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_val_4351_);
lean_dec(v_a_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4391_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4355_; 
lean_inc(v_mvarId_3870_);
v___x_4355_ = l_Lean_MVarId_getType(v_mvarId_3870_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v___x_4357_ = l_Lean_LocalDecl_toExpr(v_val_3901_);
v___x_4358_ = l_Lean_Meta_mkAbsurd(v_a_4356_, v_val_4351_, v___x_4357_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4360_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v___x_4360_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3870_, v_a_4359_, v___y_4346_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v___x_4361_; lean_object* v___x_4363_; 
lean_dec_ref_known(v___x_4360_, 1);
v___x_4361_ = lean_box(v___x_3880_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4361_);
v___x_4363_ = v___x_4353_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4361_);
v___x_4363_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
lean_ctor_set(v___x_4364_, 1, v___x_3905_);
v___x_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
v_a_3887_ = v___x_4365_;
goto v___jp_3886_;
}
}
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
lean_del_object(v___x_4353_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
v_a_4367_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4360_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4360_);
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
lean_del_object(v___x_4353_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_4375_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4358_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4358_);
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
lean_del_object(v___x_4353_);
lean_dec(v_val_4351_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_4383_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4355_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4355_);
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
}
else
{
lean_object* v___x_4392_; 
lean_dec(v_a_4350_);
lean_inc_ref(v___x_4021_);
v___x_4392_ = l_Lean_Meta_matchNe_x3f(v___x_4021_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4393_);
lean_dec_ref_known(v___x_4392_, 1);
if (lean_obj_tag(v_a_4393_) == 1)
{
lean_object* v_val_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4464_; 
v_val_4394_ = lean_ctor_get(v_a_4393_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_a_4393_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4396_ = v_a_4393_;
v_isShared_4397_ = v_isSharedCheck_4464_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_val_4394_);
lean_dec(v_a_4393_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4464_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v_snd_4398_; lean_object* v_fst_4399_; lean_object* v_snd_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4463_; 
v_snd_4398_ = lean_ctor_get(v_val_4394_, 1);
lean_inc(v_snd_4398_);
lean_dec(v_val_4394_);
v_fst_4399_ = lean_ctor_get(v_snd_4398_, 0);
v_snd_4400_ = lean_ctor_get(v_snd_4398_, 1);
v_isSharedCheck_4463_ = !lean_is_exclusive(v_snd_4398_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4402_ = v_snd_4398_;
v_isShared_4403_ = v_isSharedCheck_4463_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_snd_4400_);
lean_inc(v_fst_4399_);
lean_dec(v_snd_4398_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4463_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; 
lean_inc(v_fst_4399_);
v___x_4404_ = l_Lean_Meta_isExprDefEq(v_fst_4399_, v_snd_4400_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; uint8_t v___x_4406_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4404_, 1);
v___x_4406_ = lean_unbox(v_a_4405_);
lean_dec(v_a_4405_);
if (v___x_4406_ == 0)
{
lean_del_object(v___x_4402_);
lean_dec(v_fst_4399_);
lean_del_object(v___x_4396_);
v___y_4299_ = v___y_4345_;
v___y_4300_ = v___y_4346_;
v___y_4301_ = v___y_4347_;
v___y_4302_ = v___y_4348_;
goto v___jp_4298_;
}
else
{
lean_object* v___x_4407_; 
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec_ref(v_config_3869_);
lean_inc(v_mvarId_3870_);
v___x_4407_ = l_Lean_MVarId_getType(v_mvarId_3870_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4409_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref_known(v___x_4407_, 1);
v___x_4409_ = l_Lean_Meta_mkEqRefl(v_fst_4399_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = l_Lean_LocalDecl_toExpr(v_val_3901_);
v___x_4412_ = l_Lean_Meta_mkAbsurd(v_a_4408_, v_a_4410_, v___x_4411_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4414_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v___x_4414_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3870_, v_a_4413_, v___y_4346_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v___x_4415_; lean_object* v___x_4417_; 
lean_dec_ref_known(v___x_4414_, 1);
v___x_4415_ = lean_box(v___x_3880_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4415_);
v___x_4417_ = v___x_4396_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4415_);
v___x_4417_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
lean_object* v___x_4419_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 1, v___x_3905_);
lean_ctor_set(v___x_4402_, 0, v___x_4417_);
v___x_4419_ = v___x_4402_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4417_);
lean_ctor_set(v_reuseFailAlloc_4421_, 1, v___x_3905_);
v___x_4419_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
v_a_3887_ = v___x_4420_;
goto v___jp_3886_;
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_del_object(v___x_4402_);
lean_del_object(v___x_4396_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
v_a_4423_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4414_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4414_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_del_object(v___x_4402_);
lean_del_object(v___x_4396_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_4431_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4412_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4412_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_dec(v_a_4408_);
lean_del_object(v___x_4402_);
lean_del_object(v___x_4396_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_4439_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4409_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4409_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_del_object(v___x_4402_);
lean_dec(v_fst_4399_);
lean_del_object(v___x_4396_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_4447_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4407_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4407_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_del_object(v___x_4402_);
lean_dec(v_fst_4399_);
lean_del_object(v___x_4396_);
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4455_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4404_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4404_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4393_);
v___y_4299_ = v___y_4345_;
v___y_4300_ = v___y_4346_;
v___y_4301_ = v___y_4347_;
v___y_4302_ = v___y_4348_;
goto v___jp_4298_;
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4465_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4392_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4392_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4473_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4349_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4349_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
else
{
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
v_a_3895_ = v___x_3947_;
goto v___jp_3894_;
}
v___jp_3906_:
{
lean_object* v___x_3911_; 
lean_inc(v_mvarId_3870_);
v___x_3911_ = l_Lean_MVarId_getType(v_mvarId_3870_, v___y_3908_, v___y_3909_, v___y_3907_, v___y_3910_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = l_Lean_LocalDecl_toExpr(v_val_3901_);
v___x_3914_ = l_Lean_Meta_mkNoConfusion(v_a_3912_, v___x_3913_, v___y_3908_, v___y_3909_, v___y_3907_, v___y_3910_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v___x_3916_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3870_, v_a_3915_, v___y_3909_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
lean_dec_ref_known(v___x_3916_, 1);
v___x_3917_ = lean_box(v___x_3880_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 0, v___x_3917_);
v___x_3919_ = v___x_3903_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
lean_ctor_set(v___x_3920_, 1, v___x_3905_);
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
v_a_3887_ = v___x_3921_;
goto v___jp_3886_;
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_del_object(v___x_3903_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
v_a_3923_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3916_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3916_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_del_object(v___x_3903_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_3931_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3914_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3914_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_del_object(v___x_3903_);
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
v_a_3939_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3911_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3911_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
v___jp_3948_:
{
lean_object* v_searchFuel_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_searchFuel_3953_ = lean_ctor_get(v_config_3869_, 0);
v___x_3954_ = l_Lean_LocalDecl_fvarId(v_val_3901_);
lean_dec(v_val_3901_);
lean_inc(v_searchFuel_3953_);
lean_inc(v_mvarId_3870_);
v___x_3955_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3870_, v___x_3954_, v_searchFuel_3953_, v___y_3952_, v___y_3951_, v___y_3950_, v___y_3949_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; uint8_t v___x_3957_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref_known(v___x_3955_, 1);
v___x_3957_ = lean_unbox(v_a_3956_);
lean_dec(v_a_3956_);
if (v___x_3957_ == 0)
{
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
v_a_3895_ = v___x_3947_;
goto v___jp_3894_;
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v___x_3958_ = lean_box(v___x_3880_);
v___x_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
v___x_3960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
lean_ctor_set(v___x_3960_, 1, v___x_3905_);
v___x_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
v_a_3887_ = v___x_3961_;
goto v___jp_3886_;
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_3962_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3955_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3955_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
v___jp_3970_:
{
if (v___y_3975_ == 0)
{
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
v_a_3895_ = v___x_3947_;
goto v___jp_3894_;
}
else
{
v___y_3949_ = v___y_3972_;
v___y_3950_ = v___y_3971_;
v___y_3951_ = v___y_3973_;
v___y_3952_ = v___y_3974_;
goto v___jp_3948_;
}
}
v___jp_3977_:
{
if (v___y_3980_ == 0)
{
v___y_3949_ = v___y_3979_;
v___y_3950_ = v___y_3978_;
v___y_3951_ = v___y_3981_;
v___y_3952_ = v___y_3982_;
goto v___jp_3948_;
}
else
{
v___y_3971_ = v___y_3978_;
v___y_3972_ = v___y_3979_;
v___y_3973_ = v___y_3981_;
v___y_3974_ = v___y_3982_;
v___y_3975_ = v___x_3976_;
goto v___jp_3970_;
}
}
v___jp_3983_:
{
if (v___y_3989_ == 0)
{
v___y_3971_ = v___y_3986_;
v___y_3972_ = v___y_3985_;
v___y_3973_ = v___y_3987_;
v___y_3974_ = v___y_3988_;
v___y_3975_ = v___x_3976_;
goto v___jp_3970_;
}
else
{
v___y_3978_ = v___y_3986_;
v___y_3979_ = v___y_3985_;
v___y_3980_ = v___y_3984_;
v___y_3981_ = v___y_3987_;
v___y_3982_ = v___y_3988_;
goto v___jp_3977_;
}
}
v___jp_3990_:
{
uint8_t v_emptyType_3997_; 
v_emptyType_3997_ = lean_ctor_get_uint8(v_config_3869_, sizeof(void*)*1 + 1);
if (v_emptyType_3997_ == 0)
{
v___y_3984_ = v___y_3991_;
v___y_3985_ = v___y_3996_;
v___y_3986_ = v___y_3995_;
v___y_3987_ = v___y_3994_;
v___y_3988_ = v___y_3993_;
v___y_3989_ = v___x_3976_;
goto v___jp_3983_;
}
else
{
if (v___y_3992_ == 0)
{
v___y_3978_ = v___y_3995_;
v___y_3979_ = v___y_3996_;
v___y_3980_ = v___y_3991_;
v___y_3981_ = v___y_3994_;
v___y_3982_ = v___y_3993_;
goto v___jp_3977_;
}
else
{
v___y_3984_ = v___y_3991_;
v___y_3985_ = v___y_3996_;
v___y_3986_ = v___y_3995_;
v___y_3987_ = v___y_3994_;
v___y_3988_ = v___y_3993_;
v___y_3989_ = v___x_3976_;
goto v___jp_3983_;
}
}
}
v___jp_3998_:
{
if (v___y_4005_ == 0)
{
v___y_3991_ = v___y_4003_;
v___y_3992_ = v___y_4004_;
v___y_3993_ = v___y_4002_;
v___y_3994_ = v___y_4001_;
v___y_3995_ = v___y_4000_;
v___y_3996_ = v___y_3999_;
goto v___jp_3990_;
}
else
{
lean_object* v___x_4006_; 
lean_inc(v_val_3901_);
lean_inc(v_mvarId_3870_);
v___x_4006_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3870_, v_val_3901_, v___y_4002_, v___y_4001_, v___y_4000_, v___y_3999_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; uint8_t v___x_4008_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
v___x_4008_ = lean_unbox(v_a_4007_);
lean_dec(v_a_4007_);
if (v___x_4008_ == 0)
{
v___y_3991_ = v___y_4003_;
v___y_3992_ = v___y_4004_;
v___y_3993_ = v___y_4002_;
v___y_3994_ = v___y_4001_;
v___y_3995_ = v___y_4000_;
v___y_3996_ = v___y_3999_;
goto v___jp_3990_;
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
lean_dec(v_val_3901_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v___x_4009_ = lean_box(v___x_3880_);
v___x_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
v___x_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
lean_ctor_set(v___x_4011_, 1, v___x_3905_);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
v_a_3887_ = v___x_4012_;
goto v___jp_3886_;
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec(v_val_3901_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_config_3869_);
v_a_4013_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4006_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4006_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
}
}
v___jp_3886_:
{
lean_object* v___x_3888_; lean_object* v___x_3890_; 
v___x_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3888_, 0, v_a_3887_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3888_);
v___x_3890_ = v___x_3884_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3888_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_snd_3882_);
v___x_3890_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3891_; 
v___x_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
return v___x_3891_;
}
}
v___jp_3894_:
{
lean_object* v___x_3896_; size_t v___x_3897_; size_t v___x_3898_; lean_object* v___x_3899_; 
v___x_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3893_);
lean_ctor_set(v___x_3896_, 1, v_a_3895_);
v___x_3897_ = ((size_t)1ULL);
v___x_3898_ = lean_usize_add(v_i_3873_, v___x_3897_);
v___x_3899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3869_, v_mvarId_3870_, v_as_3871_, v_sz_3872_, v___x_3898_, v___x_3896_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
return v___x_3899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4554_, lean_object* v_mvarId_4555_, lean_object* v_as_4556_, lean_object* v_sz_4557_, lean_object* v_i_4558_, lean_object* v_b_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
size_t v_sz_boxed_4565_; size_t v_i_boxed_4566_; lean_object* v_res_4567_; 
v_sz_boxed_4565_ = lean_unbox_usize(v_sz_4557_);
lean_dec(v_sz_4557_);
v_i_boxed_4566_ = lean_unbox_usize(v_i_4558_);
lean_dec(v_i_4558_);
v_res_4567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4554_, v_mvarId_4555_, v_as_4556_, v_sz_boxed_4565_, v_i_boxed_4566_, v_b_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
lean_dec_ref(v_as_4556_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4568_, lean_object* v_config_4569_, lean_object* v_mvarId_4570_, lean_object* v_n_4571_, lean_object* v_b_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
if (lean_obj_tag(v_n_4571_) == 0)
{
lean_object* v_cs_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; size_t v_sz_4581_; size_t v___x_4582_; lean_object* v___x_4583_; 
v_cs_4578_ = lean_ctor_get(v_n_4571_, 0);
v___x_4579_ = lean_box(0);
v___x_4580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v_b_4572_);
v_sz_4581_ = lean_array_size(v_cs_4578_);
v___x_4582_ = ((size_t)0ULL);
v___x_4583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4568_, v_config_4569_, v_mvarId_4570_, v_cs_4578_, v_sz_4581_, v___x_4582_, v___x_4580_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4598_; 
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4586_ = v___x_4583_;
v_isShared_4587_ = v_isSharedCheck_4598_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4583_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4598_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v_fst_4588_; 
v_fst_4588_ = lean_ctor_get(v_a_4584_, 0);
if (lean_obj_tag(v_fst_4588_) == 0)
{
lean_object* v_snd_4589_; lean_object* v___x_4590_; lean_object* v___x_4592_; 
v_snd_4589_ = lean_ctor_get(v_a_4584_, 1);
lean_inc(v_snd_4589_);
lean_dec(v_a_4584_);
v___x_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4590_, 0, v_snd_4589_);
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 0, v___x_4590_);
v___x_4592_ = v___x_4586_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4590_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
else
{
lean_object* v_val_4594_; lean_object* v___x_4596_; 
lean_inc_ref(v_fst_4588_);
lean_dec(v_a_4584_);
v_val_4594_ = lean_ctor_get(v_fst_4588_, 0);
lean_inc(v_val_4594_);
lean_dec_ref_known(v_fst_4588_, 1);
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 0, v_val_4594_);
v___x_4596_ = v___x_4586_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_val_4594_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
v_a_4599_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4583_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4583_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4604_; 
if (v_isShared_4602_ == 0)
{
v___x_4604_ = v___x_4601_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
else
{
lean_object* v_vs_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; size_t v_sz_4610_; size_t v___x_4611_; lean_object* v___x_4612_; 
v_vs_4607_ = lean_ctor_get(v_n_4571_, 0);
v___x_4608_ = lean_box(0);
v___x_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
lean_ctor_set(v___x_4609_, 1, v_b_4572_);
v_sz_4610_ = lean_array_size(v_vs_4607_);
v___x_4611_ = ((size_t)0ULL);
v___x_4612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4569_, v_mvarId_4570_, v_vs_4607_, v_sz_4610_, v___x_4611_, v___x_4609_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4627_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4627_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4627_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v_fst_4617_; 
v_fst_4617_ = lean_ctor_get(v_a_4613_, 0);
if (lean_obj_tag(v_fst_4617_) == 0)
{
lean_object* v_snd_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
v_snd_4618_ = lean_ctor_get(v_a_4613_, 1);
lean_inc(v_snd_4618_);
lean_dec(v_a_4613_);
v___x_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4619_, 0, v_snd_4618_);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4619_);
v___x_4621_ = v___x_4615_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
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
lean_inc_ref(v_fst_4617_);
lean_dec(v_a_4613_);
v_val_4623_ = lean_ctor_get(v_fst_4617_, 0);
lean_inc(v_val_4623_);
lean_dec_ref_known(v_fst_4617_, 1);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v_val_4623_);
v___x_4625_ = v___x_4615_;
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
v_a_4628_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4612_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4612_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4636_, lean_object* v_config_4637_, lean_object* v_mvarId_4638_, lean_object* v_as_4639_, size_t v_sz_4640_, size_t v_i_4641_, lean_object* v_b_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
uint8_t v___x_4648_; 
v___x_4648_ = lean_usize_dec_lt(v_i_4641_, v_sz_4640_);
if (v___x_4648_ == 0)
{
lean_object* v___x_4649_; 
lean_dec(v_mvarId_4638_);
lean_dec_ref(v_config_4637_);
v___x_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4649_, 0, v_b_4642_);
return v___x_4649_;
}
else
{
lean_object* v_snd_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4684_; 
v_snd_4650_ = lean_ctor_get(v_b_4642_, 1);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_b_4642_);
if (v_isSharedCheck_4684_ == 0)
{
lean_object* v_unused_4685_; 
v_unused_4685_ = lean_ctor_get(v_b_4642_, 0);
lean_dec(v_unused_4685_);
v___x_4652_ = v_b_4642_;
v_isShared_4653_ = v_isSharedCheck_4684_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_snd_4650_);
lean_dec(v_b_4642_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4684_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4654_; lean_object* v_a_4655_; lean_object* v___x_4656_; 
v___x_4654_ = lean_box(0);
v_a_4655_ = lean_array_uget_borrowed(v_as_4639_, v_i_4641_);
lean_inc(v_snd_4650_);
lean_inc(v_mvarId_4638_);
lean_inc_ref(v_config_4637_);
v___x_4656_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4636_, v_config_4637_, v_mvarId_4638_, v_a_4655_, v_snd_4650_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4675_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4659_ = v___x_4656_;
v_isShared_4660_ = v_isSharedCheck_4675_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4675_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
if (lean_obj_tag(v_a_4657_) == 0)
{
lean_object* v___x_4661_; lean_object* v___x_4663_; 
lean_dec(v_mvarId_4638_);
lean_dec_ref(v_config_4637_);
v___x_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4661_, 0, v_a_4657_);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v___x_4661_);
v___x_4663_ = v___x_4652_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4661_);
lean_ctor_set(v_reuseFailAlloc_4667_, 1, v_snd_4650_);
v___x_4663_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
lean_object* v___x_4665_; 
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
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; 
lean_del_object(v___x_4659_);
lean_dec(v_snd_4650_);
v_a_4668_ = lean_ctor_get(v_a_4657_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v_a_4657_, 1);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 1, v_a_4668_);
lean_ctor_set(v___x_4652_, 0, v___x_4654_);
v___x_4670_ = v___x_4652_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4674_, 1, v_a_4668_);
v___x_4670_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
size_t v___x_4671_; size_t v___x_4672_; 
v___x_4671_ = ((size_t)1ULL);
v___x_4672_ = lean_usize_add(v_i_4641_, v___x_4671_);
v_i_4641_ = v___x_4672_;
v_b_4642_ = v___x_4670_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4683_; 
lean_del_object(v___x_4652_);
lean_dec(v_snd_4650_);
lean_dec(v_mvarId_4638_);
lean_dec_ref(v_config_4637_);
v_a_4676_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4678_ = v___x_4656_;
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4656_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4681_; 
if (v_isShared_4679_ == 0)
{
v___x_4681_ = v___x_4678_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4676_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4686_, lean_object* v_config_4687_, lean_object* v_mvarId_4688_, lean_object* v_as_4689_, lean_object* v_sz_4690_, lean_object* v_i_4691_, lean_object* v_b_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
size_t v_sz_boxed_4698_; size_t v_i_boxed_4699_; lean_object* v_res_4700_; 
v_sz_boxed_4698_ = lean_unbox_usize(v_sz_4690_);
lean_dec(v_sz_4690_);
v_i_boxed_4699_ = lean_unbox_usize(v_i_4691_);
lean_dec(v_i_4691_);
v_res_4700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4686_, v_config_4687_, v_mvarId_4688_, v_as_4689_, v_sz_boxed_4698_, v_i_boxed_4699_, v_b_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec_ref(v_as_4689_);
lean_dec_ref(v_init_4686_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4701_, lean_object* v_config_4702_, lean_object* v_mvarId_4703_, lean_object* v_n_4704_, lean_object* v_b_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4701_, v_config_4702_, v_mvarId_4703_, v_n_4704_, v_b_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec_ref(v_n_4704_);
lean_dec_ref(v_init_4701_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4712_, lean_object* v_mvarId_4713_, lean_object* v_t_4714_, lean_object* v_init_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v_root_4721_; lean_object* v_tail_4722_; lean_object* v___x_4723_; 
v_root_4721_ = lean_ctor_get(v_t_4714_, 0);
v_tail_4722_ = lean_ctor_get(v_t_4714_, 1);
lean_inc(v_mvarId_4713_);
lean_inc_ref(v_config_4712_);
lean_inc_ref(v_init_4715_);
v___x_4723_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4715_, v_config_4712_, v_mvarId_4713_, v_root_4721_, v_init_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
lean_dec_ref(v_init_4715_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4760_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4726_ = v___x_4723_;
v_isShared_4727_ = v_isSharedCheck_4760_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4723_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4760_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
if (lean_obj_tag(v_a_4724_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4730_; 
lean_dec(v_mvarId_4713_);
lean_dec_ref(v_config_4712_);
v_a_4728_ = lean_ctor_get(v_a_4724_, 0);
lean_inc(v_a_4728_);
lean_dec_ref_known(v_a_4724_, 1);
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 0, v_a_4728_);
v___x_4730_ = v___x_4726_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4728_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; size_t v_sz_4735_; size_t v___x_4736_; lean_object* v___x_4737_; 
lean_del_object(v___x_4726_);
v_a_4732_ = lean_ctor_get(v_a_4724_, 0);
lean_inc(v_a_4732_);
lean_dec_ref_known(v_a_4724_, 1);
v___x_4733_ = lean_box(0);
v___x_4734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
lean_ctor_set(v___x_4734_, 1, v_a_4732_);
v_sz_4735_ = lean_array_size(v_tail_4722_);
v___x_4736_ = ((size_t)0ULL);
v___x_4737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4712_, v_mvarId_4713_, v_tail_4722_, v_sz_4735_, v___x_4736_, v___x_4734_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4751_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4740_ = v___x_4737_;
v_isShared_4741_ = v_isSharedCheck_4751_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4737_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4751_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v_fst_4742_; 
v_fst_4742_ = lean_ctor_get(v_a_4738_, 0);
if (lean_obj_tag(v_fst_4742_) == 0)
{
lean_object* v_snd_4743_; lean_object* v___x_4745_; 
v_snd_4743_ = lean_ctor_get(v_a_4738_, 1);
lean_inc(v_snd_4743_);
lean_dec(v_a_4738_);
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 0, v_snd_4743_);
v___x_4745_ = v___x_4740_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_snd_4743_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
else
{
lean_object* v_val_4747_; lean_object* v___x_4749_; 
lean_inc_ref(v_fst_4742_);
lean_dec(v_a_4738_);
v_val_4747_ = lean_ctor_get(v_fst_4742_, 0);
lean_inc(v_val_4747_);
lean_dec_ref_known(v_fst_4742_, 1);
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 0, v_val_4747_);
v___x_4749_ = v___x_4740_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_val_4747_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
v_a_4752_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4737_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4737_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
}
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec(v_mvarId_4713_);
lean_dec_ref(v_config_4712_);
v_a_4761_ = lean_ctor_get(v___x_4723_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4723_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4723_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4769_, lean_object* v_mvarId_4770_, lean_object* v_t_4771_, lean_object* v_init_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4769_, v_mvarId_4770_, v_t_4771_, v_init_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec_ref(v_t_4771_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4779_, lean_object* v___x_4780_, lean_object* v_config_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
lean_object* v___x_4787_; 
lean_inc(v_mvarId_4779_);
v___x_4787_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4779_, v___x_4780_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v___x_4788_; 
lean_dec_ref_known(v___x_4787_, 1);
lean_inc(v_mvarId_4779_);
v___x_4788_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4779_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4822_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4791_ = v___x_4788_;
v_isShared_4792_ = v_isSharedCheck_4822_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4822_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
uint8_t v___x_4793_; 
v___x_4793_ = lean_unbox(v_a_4789_);
if (v___x_4793_ == 0)
{
lean_object* v_lctx_4794_; lean_object* v_decls_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
lean_del_object(v___x_4791_);
v_lctx_4794_ = lean_ctor_get(v___y_4782_, 2);
v_decls_4795_ = lean_ctor_get(v_lctx_4794_, 1);
v___x_4796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4797_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4781_, v_mvarId_4779_, v_decls_4795_, v___x_4796_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4810_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4800_ = v___x_4797_;
v_isShared_4801_ = v_isSharedCheck_4810_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4797_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4810_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v_fst_4802_; 
v_fst_4802_ = lean_ctor_get(v_a_4798_, 0);
lean_inc(v_fst_4802_);
lean_dec(v_a_4798_);
if (lean_obj_tag(v_fst_4802_) == 0)
{
lean_object* v___x_4804_; 
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v_a_4789_);
v___x_4804_ = v___x_4800_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4789_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
else
{
lean_object* v_val_4806_; lean_object* v___x_4808_; 
lean_dec(v_a_4789_);
v_val_4806_ = lean_ctor_get(v_fst_4802_, 0);
lean_inc(v_val_4806_);
lean_dec_ref_known(v_fst_4802_, 1);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v_val_4806_);
v___x_4808_ = v___x_4800_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_val_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
lean_dec(v_a_4789_);
v_a_4811_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4797_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4797_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
else
{
lean_object* v___x_4820_; 
lean_dec_ref(v_config_4781_);
lean_dec(v_mvarId_4779_);
if (v_isShared_4792_ == 0)
{
v___x_4820_ = v___x_4791_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_a_4789_);
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
lean_dec_ref(v_config_4781_);
lean_dec(v_mvarId_4779_);
return v___x_4788_;
}
}
else
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4830_; 
lean_dec_ref(v_config_4781_);
lean_dec(v_mvarId_4779_);
v_a_4823_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4825_ = v___x_4787_;
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v___x_4787_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4831_, lean_object* v___x_4832_, lean_object* v_config_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4831_, v___x_4832_, v_config_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4842_, lean_object* v_config_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v___x_4849_; lean_object* v___f_4850_; lean_object* v___x_4851_; 
v___x_4849_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4842_);
v___f_4850_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4850_, 0, v_mvarId_4842_);
lean_closure_set(v___f_4850_, 1, v___x_4849_);
lean_closure_set(v___f_4850_, 2, v_config_4843_);
v___x_4851_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4842_, v___f_4850_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4852_, lean_object* v_config_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Lean_MVarId_contradictionCore(v_mvarId_4852_, v_config_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4860_, lean_object* v_config_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v___x_4867_; 
lean_inc(v_mvarId_4860_);
v___x_4867_ = l_Lean_MVarId_contradictionCore(v_mvarId_4860_, v_config_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4880_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4870_ = v___x_4867_;
v_isShared_4871_ = v_isSharedCheck_4880_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4880_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
uint8_t v___x_4872_; 
v___x_4872_ = lean_unbox(v_a_4868_);
lean_dec(v_a_4868_);
if (v___x_4872_ == 0)
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; 
lean_del_object(v___x_4870_);
v___x_4873_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4874_ = lean_box(0);
v___x_4875_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4873_, v_mvarId_4860_, v___x_4874_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
return v___x_4875_;
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4878_; 
lean_dec(v_mvarId_4860_);
v___x_4876_ = lean_box(0);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v___x_4876_);
v___x_4878_ = v___x_4870_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v___x_4876_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
}
else
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4888_; 
lean_dec(v_mvarId_4860_);
v_a_4881_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4883_ = v___x_4867_;
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4867_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4886_; 
if (v_isShared_4884_ == 0)
{
v___x_4886_ = v___x_4883_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4889_, lean_object* v_config_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l_Lean_MVarId_contradiction(v_mvarId_4889_, v_config_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
lean_dec(v_a_4894_);
lean_dec_ref(v_a_4893_);
lean_dec(v_a_4892_);
lean_dec_ref(v_a_4891_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4959_; uint8_t v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4959_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4960_ = 0;
v___x_4961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4962_ = l_Lean_registerTraceClass(v___x_4959_, v___x_4960_, v___x_4961_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4964_;
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
