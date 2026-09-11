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
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
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
size_t v_x_1117__boxed_155_; size_t v_x_1118__boxed_156_; lean_object* v_res_157_; 
v_x_1117__boxed_155_ = lean_unbox_usize(v_x_151_);
lean_dec(v_x_151_);
v_x_1118__boxed_156_ = lean_unbox_usize(v_x_152_);
lean_dec(v_x_152_);
v_res_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_150_, v_x_1117__boxed_155_, v_x_1118__boxed_156_, v_x_153_, v_x_154_);
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
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_186_, v_mvarId_165_, v_val_166_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 8, v___x_192_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
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
lean_ctor_set(v_reuseFailAlloc_201_, 8, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_201_, 9, v_dAssignment_187_);
lean_ctor_set(v_reuseFailAlloc_201_, 10, v_instanceTypedMVars_188_);
v___x_194_ = v_reuseFailAlloc_201_;
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
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_cache_171_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_zetaDeltaFVarIds_172_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_postponed_173_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_diag_174_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_st_ref_put(v___y_167_, v___x_196_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
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
lean_object* v___x_216_; 
lean_inc(v_mvarId_210_);
v___x_216_ = l_Lean_MVarId_getType(v_mvarId_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_261_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_261_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_261_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_261_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___f_221_; lean_object* v___x_222_; 
v___f_221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
v___x_222_ = lean_find_expr(v___f_221_, v_a_217_);
lean_dec(v_a_217_);
if (lean_obj_tag(v___x_222_) == 1)
{
lean_object* v_val_223_; lean_object* v___x_224_; 
lean_del_object(v___x_219_);
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
lean_inc(v_mvarId_210_);
v___x_224_ = l_Lean_MVarId_getType(v_mvarId_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
v___x_226_ = l_Lean_Expr_appArg_x21(v_val_223_);
lean_dec(v_val_223_);
v___x_227_ = l_Lean_Meta_mkFalseElim(v_a_225_, v___x_226_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
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
lean_dec(v_val_223_);
lean_dec(v_mvarId_210_);
v_a_248_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_224_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_224_);
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
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_257_);
v___x_259_ = v___x_219_;
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
v_a_262_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_216_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_216_);
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
size_t v_x_1468__boxed_311_; size_t v_x_1469__boxed_312_; lean_object* v_res_313_; 
v_x_1468__boxed_311_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_x_1469__boxed_312_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_res_313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_305_, v_x_306_, v_x_1468__boxed_311_, v_x_1469__boxed_312_, v_x_309_, v_x_310_);
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
lean_object* v___x_623_; double v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_623_ = lean_box(0);
v___x_624_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_625_ = 0;
v___x_626_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_627_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_627_, 0, v_cls_592_);
lean_ctor_set(v___x_627_, 1, v___x_623_);
lean_ctor_set(v___x_627_, 2, v___x_626_);
lean_ctor_set_float(v___x_627_, sizeof(void*)*3, v___x_624_);
lean_ctor_set_float(v___x_627_, sizeof(void*)*3 + 8, v___x_624_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*3 + 16, v___x_625_);
v___x_628_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_629_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v_a_601_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
lean_inc(v_ref_599_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v_ref_599_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_PersistentArray_push___redArg(v_traces_619_, v___x_630_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_631_);
v___x_633_ = v___x_621_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_631_);
lean_ctor_set_uint64(v_reuseFailAlloc_642_, sizeof(void*)*1, v_tid_618_);
v___x_633_ = v_reuseFailAlloc_642_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v___x_633_);
v___x_635_ = v___x_616_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_env_607_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_nextMacroScope_608_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_ngen_609_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_auxDeclNGen_610_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_641_, 5, v_cache_611_);
lean_ctor_set(v_reuseFailAlloc_641_, 6, v_messages_612_);
lean_ctor_set(v_reuseFailAlloc_641_, 7, v_infoState_613_);
lean_ctor_set(v_reuseFailAlloc_641_, 8, v_snapshotTasks_614_);
v___x_635_ = v_reuseFailAlloc_641_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = lean_st_ref_put(v___y_597_, v___x_635_);
v___x_637_ = lean_box(0);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_637_);
v___x_639_ = v___x_603_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
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
size_t v_sz_boxed_674_; size_t v___x_15940__boxed_675_; uint8_t v___x_15942__boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v___x_15940__boxed_675_ = lean_unbox_usize(v___x_665_);
lean_dec(v___x_665_);
v___x_15942__boxed_676_ = lean_unbox(v___x_667_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_661_, v_mvarId_662_, v_fields_663_, v_sz_boxed_674_, v___x_15940__boxed_675_, v___x_666_, v___x_15942__boxed_676_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
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
uint8_t v___x_16062__boxed_879_; uint8_t v___x_16065__boxed_880_; lean_object* v_res_881_; 
v___x_16062__boxed_879_ = lean_unbox(v___x_869_);
v___x_16065__boxed_880_ = lean_unbox(v___x_872_);
v_res_881_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_866_, v_fvarId_867_, v___x_868_, v___x_16062__boxed_879_, v___x_870_, v_val_871_, v___x_16065__boxed_880_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
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
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; 
v___x_900_ = lean_st_ref_take(v_a_887_);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_sub(v___x_900_, v___x_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_st_ref_put(v_a_887_, v___x_902_);
v___x_904_ = 1;
v___x_905_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_906_ = lean_box(0);
v___x_907_ = lean_box(v___x_899_);
v___x_908_ = lean_box(v___x_904_);
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
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_968_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_968_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_968_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_968_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
uint8_t v___x_962_; 
v___x_962_ = lean_unbox(v_a_958_);
if (v___x_962_ == 0)
{
lean_del_object(v___x_960_);
lean_dec(v_a_958_);
v_a_941_ = v___x_949_;
goto v___jp_940_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v___x_929_);
lean_dec_ref(v___x_928_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v_a_958_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_948_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_964_);
v___x_966_ = v___x_960_;
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
lean_dec(v___x_929_);
lean_dec_ref(v___x_928_);
v_a_969_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_957_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_957_);
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
lean_dec(v___x_953_);
lean_dec(v___x_929_);
lean_dec_ref(v___x_928_);
v_a_977_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_954_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_954_);
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
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Meta_saveState___redArg(v___y_1079_, v___y_1081_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___y_1086_; lean_object* v___y_1087_; uint8_t v___y_1088_; lean_object* v___y_1107_; lean_object* v_a_1108_; lean_object* v___x_1111_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
v___x_1111_ = lean_apply_5(v_x_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, lean_box(0));
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; uint8_t v___x_1113_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
v___x_1113_ = lean_unbox(v_a_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec_ref_known(v___x_1111_, 1);
v___x_1114_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1084_, v___y_1079_, v___y_1081_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_a_1084_);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v___x_1114_, 0);
lean_dec(v_unused_1122_);
v___x_1116_ = v___x_1114_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_dec(v___x_1114_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v_a_1112_);
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1112_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_a_1112_);
v_a_1123_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1114_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1114_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
lean_inc(v_a_1123_);
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
v___y_1107_ = v___x_1128_;
v_a_1108_ = v_a_1123_;
goto v___jp_1106_;
}
}
}
}
else
{
lean_dec(v_a_1112_);
lean_dec(v_a_1084_);
return v___x_1111_;
}
}
else
{
lean_object* v_a_1131_; 
v_a_1131_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1131_);
v___y_1107_ = v___x_1111_;
v_a_1108_ = v_a_1131_;
goto v___jp_1106_;
}
v___jp_1085_:
{
if (v___y_1088_ == 0)
{
lean_object* v___x_1089_; 
lean_dec_ref(v___y_1087_);
v___x_1089_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1084_, v___y_1079_, v___y_1081_);
lean_dec(v_a_1084_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1089_, 0);
lean_dec(v_unused_1097_);
v___x_1091_ = v___x_1089_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v___x_1089_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 1);
lean_ctor_set(v___x_1091_, 0, v___y_1086_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___y_1086_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v___y_1086_);
v_a_1098_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1089_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1089_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_dec_ref(v___y_1086_);
lean_dec(v_a_1084_);
return v___y_1087_;
}
}
v___jp_1106_:
{
uint8_t v___x_1109_; 
v___x_1109_ = l_Lean_Exception_isInterrupt(v_a_1108_);
if (v___x_1109_ == 0)
{
uint8_t v___x_1110_; 
lean_inc_ref(v_a_1108_);
v___x_1110_ = l_Lean_Exception_isRuntime(v_a_1108_);
v___y_1086_ = v_a_1108_;
v___y_1087_ = v___y_1107_;
v___y_1088_ = v___x_1110_;
goto v___jp_1085_;
}
else
{
v___y_1086_ = v_a_1108_;
v___y_1087_ = v___y_1107_;
v___y_1088_ = v___x_1109_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_x_1077_);
v_a_1132_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1083_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1083_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1147_, lean_object* v_x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1147_, v_x_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_a_1163_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1154_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1154_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1171_, lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1171_, v_x_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1179_, lean_object* v_mvarId_1180_, lean_object* v_x_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1180_, v_x_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1188_, lean_object* v_mvarId_1189_, lean_object* v_x_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1188_, v_mvarId_1189_, v_x_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1197_, lean_object* v_fuel_1198_, lean_object* v_fvarId_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_MVarId_exfalso(v_mvarId_1197_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1207_ = lean_st_mk_ref(v_fuel_1198_);
v___x_1208_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1206_, v_fvarId_1199_, v___x_1207_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_st_ref_get(v___x_1207_);
lean_dec(v___x_1207_);
lean_dec(v___x_1213_);
if (v_isShared_1212_ == 0)
{
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1209_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
else
{
lean_dec(v___x_1207_);
return v___x_1208_;
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_fvarId_1199_);
lean_dec(v_fuel_1198_);
v_a_1218_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1205_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1205_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1226_, lean_object* v_fuel_1227_, lean_object* v_fvarId_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1226_, v_fuel_1227_, v_fvarId_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1235_, lean_object* v___f_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1235_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; uint8_t v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
v___x_1244_ = lean_unbox(v_a_1243_);
lean_dec(v_a_1243_);
if (v___x_1244_ == 0)
{
lean_dec_ref(v___f_1236_);
return v___x_1242_;
}
else
{
lean_object* v___x_1245_; 
lean_dec_ref_known(v___x_1242_, 1);
v___x_1245_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1245_;
}
}
else
{
lean_dec_ref(v___f_1236_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1246_, lean_object* v___f_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1246_, v___f_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1254_, lean_object* v_fvarId_1255_, lean_object* v_fuel_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; 
lean_inc(v_fvarId_1255_);
lean_inc(v_mvarId_1254_);
v___f_1262_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1262_, 0, v_mvarId_1254_);
lean_closure_set(v___f_1262_, 1, v_fuel_1256_);
lean_closure_set(v___f_1262_, 2, v_fvarId_1255_);
v___f_1263_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1263_, 0, v_fvarId_1255_);
lean_closure_set(v___f_1263_, 1, v___f_1262_);
v___x_1264_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1254_, v___f_1263_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1265_, lean_object* v_fvarId_1266_, lean_object* v_fuel_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1265_, v_fvarId_1266_, v_fuel_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1274_){
_start:
{
uint8_t v___x_1275_; 
v___x_1275_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1276_){
_start:
{
uint8_t v_res_1277_; lean_object* v_r_1278_; 
v_res_1277_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1276_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1279_, lean_object* v_acc_1280_){
_start:
{
if (lean_obj_tag(v_e_1279_) == 7)
{
lean_object* v_binderType_1281_; lean_object* v_body_1282_; uint8_t v___y_1284_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_binderType_1281_ = lean_ctor_get(v_e_1279_, 1);
v_body_1282_ = lean_ctor_get(v_e_1279_, 2);
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_expr_has_loose_bvar(v_body_1282_, v___x_1288_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = l_Lean_Expr_isEq(v_binderType_1281_);
if (v___x_1290_ == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Lean_Expr_isHEq(v_binderType_1281_);
v___y_1284_ = v___x_1291_;
goto v___jp_1283_;
}
else
{
v___y_1284_ = v___x_1290_;
goto v___jp_1283_;
}
}
else
{
uint8_t v___x_1292_; 
v___x_1292_ = 0;
v___y_1284_ = v___x_1292_;
goto v___jp_1283_;
}
v___jp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_box(v___y_1284_);
v___x_1286_ = lean_array_push(v_acc_1280_, v___x_1285_);
v_e_1279_ = v_body_1282_;
v_acc_1280_ = v___x_1286_;
goto _start;
}
}
else
{
return v_acc_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1293_, lean_object* v_acc_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1293_, v_acc_1294_);
lean_dec_ref(v_e_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1300_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1298_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Meta_mkGenDiseqMask(v_e_1301_);
lean_dec_ref(v_e_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___f_1310_; lean_object* v___x_4344__overap_1311_; lean_object* v___x_1312_; 
v___f_1310_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1311_ = lean_panic_fn_borrowed(v___f_1310_, v_msg_1304_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
v___x_1312_ = lean_apply_5(v___x_4344__overap_1311_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, lean_box(0));
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1320_, lean_object* v___y_1321_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_Expr_hasMVar(v_e_1320_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_e_1320_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v_mctx_1326_; lean_object* v___x_1327_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___x_1330_; lean_object* v_cache_1331_; lean_object* v_zetaDeltaFVarIds_1332_; lean_object* v_postponed_1333_; lean_object* v_diag_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1343_; 
v___x_1325_ = lean_st_ref_get(v___y_1321_);
v_mctx_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc_ref(v_mctx_1326_);
lean_dec(v___x_1325_);
v___x_1327_ = l_Lean_instantiateMVarsCore(v_mctx_1326_, v_e_1320_);
v_fst_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_fst_1328_);
v_snd_1329_ = lean_ctor_get(v___x_1327_, 1);
lean_inc(v_snd_1329_);
lean_dec_ref(v___x_1327_);
v___x_1330_ = lean_st_ref_take(v___y_1321_);
v_cache_1331_ = lean_ctor_get(v___x_1330_, 1);
v_zetaDeltaFVarIds_1332_ = lean_ctor_get(v___x_1330_, 2);
v_postponed_1333_ = lean_ctor_get(v___x_1330_, 3);
v_diag_1334_ = lean_ctor_get(v___x_1330_, 4);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1330_, 0);
lean_dec(v_unused_1344_);
v___x_1336_ = v___x_1330_;
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_diag_1334_);
lean_inc(v_postponed_1333_);
lean_inc(v_zetaDeltaFVarIds_1332_);
lean_inc(v_cache_1331_);
lean_dec(v___x_1330_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v_snd_1329_);
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_snd_1329_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_cache_1331_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_zetaDeltaFVarIds_1332_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_postponed_1333_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_diag_1334_);
v___x_1339_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_st_ref_put(v___y_1321_, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_fst_1328_);
return v___x_1341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1345_, v___y_1346_);
lean_dec(v___y_1346_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1349_, v___y_1351_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1363_, uint8_t v_allowLevelAssignments_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1364_, v_k_1363_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_a_1379_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1370_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1370_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1387_, lean_object* v_allowLevelAssignments_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1394_; lean_object* v_res_1395_; 
v_allowLevelAssignments_boxed_1394_ = lean_unbox(v_allowLevelAssignments_1388_);
v_res_1395_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1387_, v_allowLevelAssignments_boxed_1394_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1396_, lean_object* v_k_1397_, uint8_t v_allowLevelAssignments_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1397_, v_allowLevelAssignments_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1405_, lean_object* v_k_1406_, lean_object* v_allowLevelAssignments_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1413_; lean_object* v_res_1414_; 
v_allowLevelAssignments_boxed_1413_ = lean_unbox(v_allowLevelAssignments_1407_);
v_res_1414_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1405_, v_k_1406_, v_allowLevelAssignments_boxed_1413_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1417_, size_t v_sz_1418_, size_t v_i_1419_, lean_object* v_b_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_a_1427_; uint8_t v___x_1431_; 
v___x_1431_ = lean_usize_dec_lt(v_i_1419_, v_sz_1418_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_b_1420_);
return v___x_1432_;
}
else
{
lean_object* v_snd_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1595_; 
v_snd_1433_ = lean_ctor_get(v_b_1420_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_b_1420_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v_b_1420_, 0);
lean_dec(v_unused_1596_);
v___x_1435_ = v_b_1420_;
v_isShared_1436_ = v_isSharedCheck_1595_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_snd_1433_);
lean_dec(v_b_1420_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1595_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_array_1437_; lean_object* v_start_1438_; lean_object* v_stop_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_array_1437_ = lean_ctor_get(v_snd_1433_, 0);
v_start_1438_ = lean_ctor_get(v_snd_1433_, 1);
v_stop_1439_ = lean_ctor_get(v_snd_1433_, 2);
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_nat_dec_lt(v_start_1438_, v_stop_1439_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1443_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1440_);
v___x_1443_ = v___x_1435_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_snd_1433_);
v___x_1443_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
else
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1591_; 
lean_inc(v_stop_1439_);
lean_inc(v_start_1438_);
lean_inc_ref(v_array_1437_);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_snd_1433_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; 
v_unused_1592_ = lean_ctor_get(v_snd_1433_, 2);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_snd_1433_, 1);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_snd_1433_, 0);
lean_dec(v_unused_1594_);
v___x_1447_ = v_snd_1433_;
v_isShared_1448_ = v_isSharedCheck_1591_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v_snd_1433_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1591_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1449_ = lean_array_fget(v_array_1437_, v_start_1438_);
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_add(v_start_1438_, v___x_1450_);
lean_dec(v_start_1438_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 1, v___x_1451_);
v___x_1453_ = v___x_1447_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_array_1437_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_stop_1439_);
v___x_1453_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_unbox(v___x_1449_);
lean_dec(v___x_1449_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1456_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1453_);
lean_ctor_set(v___x_1435_, 0, v___x_1440_);
v___x_1456_ = v___x_1435_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1453_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
v_a_1427_ = v___x_1456_;
goto v___jp_1426_;
}
}
else
{
lean_object* v_a_1458_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___x_1530_; 
v_a_1458_ = lean_array_uget_borrowed(v_as_1417_, v_i_1419_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
lean_inc(v_a_1458_);
v___x_1530_ = lean_infer_type(v_a_1458_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = l_Lean_Meta_matchEq_x3f(v_a_1531_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
if (lean_obj_tag(v_a_1533_) == 1)
{
lean_object* v_val_1534_; lean_object* v_snd_1535_; lean_object* v_fst_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1572_; 
v_val_1534_ = lean_ctor_get(v_a_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v_a_1533_, 1);
v_snd_1535_ = lean_ctor_get(v_val_1534_, 1);
lean_inc(v_snd_1535_);
lean_dec(v_val_1534_);
v_fst_1536_ = lean_ctor_get(v_snd_1535_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_snd_1535_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v_snd_1535_, 1);
lean_dec(v_unused_1573_);
v___x_1538_ = v_snd_1535_;
v_isShared_1539_ = v_isSharedCheck_1572_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_fst_1536_);
lean_dec(v_snd_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1572_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_Meta_mkEqRefl(v_fst_1536_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
lean_inc(v_a_1458_);
v___x_1542_ = l_Lean_Meta_isExprDefEq(v_a_1458_, v_a_1541_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1555_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1555_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1555_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_unbox(v_a_1543_);
lean_dec(v_a_1543_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
lean_del_object(v___x_1435_);
v___x_1548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 1, v___x_1453_);
lean_ctor_set(v___x_1538_, 0, v___x_1548_);
v___x_1550_ = v___x_1538_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___x_1453_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1550_);
v___x_1552_ = v___x_1545_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_del_object(v___x_1545_);
lean_del_object(v___x_1538_);
v___y_1460_ = v___y_1421_;
v___y_1461_ = v___y_1422_;
v___y_1462_ = v___y_1423_;
v___y_1463_ = v___y_1424_;
goto v___jp_1459_;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_del_object(v___x_1538_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1435_);
v_a_1556_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1542_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1542_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_del_object(v___x_1538_);
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1435_);
v_a_1564_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1540_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1540_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
else
{
lean_dec(v_a_1533_);
v___y_1460_ = v___y_1421_;
v___y_1461_ = v___y_1422_;
v___y_1462_ = v___y_1423_;
v___y_1463_ = v___y_1424_;
goto v___jp_1459_;
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1435_);
v_a_1574_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1532_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1532_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1435_);
v_a_1582_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1530_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1530_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
v___jp_1459_:
{
lean_object* v___x_1464_; 
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v_a_1458_);
v___x_1464_ = lean_infer_type(v_a_1458_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1466_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
v___x_1466_ = l_Lean_Meta_matchHEq_x3f(v_a_1465_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
if (lean_obj_tag(v_a_1467_) == 1)
{
lean_object* v_val_1468_; lean_object* v_snd_1469_; lean_object* v_fst_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1509_; 
lean_del_object(v___x_1435_);
v_val_1468_ = lean_ctor_get(v_a_1467_, 0);
lean_inc(v_val_1468_);
lean_dec_ref_known(v_a_1467_, 1);
v_snd_1469_ = lean_ctor_get(v_val_1468_, 1);
lean_inc(v_snd_1469_);
lean_dec(v_val_1468_);
v_fst_1470_ = lean_ctor_get(v_snd_1469_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_snd_1469_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_snd_1469_, 1);
lean_dec(v_unused_1510_);
v___x_1472_ = v_snd_1469_;
v_isShared_1473_ = v_isSharedCheck_1509_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_fst_1470_);
lean_dec(v_snd_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1509_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Meta_mkHEqRefl(v_fst_1470_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
lean_inc(v_a_1458_);
v___x_1476_ = l_Lean_Meta_isExprDefEq(v_a_1458_, v_a_1475_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1492_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1492_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1492_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_unbox(v_a_1477_);
lean_dec(v_a_1477_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1453_);
lean_ctor_set(v___x_1472_, 0, v___x_1482_);
v___x_1484_ = v___x_1472_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1453_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1484_);
v___x_1486_ = v___x_1479_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v___x_1490_; 
lean_del_object(v___x_1479_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1453_);
lean_ctor_set(v___x_1472_, 0, v___x_1440_);
v___x_1490_ = v___x_1472_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1453_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
v_a_1427_ = v___x_1490_;
goto v___jp_1426_;
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_del_object(v___x_1472_);
lean_dec_ref(v___x_1453_);
v_a_1493_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1476_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1476_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_del_object(v___x_1472_);
lean_dec_ref(v___x_1453_);
v_a_1501_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1474_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1474_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
else
{
lean_object* v___x_1512_; 
lean_dec(v_a_1467_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1453_);
lean_ctor_set(v___x_1435_, 0, v___x_1440_);
v___x_1512_ = v___x_1435_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1453_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
v_a_1427_ = v___x_1512_;
goto v___jp_1426_;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1435_);
v_a_1514_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1466_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1466_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v___x_1453_);
lean_del_object(v___x_1435_);
v_a_1522_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1464_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1464_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
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
v___jp_1426_:
{
size_t v___x_1428_; size_t v___x_1429_; 
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = lean_usize_add(v_i_1419_, v___x_1428_);
v_i_1419_ = v___x_1429_;
v_b_1420_ = v_a_1427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1597_, lean_object* v_sz_1598_, lean_object* v_i_1599_, lean_object* v_b_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
size_t v_sz_boxed_1606_; size_t v_i_boxed_1607_; lean_object* v_res_1608_; 
v_sz_boxed_1606_ = lean_unbox_usize(v_sz_1598_);
lean_dec(v_sz_1598_);
v_i_boxed_1607_ = lean_unbox_usize(v_i_1599_);
lean_dec(v_i_1599_);
v_res_1608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1597_, v_sz_boxed_1606_, v_i_boxed_1607_, v_b_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec_ref(v_as_1597_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1609_, uint8_t v___x_1610_, lean_object* v_localDecl_1611_, lean_object* v_mvarId_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; 
lean_inc_ref(v___x_1609_);
v___x_1618_ = l_Lean_Meta_forallMetaTelescope(v___x_1609_, v___x_1610_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v_fst_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1709_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v_fst_1620_ = lean_ctor_get(v_a_1619_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_a_1619_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v_a_1619_, 1);
lean_dec(v_unused_1710_);
v___x_1622_ = v_a_1619_;
v_isShared_1623_ = v_isSharedCheck_1709_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_fst_1620_);
lean_dec(v_a_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1709_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1624_ = l_Lean_Meta_mkGenDiseqMask(v___x_1609_);
lean_dec_ref(v___x_1609_);
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = lean_array_get_size(v___x_1624_);
v___x_1627_ = l_Array_toSubarray___redArg(v___x_1624_, v___x_1625_, v___x_1626_);
v___x_1628_ = lean_box(0);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___x_1627_);
lean_ctor_set(v___x_1622_, 0, v___x_1628_);
v___x_1630_ = v___x_1622_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v___x_1627_);
v___x_1630_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
size_t v_sz_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v_sz_1631_ = lean_array_size(v_fst_1620_);
v___x_1632_ = ((size_t)0ULL);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1620_, v_sz_1631_, v___x_1632_, v___x_1630_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1699_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1699_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1699_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_fst_1638_; 
v_fst_1638_ = lean_ctor_get(v_a_1634_, 0);
lean_inc(v_fst_1638_);
lean_dec(v_a_1634_);
if (lean_obj_tag(v_fst_1638_) == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1694_; 
lean_del_object(v___x_1636_);
v___x_1639_ = l_Lean_LocalDecl_toExpr(v_localDecl_1611_);
v___x_1640_ = l_Lean_mkAppN(v___x_1639_, v_fst_1620_);
lean_dec(v_fst_1620_);
v___x_1641_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1640_, v___y_1614_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1694_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1694_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; 
lean_inc(v_a_1642_);
v___x_1646_ = l_Lean_Meta_hasAssignableMVar(v_a_1642_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1685_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1685_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1685_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_unbox(v_a_1647_);
lean_dec(v_a_1647_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_del_object(v___x_1649_);
v___x_1652_ = l_Lean_MVarId_getType(v_mvarId_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = l_Lean_Meta_mkFalseElim(v_a_1653_, v_a_1642_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1665_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 1);
lean_ctor_set(v___x_1644_, 0, v_a_1655_);
v___x_1660_ = v___x_1644_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1660_);
v___x_1662_ = v___x_1657_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
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
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_del_object(v___x_1644_);
v_a_1666_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1654_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1654_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
v_a_1674_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1652_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1652_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_object* v___x_1683_; 
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
lean_dec(v_mvarId_1612_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1628_);
v___x_1683_ = v___x_1649_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1628_);
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
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_del_object(v___x_1644_);
lean_dec(v_a_1642_);
lean_dec(v_mvarId_1612_);
v_a_1686_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1646_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1646_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
else
{
lean_object* v_val_1695_; lean_object* v___x_1697_; 
lean_dec(v_fst_1620_);
lean_dec(v_mvarId_1612_);
lean_dec_ref(v_localDecl_1611_);
v_val_1695_ = lean_ctor_get(v_fst_1638_, 0);
lean_inc(v_val_1695_);
lean_dec_ref_known(v_fst_1638_, 1);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_val_1695_);
v___x_1697_ = v___x_1636_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_val_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec(v_fst_1620_);
lean_dec(v_mvarId_1612_);
lean_dec_ref(v_localDecl_1611_);
v_a_1700_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1633_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1633_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_mvarId_1612_);
lean_dec_ref(v_localDecl_1611_);
lean_dec_ref(v___x_1609_);
v_a_1711_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1618_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1618_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1719_, lean_object* v___x_1720_, lean_object* v_localDecl_1721_, lean_object* v_mvarId_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
uint8_t v___x_6076__boxed_1728_; lean_object* v_res_1729_; 
v___x_6076__boxed_1728_ = lean_unbox(v___x_1720_);
v_res_1729_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1719_, v___x_6076__boxed_1728_, v_localDecl_1721_, v_mvarId_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1729_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1734_ = lean_unsigned_to_nat(2u);
v___x_1735_ = lean_unsigned_to_nat(120u);
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1738_ = l_mkPanicMessageWithDecl(v___x_1737_, v___x_1736_, v___x_1735_, v___x_1734_, v___x_1733_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1739_, lean_object* v_localDecl_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = l_Lean_LocalDecl_type(v_localDecl_1740_);
lean_inc_ref(v___x_1746_);
v___x_1747_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec_ref(v___x_1746_);
lean_dec_ref(v_localDecl_1740_);
lean_dec(v_mvarId_1739_);
v___x_1748_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1749_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1748_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
return v___x_1749_;
}
else
{
uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___f_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1750_ = 0;
v___x_1751_ = lean_box(v___x_1750_);
lean_inc(v_mvarId_1739_);
v___f_1752_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1752_, 0, v___x_1746_);
lean_closure_set(v___f_1752_, 1, v___x_1751_);
lean_closure_set(v___f_1752_, 2, v_localDecl_1740_);
lean_closure_set(v___f_1752_, 3, v_mvarId_1739_);
v___x_1753_ = 0;
v___x_1754_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1752_, v___x_1753_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1774_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1774_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1774_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
if (lean_obj_tag(v_a_1755_) == 1)
{
lean_object* v_val_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
lean_del_object(v___x_1757_);
v_val_1759_ = lean_ctor_get(v_a_1755_, 0);
lean_inc(v_val_1759_);
lean_dec_ref_known(v_a_1755_, 1);
v___x_1760_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1739_, v_val_1759_, v_a_1742_);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v___x_1760_, 0);
lean_dec(v_unused_1769_);
v___x_1762_ = v___x_1760_;
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
else
{
lean_dec(v___x_1760_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = lean_box(v___x_1747_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_dec(v_a_1755_);
lean_dec(v_mvarId_1739_);
v___x_1770_ = lean_box(v___x_1753_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1770_);
v___x_1772_ = v___x_1757_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec(v_mvarId_1739_);
v_a_1775_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1754_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1754_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1783_, lean_object* v_localDecl_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1783_, v_localDecl_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1790_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(0);
v___x_1803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1804_ = l_Lean_mkConst(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1805_; lean_object* v_dummy_1806_; 
v___x_1805_ = lean_box(0);
v_dummy_1806_ = l_Lean_Expr_sort___override(v___x_1805_);
return v_dummy_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1807_, lean_object* v_mvarId_1808_, lean_object* v_as_1809_, size_t v_sz_1810_, size_t v_i_1811_, lean_object* v_b_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_usize_dec_lt(v_i_1811_, v_sz_1810_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; 
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_b_1812_);
return v___x_1819_;
}
else
{
lean_object* v_snd_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_2470_; 
v_snd_1820_ = lean_ctor_get(v_b_1812_, 1);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_b_1812_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v_b_1812_, 0);
lean_dec(v_unused_2471_);
v___x_1822_ = v_b_1812_;
v_isShared_1823_ = v_isSharedCheck_2470_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_snd_1820_);
lean_dec(v_b_1812_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_2470_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_a_1825_; lean_object* v___x_1831_; lean_object* v_a_1833_; lean_object* v_a_1838_; 
v___x_1831_ = lean_box(0);
v_a_1838_ = lean_array_uget(v_as_1809_, v_i_1811_);
if (lean_obj_tag(v_a_1838_) == 0)
{
lean_del_object(v___x_1822_);
v_a_1833_ = v_snd_1820_;
goto v___jp_1832_;
}
else
{
lean_object* v_val_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_2469_; 
v_val_1839_ = lean_ctor_get(v_a_1838_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_a_1838_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_1841_ = v_a_1838_;
v_isShared_1842_ = v_isSharedCheck_2469_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_val_1839_);
lean_dec(v_a_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_2469_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___x_1884_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; uint8_t v___y_1911_; uint8_t v___x_1912_; lean_object* v___y_1914_; uint8_t v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1920_; uint8_t v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; uint8_t v___y_1925_; uint8_t v___y_1927_; uint8_t v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; uint8_t v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; uint8_t v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; uint8_t v___y_1941_; 
v___x_1843_ = lean_box(0);
v___x_1884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1912_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1839_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1956_; uint8_t v___y_1958_; uint8_t v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1967_; lean_object* v___y_1968_; uint8_t v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; uint8_t v___y_1972_; lean_object* v___y_1973_; uint8_t v___y_1974_; lean_object* v___y_1977_; uint8_t v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1981_; lean_object* v___y_1982_; lean_object* v_a_1983_; lean_object* v___y_1987_; lean_object* v___y_1988_; uint8_t v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; uint8_t v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_2031_; uint8_t v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; uint8_t v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2060_; uint8_t v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; uint8_t v___y_2064_; lean_object* v___y_2065_; uint8_t v___y_2066_; lean_object* v___y_2068_; uint8_t v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; uint8_t v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; uint8_t v___y_2075_; lean_object* v___y_2078_; uint8_t v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; uint8_t v___y_2082_; lean_object* v___y_2083_; uint8_t v___y_2084_; lean_object* v___y_2097_; uint8_t v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; uint8_t v___y_2101_; lean_object* v___y_2102_; uint8_t v___y_2103_; uint8_t v___y_2105_; uint8_t v_isHEq_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; uint8_t v___y_2120_; uint8_t v_isEq_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___x_2406_; 
v___x_1956_ = l_Lean_LocalDecl_type(v_val_1839_);
lean_inc_ref(v___x_1956_);
v___x_2406_ = l_Lean_Meta_matchNot_x3f(v___x_1956_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
if (lean_obj_tag(v_a_2407_) == 1)
{
lean_object* v_val_2408_; lean_object* v___x_2409_; 
v_val_2408_ = lean_ctor_get(v_a_2407_, 0);
lean_inc(v_val_2408_);
lean_dec_ref_known(v_a_2407_, 1);
v___x_2409_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2408_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
if (lean_obj_tag(v_a_2410_) == 1)
{
lean_object* v_val_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec_ref(v_config_1807_);
v_val_2411_ = lean_ctor_get(v_a_2410_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_a_2410_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2413_ = v_a_2410_;
v_isShared_2414_ = v_isSharedCheck_2452_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_val_2411_);
lean_dec(v_a_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2452_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; 
lean_inc(v_mvarId_1808_);
v___x_2415_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2417_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2418_ = l_Lean_mkFVar(v_val_2411_);
v___x_2419_ = l_Lean_Expr_app___override(v___x_2417_, v___x_2418_);
v___x_2420_ = l_Lean_Meta_mkFalseElim(v_a_2416_, v___x_2419_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2422_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2420_, 1);
v___x_2422_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2421_, v___y_1814_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_dec_ref_known(v___x_2422_, 1);
v___x_2423_ = lean_box(v___x_1818_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2423_);
v___x_2425_ = v___x_2413_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v___x_1843_);
v_a_1825_ = v___x_2426_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_del_object(v___x_2413_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_2428_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2422_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2422_);
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
lean_del_object(v___x_2413_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2436_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2420_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2420_);
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
lean_del_object(v___x_2413_);
lean_dec(v_val_2411_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2444_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2415_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2415_);
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
lean_dec(v_a_2410_);
v___y_2272_ = v___y_1813_;
v___y_2273_ = v___y_1814_;
v___y_2274_ = v___y_1815_;
v___y_2275_ = v___y_1816_;
goto v___jp_2271_;
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2453_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2409_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2409_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_dec(v_a_2407_);
v___y_2272_ = v___y_1813_;
v___y_2273_ = v___y_1814_;
v___y_2274_ = v___y_1815_;
v___y_2275_ = v___y_1816_;
goto v___jp_2271_;
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2461_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2406_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2406_);
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
v___jp_1957_:
{
uint8_t v_genDiseq_1964_; 
v_genDiseq_1964_ = lean_ctor_get_uint8(v_config_1807_, sizeof(void*)*1 + 2);
if (v_genDiseq_1964_ == 0)
{
lean_dec_ref(v___x_1956_);
v___y_1935_ = v___y_1958_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1961_;
v___y_1938_ = v___y_1959_;
v___y_1939_ = v___y_1963_;
v___y_1940_ = v___y_1962_;
v___y_1941_ = v___x_1912_;
goto v___jp_1934_;
}
else
{
uint8_t v___x_1965_; 
v___x_1965_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1956_);
v___y_1935_ = v___y_1958_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1961_;
v___y_1938_ = v___y_1959_;
v___y_1939_ = v___y_1963_;
v___y_1940_ = v___y_1962_;
v___y_1941_ = v___x_1965_;
goto v___jp_1934_;
}
}
v___jp_1966_:
{
if (v___y_1974_ == 0)
{
lean_dec_ref(v___y_1968_);
v___y_1958_ = v___y_1969_;
v___y_1959_ = v___y_1972_;
v___y_1960_ = v___y_1971_;
v___y_1961_ = v___y_1970_;
v___y_1962_ = v___y_1973_;
v___y_1963_ = v___y_1967_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_1975_; 
lean_dec_ref(v___x_1956_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___y_1968_);
return v___x_1975_;
}
}
v___jp_1976_:
{
uint8_t v___x_1984_; 
v___x_1984_ = l_Lean_Exception_isInterrupt(v_a_1983_);
if (v___x_1984_ == 0)
{
uint8_t v___x_1985_; 
lean_inc_ref(v_a_1983_);
v___x_1985_ = l_Lean_Exception_isRuntime(v_a_1983_);
v___y_1967_ = v___y_1977_;
v___y_1968_ = v_a_1983_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1979_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___x_1985_;
goto v___jp_1966_;
}
else
{
v___y_1967_ = v___y_1977_;
v___y_1968_ = v_a_1983_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1979_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___x_1984_;
goto v___jp_1966_;
}
}
v___jp_1986_:
{
if (lean_obj_tag(v___y_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_a_1995_ = lean_ctor_get(v___y_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___y_1994_, 1);
v___x_1996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_1997_ = l_Lean_Expr_isConstOf(v_a_1995_, v___x_1996_);
lean_dec(v_a_1995_);
if (v___x_1997_ == 0)
{
lean_dec_ref(v___y_1988_);
v___y_1958_ = v___y_1989_;
v___y_1959_ = v___y_1992_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1990_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1987_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_1998_; 
lean_inc_ref(v___y_1988_);
v___x_1998_ = l_Lean_Meta_mkEqRefl(v___y_1988_, v___y_1991_, v___y_1990_, v___y_1993_, v___y_1987_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
lean_inc(v_mvarId_1808_);
v___x_2000_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_1991_, v___y_1990_, v___y_1993_, v___y_1987_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v_nargs_2002_; lean_object* v___x_2003_; lean_object* v_dummy_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v_nargs_2002_ = l_Lean_Expr_getAppNumArgs(v___y_1988_);
v___x_2003_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2002_);
v___x_2005_ = lean_mk_array(v_nargs_2002_, v_dummy_2004_);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_sub(v_nargs_2002_, v___x_2006_);
lean_dec(v_nargs_2002_);
v___x_2008_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1988_, v___x_2005_, v___x_2007_);
v___x_2009_ = lean_array_push(v___x_2008_, v_a_1999_);
v___x_2010_ = l_Lean_mkAppN(v___x_2003_, v___x_2009_);
lean_dec_ref(v___x_2009_);
lean_inc(v_val_1839_);
v___x_2011_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2012_ = l_Lean_Meta_mkAbsurd(v_a_2001_, v___x_2011_, v___x_2010_, v___y_1991_, v___y_1990_, v___y_1993_, v___y_1987_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
lean_inc(v_mvarId_1808_);
v___x_2014_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2013_, v___y_1990_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v___x_1956_);
lean_dec(v_val_1839_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v___x_2014_, 0);
lean_dec(v_unused_2024_);
v___x_2016_ = v___x_2014_;
v_isShared_2017_ = v_isSharedCheck_2023_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v___x_2014_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2023_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = lean_box(v___x_1818_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 1);
lean_ctor_set(v___x_2016_, 0, v___x_2018_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v___x_1843_);
v_a_1825_ = v___x_2021_;
goto v___jp_1824_;
}
}
}
else
{
lean_object* v_a_2025_; 
v_a_2025_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2014_, 1);
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v_a_1983_ = v_a_2025_;
goto v___jp_1976_;
}
}
else
{
lean_object* v_a_2026_; 
v_a_2026_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2012_, 1);
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v_a_1983_ = v_a_2026_;
goto v___jp_1976_;
}
}
else
{
lean_object* v_a_2027_; 
lean_dec(v_a_1999_);
lean_dec_ref(v___y_1988_);
v_a_2027_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2000_, 1);
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v_a_1983_ = v_a_2027_;
goto v___jp_1976_;
}
}
else
{
lean_object* v_a_2028_; 
lean_dec_ref(v___y_1988_);
v_a_2028_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_1998_, 1);
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v_a_1983_ = v_a_2028_;
goto v___jp_1976_;
}
}
}
else
{
lean_object* v_a_2029_; 
lean_dec_ref(v___y_1988_);
v_a_2029_ = lean_ctor_get(v___y_1994_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___y_1994_, 1);
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v_a_1983_ = v_a_2029_;
goto v___jp_1976_;
}
}
v___jp_2030_:
{
lean_object* v___x_2037_; 
lean_inc_ref(v___x_1956_);
v___x_2037_ = l_Lean_Meta_mkDecide(v___x_1956_, v___y_2034_, v___y_2033_, v___y_2036_, v___y_2031_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; uint8_t v_transparency_2040_; uint8_t v___x_2041_; uint8_t v___x_2042_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2039_ = l_Lean_Meta_Context_config(v___y_2034_);
v_transparency_2040_ = lean_ctor_get_uint8(v___x_2039_, 9);
lean_dec_ref(v___x_2039_);
v___x_2041_ = 1;
v___x_2042_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2040_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_object* v_keyedConfig_2043_; uint8_t v_trackZetaDelta_2044_; lean_object* v_zetaDeltaSet_2045_; lean_object* v_lctx_2046_; lean_object* v_localInstances_2047_; lean_object* v_defEqCtx_x3f_2048_; lean_object* v_synthPendingDepth_2049_; lean_object* v_customCanUnfoldPredicate_x3f_2050_; uint8_t v_univApprox_2051_; uint8_t v_inTypeClassResolution_2052_; uint8_t v_cacheInferType_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_keyedConfig_2043_ = lean_ctor_get(v___y_2034_, 0);
v_trackZetaDelta_2044_ = lean_ctor_get_uint8(v___y_2034_, sizeof(void*)*7);
v_zetaDeltaSet_2045_ = lean_ctor_get(v___y_2034_, 1);
v_lctx_2046_ = lean_ctor_get(v___y_2034_, 2);
v_localInstances_2047_ = lean_ctor_get(v___y_2034_, 3);
v_defEqCtx_x3f_2048_ = lean_ctor_get(v___y_2034_, 4);
v_synthPendingDepth_2049_ = lean_ctor_get(v___y_2034_, 5);
v_customCanUnfoldPredicate_x3f_2050_ = lean_ctor_get(v___y_2034_, 6);
v_univApprox_2051_ = lean_ctor_get_uint8(v___y_2034_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2052_ = lean_ctor_get_uint8(v___y_2034_, sizeof(void*)*7 + 2);
v_cacheInferType_2053_ = lean_ctor_get_uint8(v___y_2034_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2043_);
v___x_2054_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2041_, v_keyedConfig_2043_);
lean_inc(v_customCanUnfoldPredicate_x3f_2050_);
lean_inc(v_synthPendingDepth_2049_);
lean_inc(v_defEqCtx_x3f_2048_);
lean_inc_ref(v_localInstances_2047_);
lean_inc_ref(v_lctx_2046_);
lean_inc(v_zetaDeltaSet_2045_);
v___x_2055_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v_zetaDeltaSet_2045_);
lean_ctor_set(v___x_2055_, 2, v_lctx_2046_);
lean_ctor_set(v___x_2055_, 3, v_localInstances_2047_);
lean_ctor_set(v___x_2055_, 4, v_defEqCtx_x3f_2048_);
lean_ctor_set(v___x_2055_, 5, v_synthPendingDepth_2049_);
lean_ctor_set(v___x_2055_, 6, v_customCanUnfoldPredicate_x3f_2050_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*7, v_trackZetaDelta_2044_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*7 + 1, v_univApprox_2051_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2052_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*7 + 3, v_cacheInferType_2053_);
lean_inc(v___y_2031_);
lean_inc_ref(v___y_2036_);
lean_inc(v___y_2033_);
lean_inc(v_a_2038_);
v___x_2056_ = lean_whnf(v_a_2038_, v___x_2055_, v___y_2033_, v___y_2036_, v___y_2031_);
v___y_1987_ = v___y_2031_;
v___y_1988_ = v_a_2038_;
v___y_1989_ = v___y_2032_;
v___y_1990_ = v___y_2033_;
v___y_1991_ = v___y_2034_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___y_2036_;
v___y_1994_ = v___x_2056_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2057_; 
lean_inc(v___y_2031_);
lean_inc_ref(v___y_2036_);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2034_);
lean_inc(v_a_2038_);
v___x_2057_ = lean_whnf(v_a_2038_, v___y_2034_, v___y_2033_, v___y_2036_, v___y_2031_);
v___y_1987_ = v___y_2031_;
v___y_1988_ = v_a_2038_;
v___y_1989_ = v___y_2032_;
v___y_1990_ = v___y_2033_;
v___y_1991_ = v___y_2034_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___y_2036_;
v___y_1994_ = v___x_2057_;
goto v___jp_1986_;
}
}
else
{
lean_object* v_a_2058_; 
v_a_2058_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2037_, 1);
v___y_1977_ = v___y_2031_;
v___y_1978_ = v___y_2032_;
v___y_1979_ = v___y_2033_;
v___y_1980_ = v___y_2034_;
v___y_1981_ = v___y_2035_;
v___y_1982_ = v___y_2036_;
v_a_1983_ = v_a_2058_;
goto v___jp_1976_;
}
}
v___jp_2059_:
{
if (v___y_2066_ == 0)
{
v___y_1958_ = v___y_2061_;
v___y_1959_ = v___y_2064_;
v___y_1960_ = v___y_2063_;
v___y_1961_ = v___y_2062_;
v___y_1962_ = v___y_2065_;
v___y_1963_ = v___y_2060_;
goto v___jp_1957_;
}
else
{
v___y_2031_ = v___y_2060_;
v___y_2032_ = v___y_2061_;
v___y_2033_ = v___y_2062_;
v___y_2034_ = v___y_2063_;
v___y_2035_ = v___y_2064_;
v___y_2036_ = v___y_2065_;
goto v___jp_2030_;
}
}
v___jp_2067_:
{
if (v___y_2075_ == 0)
{
lean_dec_ref(v___y_2073_);
v___y_2060_ = v___y_2068_;
v___y_2061_ = v___y_2069_;
v___y_2062_ = v___y_2070_;
v___y_2063_ = v___y_2071_;
v___y_2064_ = v___y_2072_;
v___y_2065_ = v___y_2074_;
v___y_2066_ = v___x_1912_;
goto v___jp_2059_;
}
else
{
uint8_t v___x_2076_; 
v___x_2076_ = l_Lean_Expr_hasFVar(v___y_2073_);
lean_dec_ref(v___y_2073_);
if (v___x_2076_ == 0)
{
v___y_2031_ = v___y_2068_;
v___y_2032_ = v___y_2069_;
v___y_2033_ = v___y_2070_;
v___y_2034_ = v___y_2071_;
v___y_2035_ = v___y_2072_;
v___y_2036_ = v___y_2074_;
goto v___jp_2030_;
}
else
{
v___y_2060_ = v___y_2068_;
v___y_2061_ = v___y_2069_;
v___y_2062_ = v___y_2070_;
v___y_2063_ = v___y_2071_;
v___y_2064_ = v___y_2072_;
v___y_2065_ = v___y_2074_;
v___y_2066_ = v___x_1912_;
goto v___jp_2059_;
}
}
}
v___jp_2077_:
{
lean_object* v___x_2085_; 
lean_inc_ref(v___x_1956_);
v___x_2085_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1956_, v___y_2080_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; uint8_t v___x_2087_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2087_ = l_Lean_Expr_hasMVar(v_a_2086_);
if (v___x_2087_ == 0)
{
v___y_2068_ = v___y_2078_;
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v___y_2082_;
v___y_2073_ = v_a_2086_;
v___y_2074_ = v___y_2083_;
v___y_2075_ = v___y_2084_;
goto v___jp_2067_;
}
else
{
v___y_2068_ = v___y_2078_;
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v___y_2082_;
v___y_2073_ = v_a_2086_;
v___y_2074_ = v___y_2083_;
v___y_2075_ = v___x_1912_;
goto v___jp_2067_;
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v___x_1956_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2088_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2085_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2085_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
v___jp_2096_:
{
if (v___y_2103_ == 0)
{
v___y_1958_ = v___y_2098_;
v___y_1959_ = v___y_2101_;
v___y_1960_ = v___y_2100_;
v___y_1961_ = v___y_2099_;
v___y_1962_ = v___y_2102_;
v___y_1963_ = v___y_2097_;
goto v___jp_1957_;
}
else
{
v___y_2078_ = v___y_2097_;
v___y_2079_ = v___y_2098_;
v___y_2080_ = v___y_2099_;
v___y_2081_ = v___y_2100_;
v___y_2082_ = v___y_2101_;
v___y_2083_ = v___y_2102_;
v___y_2084_ = v___y_2103_;
goto v___jp_2077_;
}
}
v___jp_2104_:
{
uint8_t v_useDecide_2111_; 
v_useDecide_2111_ = lean_ctor_get_uint8(v_config_1807_, sizeof(void*)*1);
if (v_useDecide_2111_ == 0)
{
v___y_2097_ = v___y_2110_;
v___y_2098_ = v_isHEq_2106_;
v___y_2099_ = v___y_2108_;
v___y_2100_ = v___y_2107_;
v___y_2101_ = v___y_2105_;
v___y_2102_ = v___y_2109_;
v___y_2103_ = v___x_1912_;
goto v___jp_2096_;
}
else
{
uint8_t v___x_2112_; 
v___x_2112_ = l_Lean_Expr_hasFVar(v___x_1956_);
if (v___x_2112_ == 0)
{
v___y_2078_ = v___y_2110_;
v___y_2079_ = v_isHEq_2106_;
v___y_2080_ = v___y_2108_;
v___y_2081_ = v___y_2107_;
v___y_2082_ = v___y_2105_;
v___y_2083_ = v___y_2109_;
v___y_2084_ = v_useDecide_2111_;
goto v___jp_2077_;
}
else
{
v___y_2097_ = v___y_2110_;
v___y_2098_ = v_isHEq_2106_;
v___y_2099_ = v___y_2108_;
v___y_2100_ = v___y_2107_;
v___y_2101_ = v___y_2105_;
v___y_2102_ = v___y_2109_;
v___y_2103_ = v___x_1912_;
goto v___jp_2096_;
}
}
}
v___jp_2113_:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Meta_isExprDefEq(v___y_2116_, v___y_2117_, v___y_2119_, v___y_2118_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; uint8_t v___x_2123_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = lean_unbox(v_a_2122_);
lean_dec(v_a_2122_);
if (v___x_2123_ == 0)
{
v___y_2105_ = v___y_2120_;
v_isHEq_2106_ = v___x_1818_;
v___y_2107_ = v___y_2119_;
v___y_2108_ = v___y_2118_;
v___y_2109_ = v___y_2114_;
v___y_2110_ = v___y_2115_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2124_; 
lean_dec_ref(v___x_1956_);
lean_dec_ref(v_config_1807_);
lean_inc(v_mvarId_1808_);
v___x_2124_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_2119_, v___y_2118_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2127_ = l_Lean_Meta_mkEqOfHEq(v___x_2126_, v___x_1818_, v___y_2119_, v___y_2118_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = l_Lean_Meta_mkNoConfusion(v_a_2125_, v_a_2128_, v___y_2119_, v___y_2118_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2130_, v___y_2118_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec_ref_known(v___x_2131_, 1);
v___x_2132_ = lean_box(v___x_1818_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set(v___x_2134_, 1, v___x_1843_);
v_a_1825_ = v___x_2134_;
goto v___jp_1824_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_2135_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2131_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2131_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2143_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2129_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2129_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_a_2125_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2151_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2127_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2127_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2159_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2124_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2124_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec_ref(v___x_1956_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2167_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2121_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2121_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
v___jp_2175_:
{
lean_object* v___x_2181_; 
lean_inc_ref(v___x_1956_);
v___x_2181_ = l_Lean_Meta_matchHEq_x3f(v___x_1956_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2181_, 1);
if (lean_obj_tag(v_a_2182_) == 1)
{
lean_object* v_val_2183_; lean_object* v_snd_2184_; lean_object* v_snd_2185_; lean_object* v_fst_2186_; lean_object* v_fst_2187_; lean_object* v_fst_2188_; lean_object* v_snd_2189_; lean_object* v___x_2190_; 
v_val_2183_ = lean_ctor_get(v_a_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref_known(v_a_2182_, 1);
v_snd_2184_ = lean_ctor_get(v_val_2183_, 1);
lean_inc(v_snd_2184_);
v_snd_2185_ = lean_ctor_get(v_snd_2184_, 1);
lean_inc(v_snd_2185_);
v_fst_2186_ = lean_ctor_get(v_val_2183_, 0);
lean_inc(v_fst_2186_);
lean_dec(v_val_2183_);
v_fst_2187_ = lean_ctor_get(v_snd_2184_, 0);
lean_inc(v_fst_2187_);
lean_dec(v_snd_2184_);
v_fst_2188_ = lean_ctor_get(v_snd_2185_, 0);
lean_inc(v_fst_2188_);
v_snd_2189_ = lean_ctor_get(v_snd_2185_, 1);
lean_inc(v_snd_2189_);
lean_dec(v_snd_2185_);
v___x_2190_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2187_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
if (lean_obj_tag(v_a_2191_) == 1)
{
lean_object* v_val_2192_; lean_object* v___x_2193_; 
v_val_2192_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_val_2192_);
lean_dec_ref_known(v_a_2191_, 1);
v___x_2193_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2189_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
if (lean_obj_tag(v_a_2194_) == 1)
{
lean_object* v_toConstantVal_2195_; lean_object* v_val_2196_; lean_object* v_toConstantVal_2197_; lean_object* v_name_2198_; lean_object* v_name_2199_; uint8_t v___x_2200_; 
v_toConstantVal_2195_ = lean_ctor_get(v_val_2192_, 0);
lean_inc_ref(v_toConstantVal_2195_);
lean_dec(v_val_2192_);
v_val_2196_ = lean_ctor_get(v_a_2194_, 0);
lean_inc(v_val_2196_);
lean_dec_ref_known(v_a_2194_, 1);
v_toConstantVal_2197_ = lean_ctor_get(v_val_2196_, 0);
lean_inc_ref(v_toConstantVal_2197_);
lean_dec(v_val_2196_);
v_name_2198_ = lean_ctor_get(v_toConstantVal_2195_, 0);
lean_inc(v_name_2198_);
lean_dec_ref(v_toConstantVal_2195_);
v_name_2199_ = lean_ctor_get(v_toConstantVal_2197_, 0);
lean_inc(v_name_2199_);
lean_dec_ref(v_toConstantVal_2197_);
v___x_2200_ = lean_name_eq(v_name_2198_, v_name_2199_);
lean_dec(v_name_2199_);
lean_dec(v_name_2198_);
if (v___x_2200_ == 0)
{
v___y_2114_ = v___y_2179_;
v___y_2115_ = v___y_2180_;
v___y_2116_ = v_fst_2186_;
v___y_2117_ = v_fst_2188_;
v___y_2118_ = v___y_2178_;
v___y_2119_ = v___y_2177_;
v___y_2120_ = v_isEq_2176_;
goto v___jp_2113_;
}
else
{
if (v___x_1912_ == 0)
{
lean_dec(v_fst_2188_);
lean_dec(v_fst_2186_);
v___y_2105_ = v_isEq_2176_;
v_isHEq_2106_ = v___x_1818_;
v___y_2107_ = v___y_2177_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
goto v___jp_2104_;
}
else
{
v___y_2114_ = v___y_2179_;
v___y_2115_ = v___y_2180_;
v___y_2116_ = v_fst_2186_;
v___y_2117_ = v_fst_2188_;
v___y_2118_ = v___y_2178_;
v___y_2119_ = v___y_2177_;
v___y_2120_ = v_isEq_2176_;
goto v___jp_2113_;
}
}
}
else
{
lean_dec(v_a_2194_);
lean_dec(v_val_2192_);
lean_dec(v_fst_2188_);
lean_dec(v_fst_2186_);
v___y_2105_ = v_isEq_2176_;
v_isHEq_2106_ = v___x_1818_;
v___y_2107_ = v___y_2177_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
goto v___jp_2104_;
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_val_2192_);
lean_dec(v_fst_2188_);
lean_dec(v_fst_2186_);
lean_dec_ref(v___x_1956_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2201_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2193_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2193_);
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
lean_dec(v_a_2191_);
lean_dec(v_snd_2189_);
lean_dec(v_fst_2188_);
lean_dec(v_fst_2186_);
v___y_2105_ = v_isEq_2176_;
v_isHEq_2106_ = v___x_1818_;
v___y_2107_ = v___y_2177_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
goto v___jp_2104_;
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_snd_2189_);
lean_dec(v_fst_2188_);
lean_dec(v_fst_2186_);
lean_dec_ref(v___x_1956_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2209_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2190_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2190_);
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
else
{
lean_dec(v_a_2182_);
v___y_2105_ = v_isEq_2176_;
v_isHEq_2106_ = v___x_1912_;
v___y_2107_ = v___y_2177_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
v___y_2110_ = v___y_2180_;
goto v___jp_2104_;
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v___x_1956_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2217_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2181_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2181_);
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
v___jp_2225_:
{
lean_object* v___x_2230_; 
lean_inc_ref(v___x_1956_);
v___x_2230_ = l_Lean_Meta_matchEq_x3f(v___x_1956_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
if (lean_obj_tag(v_a_2231_) == 1)
{
lean_object* v_val_2232_; lean_object* v_snd_2233_; lean_object* v_fst_2234_; lean_object* v_snd_2235_; lean_object* v___x_2236_; 
v_val_2232_ = lean_ctor_get(v_a_2231_, 0);
lean_inc(v_val_2232_);
lean_dec_ref_known(v_a_2231_, 1);
v_snd_2233_ = lean_ctor_get(v_val_2232_, 1);
lean_inc(v_snd_2233_);
lean_dec(v_val_2232_);
v_fst_2234_ = lean_ctor_get(v_snd_2233_, 0);
lean_inc(v_fst_2234_);
v_snd_2235_ = lean_ctor_get(v_snd_2233_, 1);
lean_inc(v_snd_2235_);
lean_dec(v_snd_2233_);
v___x_2236_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2234_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
if (lean_obj_tag(v_a_2237_) == 1)
{
lean_object* v_val_2238_; lean_object* v___x_2239_; 
v_val_2238_ = lean_ctor_get(v_a_2237_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v_a_2237_, 1);
v___x_2239_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2235_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
if (lean_obj_tag(v_a_2240_) == 1)
{
lean_object* v_toConstantVal_2241_; lean_object* v_val_2242_; lean_object* v_toConstantVal_2243_; lean_object* v_name_2244_; lean_object* v_name_2245_; uint8_t v___x_2246_; 
v_toConstantVal_2241_ = lean_ctor_get(v_val_2238_, 0);
lean_inc_ref(v_toConstantVal_2241_);
lean_dec(v_val_2238_);
v_val_2242_ = lean_ctor_get(v_a_2240_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v_a_2240_, 1);
v_toConstantVal_2243_ = lean_ctor_get(v_val_2242_, 0);
lean_inc_ref(v_toConstantVal_2243_);
lean_dec(v_val_2242_);
v_name_2244_ = lean_ctor_get(v_toConstantVal_2241_, 0);
lean_inc(v_name_2244_);
lean_dec_ref(v_toConstantVal_2241_);
v_name_2245_ = lean_ctor_get(v_toConstantVal_2243_, 0);
lean_inc(v_name_2245_);
lean_dec_ref(v_toConstantVal_2243_);
v___x_2246_ = lean_name_eq(v_name_2244_, v_name_2245_);
lean_dec(v_name_2245_);
lean_dec(v_name_2244_);
if (v___x_2246_ == 0)
{
lean_dec_ref(v___x_1956_);
lean_dec_ref(v_config_1807_);
v___y_1845_ = v___y_2229_;
v___y_1846_ = v___y_2228_;
v___y_1847_ = v___y_2227_;
v___y_1848_ = v___y_2226_;
goto v___jp_1844_;
}
else
{
if (v___x_1912_ == 0)
{
lean_del_object(v___x_1841_);
v_isEq_2176_ = v___x_1818_;
v___y_2177_ = v___y_2226_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
goto v___jp_2175_;
}
else
{
lean_dec_ref(v___x_1956_);
lean_dec_ref(v_config_1807_);
v___y_1845_ = v___y_2229_;
v___y_1846_ = v___y_2228_;
v___y_1847_ = v___y_2227_;
v___y_1848_ = v___y_2226_;
goto v___jp_1844_;
}
}
}
else
{
lean_dec(v_a_2240_);
lean_dec(v_val_2238_);
lean_del_object(v___x_1841_);
v_isEq_2176_ = v___x_1818_;
v___y_2177_ = v___y_2226_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
goto v___jp_2175_;
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_val_2238_);
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2247_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2239_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2239_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_dec(v_a_2237_);
lean_dec(v_snd_2235_);
lean_del_object(v___x_1841_);
v_isEq_2176_ = v___x_1818_;
v___y_2177_ = v___y_2226_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
goto v___jp_2175_;
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_snd_2235_);
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2255_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2236_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2236_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_dec(v_a_2231_);
lean_del_object(v___x_1841_);
v_isEq_2176_ = v___x_1912_;
v___y_2177_ = v___y_2226_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
v___y_2180_ = v___y_2229_;
goto v___jp_2175_;
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2263_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2230_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2230_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
v___jp_2271_:
{
lean_object* v___x_2276_; 
lean_inc_ref(v___x_1956_);
v___x_2276_ = l_Lean_refutableHasNotBit_x3f(v___x_1956_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
if (lean_obj_tag(v_a_2277_) == 1)
{
lean_object* v_val_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec_ref(v_config_1807_);
v_val_2278_ = lean_ctor_get(v_a_2277_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_a_2277_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2280_ = v_a_2277_;
v_isShared_2281_ = v_isSharedCheck_2317_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_val_2278_);
lean_dec(v_a_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2317_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; 
lean_inc(v_mvarId_1808_);
v___x_2282_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2285_ = l_Lean_Meta_mkAbsurd(v_a_2283_, v_val_2278_, v___x_2284_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2286_, v___y_2273_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
lean_dec_ref_known(v___x_2287_, 1);
v___x_2288_ = lean_box(v___x_1818_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2288_);
v___x_2290_ = v___x_2280_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___x_1843_);
v_a_1825_ = v___x_2291_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_del_object(v___x_2280_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_2293_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2287_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2287_);
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
lean_del_object(v___x_2280_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2301_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2285_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2285_);
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
lean_del_object(v___x_2280_);
lean_dec(v_val_2278_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2309_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2282_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2282_);
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
}
else
{
lean_object* v___x_2318_; 
lean_dec(v_a_2277_);
lean_inc_ref(v___x_1956_);
v___x_2318_ = l_Lean_Meta_matchNe_x3f(v___x_1956_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
if (lean_obj_tag(v_a_2319_) == 1)
{
lean_object* v_val_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2389_; 
v_val_2320_ = lean_ctor_get(v_a_2319_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_a_2319_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2322_ = v_a_2319_;
v_isShared_2323_ = v_isSharedCheck_2389_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_val_2320_);
lean_dec(v_a_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2389_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v_snd_2324_; lean_object* v_fst_2325_; lean_object* v_snd_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2388_; 
v_snd_2324_ = lean_ctor_get(v_val_2320_, 1);
lean_inc(v_snd_2324_);
lean_dec(v_val_2320_);
v_fst_2325_ = lean_ctor_get(v_snd_2324_, 0);
v_snd_2326_ = lean_ctor_get(v_snd_2324_, 1);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_snd_2324_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2328_ = v_snd_2324_;
v_isShared_2329_ = v_isSharedCheck_2388_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_snd_2326_);
lean_inc(v_fst_2325_);
lean_dec(v_snd_2324_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2388_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; 
lean_inc(v_fst_2325_);
v___x_2330_ = l_Lean_Meta_isExprDefEq(v_fst_2325_, v_snd_2326_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; uint8_t v___x_2332_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = lean_unbox(v_a_2331_);
lean_dec(v_a_2331_);
if (v___x_2332_ == 0)
{
lean_del_object(v___x_2328_);
lean_dec(v_fst_2325_);
lean_del_object(v___x_2322_);
v___y_2226_ = v___y_2272_;
v___y_2227_ = v___y_2273_;
v___y_2228_ = v___y_2274_;
v___y_2229_ = v___y_2275_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2333_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec_ref(v_config_1807_);
lean_inc(v_mvarId_1808_);
v___x_2333_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v___x_2335_ = l_Lean_Meta_mkEqRefl(v_fst_2325_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2338_ = l_Lean_Meta_mkAbsurd(v_a_2334_, v_a_2336_, v___x_2337_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2339_, v___y_2273_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
lean_dec_ref_known(v___x_2340_, 1);
v___x_2341_ = lean_box(v___x_1818_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2341_);
v___x_2343_ = v___x_2322_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v___x_1843_);
lean_ctor_set(v___x_2328_, 0, v___x_2343_);
v___x_2345_ = v___x_2328_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_1843_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
v_a_1825_ = v___x_2345_;
goto v___jp_1824_;
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_del_object(v___x_2328_);
lean_del_object(v___x_2322_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_2348_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2340_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2340_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_del_object(v___x_2328_);
lean_del_object(v___x_2322_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2356_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2338_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2338_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_a_2334_);
lean_del_object(v___x_2328_);
lean_del_object(v___x_2322_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2364_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2335_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2335_);
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
lean_del_object(v___x_2328_);
lean_dec(v_fst_2325_);
lean_del_object(v___x_2322_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2372_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2333_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2333_);
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
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_del_object(v___x_2328_);
lean_dec(v_fst_2325_);
lean_del_object(v___x_2322_);
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2380_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2330_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2330_);
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
}
else
{
lean_dec(v_a_2319_);
v___y_2226_ = v___y_2272_;
v___y_2227_ = v___y_2273_;
v___y_2228_ = v___y_2274_;
v___y_2229_ = v___y_2275_;
goto v___jp_2225_;
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2390_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2318_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2318_);
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
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2398_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2276_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2276_);
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
}
else
{
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_1833_ = v___x_1884_;
goto v___jp_1832_;
}
v___jp_1844_:
{
lean_object* v___x_1849_; 
lean_inc(v_mvarId_1808_);
v___x_1849_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_1848_, v___y_1847_, v___y_1846_, v___y_1845_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_1852_ = l_Lean_Meta_mkNoConfusion(v_a_1850_, v___x_1851_, v___y_1848_, v___y_1847_, v___y_1846_, v___y_1845_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_1853_, v___y_1847_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec_ref_known(v___x_1854_, 1);
v___x_1855_ = lean_box(v___x_1818_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1855_);
v___x_1857_ = v___x_1841_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___x_1843_);
v_a_1825_ = v___x_1858_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1841_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_1860_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1854_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1854_);
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
lean_del_object(v___x_1841_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_1868_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1852_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1852_);
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
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_1876_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1849_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1849_);
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
v___jp_1885_:
{
lean_object* v_searchFuel_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_searchFuel_1890_ = lean_ctor_get(v_config_1807_, 0);
v___x_1891_ = l_Lean_LocalDecl_fvarId(v_val_1839_);
lean_dec(v_val_1839_);
lean_inc(v_searchFuel_1890_);
lean_inc(v_mvarId_1808_);
v___x_1892_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1808_, v___x_1891_, v_searchFuel_1890_, v___y_1888_, v___y_1886_, v___y_1889_, v___y_1887_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; uint8_t v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1894_ = lean_unbox(v_a_1893_);
lean_dec(v_a_1893_);
if (v___x_1894_ == 0)
{
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_1833_ = v___x_1884_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v___x_1895_ = lean_box(v___x_1818_);
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v___x_1843_);
v_a_1825_ = v___x_1897_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_1898_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1892_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1892_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
v___jp_1906_:
{
if (v___y_1911_ == 0)
{
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_1833_ = v___x_1884_;
goto v___jp_1832_;
}
else
{
v___y_1886_ = v___y_1907_;
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1909_;
v___y_1889_ = v___y_1910_;
goto v___jp_1885_;
}
}
v___jp_1913_:
{
if (v___y_1915_ == 0)
{
v___y_1886_ = v___y_1914_;
v___y_1887_ = v___y_1916_;
v___y_1888_ = v___y_1917_;
v___y_1889_ = v___y_1918_;
goto v___jp_1885_;
}
else
{
v___y_1907_ = v___y_1914_;
v___y_1908_ = v___y_1916_;
v___y_1909_ = v___y_1917_;
v___y_1910_ = v___y_1918_;
v___y_1911_ = v___x_1912_;
goto v___jp_1906_;
}
}
v___jp_1919_:
{
if (v___y_1925_ == 0)
{
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1922_;
v___y_1909_ = v___y_1923_;
v___y_1910_ = v___y_1924_;
v___y_1911_ = v___x_1912_;
goto v___jp_1906_;
}
else
{
v___y_1914_ = v___y_1920_;
v___y_1915_ = v___y_1921_;
v___y_1916_ = v___y_1922_;
v___y_1917_ = v___y_1923_;
v___y_1918_ = v___y_1924_;
goto v___jp_1913_;
}
}
v___jp_1926_:
{
uint8_t v_emptyType_1933_; 
v_emptyType_1933_ = lean_ctor_get_uint8(v_config_1807_, sizeof(void*)*1 + 1);
if (v_emptyType_1933_ == 0)
{
v___y_1920_ = v___y_1930_;
v___y_1921_ = v___y_1927_;
v___y_1922_ = v___y_1932_;
v___y_1923_ = v___y_1929_;
v___y_1924_ = v___y_1931_;
v___y_1925_ = v___x_1912_;
goto v___jp_1919_;
}
else
{
if (v___y_1928_ == 0)
{
v___y_1914_ = v___y_1930_;
v___y_1915_ = v___y_1927_;
v___y_1916_ = v___y_1932_;
v___y_1917_ = v___y_1929_;
v___y_1918_ = v___y_1931_;
goto v___jp_1913_;
}
else
{
v___y_1920_ = v___y_1930_;
v___y_1921_ = v___y_1927_;
v___y_1922_ = v___y_1932_;
v___y_1923_ = v___y_1929_;
v___y_1924_ = v___y_1931_;
v___y_1925_ = v___x_1912_;
goto v___jp_1919_;
}
}
}
v___jp_1934_:
{
if (v___y_1941_ == 0)
{
v___y_1927_ = v___y_1935_;
v___y_1928_ = v___y_1938_;
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___y_1937_;
v___y_1931_ = v___y_1940_;
v___y_1932_ = v___y_1939_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1942_; 
lean_inc(v_val_1839_);
lean_inc(v_mvarId_1808_);
v___x_1942_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1808_, v_val_1839_, v___y_1936_, v___y_1937_, v___y_1940_, v___y_1939_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; uint8_t v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = lean_unbox(v_a_1943_);
lean_dec(v_a_1943_);
if (v___x_1944_ == 0)
{
v___y_1927_ = v___y_1935_;
v___y_1928_ = v___y_1938_;
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___y_1937_;
v___y_1931_ = v___y_1940_;
v___y_1932_ = v___y_1939_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec(v_val_1839_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v___x_1945_ = lean_box(v___x_1818_);
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v___x_1843_);
v_a_1825_ = v___x_1947_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_1948_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1942_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1942_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
}
v___jp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_a_1825_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1826_);
v___x_1828_ = v___x_1822_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_snd_1820_);
v___x_1828_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
v___jp_1832_:
{
lean_object* v___x_1834_; size_t v___x_1835_; size_t v___x_1836_; 
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1831_);
lean_ctor_set(v___x_1834_, 1, v_a_1833_);
v___x_1835_ = ((size_t)1ULL);
v___x_1836_ = lean_usize_add(v_i_1811_, v___x_1835_);
v_i_1811_ = v___x_1836_;
v_b_1812_ = v___x_1834_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2472_, lean_object* v_mvarId_2473_, lean_object* v_as_2474_, lean_object* v_sz_2475_, lean_object* v_i_2476_, lean_object* v_b_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
size_t v_sz_boxed_2483_; size_t v_i_boxed_2484_; lean_object* v_res_2485_; 
v_sz_boxed_2483_ = lean_unbox_usize(v_sz_2475_);
lean_dec(v_sz_2475_);
v_i_boxed_2484_ = lean_unbox_usize(v_i_2476_);
lean_dec(v_i_2476_);
v_res_2485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2472_, v_mvarId_2473_, v_as_2474_, v_sz_boxed_2483_, v_i_boxed_2484_, v_b_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v_as_2474_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2486_, lean_object* v_mvarId_2487_, lean_object* v_as_2488_, size_t v_sz_2489_, size_t v_i_2490_, lean_object* v_b_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
uint8_t v___x_2497_; 
v___x_2497_ = lean_usize_dec_lt(v_i_2490_, v_sz_2489_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_b_2491_);
return v___x_2498_;
}
else
{
lean_object* v_snd_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_3149_; 
v_snd_2499_ = lean_ctor_get(v_b_2491_, 1);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_b_2491_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v_b_2491_, 0);
lean_dec(v_unused_3150_);
v___x_2501_ = v_b_2491_;
v_isShared_2502_ = v_isSharedCheck_3149_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_snd_2499_);
lean_dec(v_b_2491_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_3149_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_a_2504_; lean_object* v___x_2510_; lean_object* v_a_2512_; lean_object* v_a_2517_; 
v___x_2510_ = lean_box(0);
v_a_2517_ = lean_array_uget(v_as_2488_, v_i_2490_);
if (lean_obj_tag(v_a_2517_) == 0)
{
lean_del_object(v___x_2501_);
v_a_2512_ = v_snd_2499_;
goto v___jp_2511_;
}
else
{
lean_object* v_val_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_3148_; 
v_val_2518_ = lean_ctor_get(v_a_2517_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_a_2517_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_2520_ = v_a_2517_;
v_isShared_2521_ = v_isSharedCheck_3148_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_val_2518_);
lean_dec(v_a_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_3148_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___x_2563_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; uint8_t v___y_2590_; uint8_t v___x_2591_; lean_object* v___y_2593_; lean_object* v___y_2594_; uint8_t v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2599_; lean_object* v___y_2600_; uint8_t v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; uint8_t v___y_2604_; uint8_t v___y_2606_; uint8_t v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; uint8_t v___y_2614_; uint8_t v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; uint8_t v___y_2620_; 
v___x_2522_ = lean_box(0);
v___x_2563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2591_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2518_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2635_; uint8_t v___y_2637_; uint8_t v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2646_; uint8_t v___y_2647_; uint8_t v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2653_; uint8_t v___y_2656_; uint8_t v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v_a_2662_; uint8_t v___y_2666_; uint8_t v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; uint8_t v___y_2710_; uint8_t v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; uint8_t v___y_2739_; uint8_t v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; uint8_t v___y_2745_; lean_object* v___y_2747_; uint8_t v___y_2748_; uint8_t v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; uint8_t v___y_2754_; uint8_t v___y_2757_; uint8_t v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; uint8_t v___y_2763_; uint8_t v___y_2776_; uint8_t v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; uint8_t v___y_2782_; uint8_t v___y_2784_; uint8_t v_isHEq_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; uint8_t v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; uint8_t v_isEq_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___x_3085_; 
v___x_2635_ = l_Lean_LocalDecl_type(v_val_2518_);
lean_inc_ref(v___x_2635_);
v___x_3085_ = l_Lean_Meta_matchNot_x3f(v___x_2635_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
if (lean_obj_tag(v_a_3086_) == 1)
{
lean_object* v_val_3087_; lean_object* v___x_3088_; 
v_val_3087_ = lean_ctor_get(v_a_3086_, 0);
lean_inc(v_val_3087_);
lean_dec_ref_known(v_a_3086_, 1);
v___x_3088_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3087_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
if (lean_obj_tag(v_a_3089_) == 1)
{
lean_object* v_val_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec_ref(v_config_2486_);
v_val_3090_ = lean_ctor_get(v_a_3089_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_a_3089_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3092_ = v_a_3089_;
v_isShared_3093_ = v_isSharedCheck_3131_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_val_3090_);
lean_dec(v_a_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3131_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; 
lean_inc(v_mvarId_2487_);
v___x_3094_ = l_Lean_MVarId_getType(v_mvarId_2487_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v___x_3094_, 1);
v___x_3096_ = l_Lean_LocalDecl_toExpr(v_val_2518_);
v___x_3097_ = l_Lean_mkFVar(v_val_3090_);
v___x_3098_ = l_Lean_Expr_app___override(v___x_3096_, v___x_3097_);
v___x_3099_ = l_Lean_Meta_mkFalseElim(v_a_3095_, v___x_3098_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3101_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3099_, 1);
v___x_3101_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2487_, v_a_3100_, v___y_2493_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
lean_dec_ref_known(v___x_3101_, 1);
v___x_3102_ = lean_box(v___x_2497_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3102_);
v___x_3104_ = v___x_3092_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set(v___x_3105_, 1, v___x_2522_);
v_a_2504_ = v___x_3105_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_del_object(v___x_3092_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
v_a_3107_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3101_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3101_);
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
lean_del_object(v___x_3092_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_3115_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3099_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3099_);
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
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_del_object(v___x_3092_);
lean_dec(v_val_3090_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_3123_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3094_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3094_);
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
}
else
{
lean_dec(v_a_3089_);
v___y_2951_ = v___y_2492_;
v___y_2952_ = v___y_2493_;
v___y_2953_ = v___y_2494_;
v___y_2954_ = v___y_2495_;
goto v___jp_2950_;
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_3132_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3088_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3088_);
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
}
else
{
lean_dec(v_a_3086_);
v___y_2951_ = v___y_2492_;
v___y_2952_ = v___y_2493_;
v___y_2953_ = v___y_2494_;
v___y_2954_ = v___y_2495_;
goto v___jp_2950_;
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_3140_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3085_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3085_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
v___jp_2636_:
{
uint8_t v_genDiseq_2643_; 
v_genDiseq_2643_ = lean_ctor_get_uint8(v_config_2486_, sizeof(void*)*1 + 2);
if (v_genDiseq_2643_ == 0)
{
lean_dec_ref(v___x_2635_);
v___y_2614_ = v___y_2637_;
v___y_2615_ = v___y_2638_;
v___y_2616_ = v___y_2642_;
v___y_2617_ = v___y_2639_;
v___y_2618_ = v___y_2640_;
v___y_2619_ = v___y_2641_;
v___y_2620_ = v___x_2591_;
goto v___jp_2613_;
}
else
{
uint8_t v___x_2644_; 
v___x_2644_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2635_);
v___y_2614_ = v___y_2637_;
v___y_2615_ = v___y_2638_;
v___y_2616_ = v___y_2642_;
v___y_2617_ = v___y_2639_;
v___y_2618_ = v___y_2640_;
v___y_2619_ = v___y_2641_;
v___y_2620_ = v___x_2644_;
goto v___jp_2613_;
}
}
v___jp_2645_:
{
if (v___y_2653_ == 0)
{
lean_dec_ref(v___y_2646_);
v___y_2637_ = v___y_2647_;
v___y_2638_ = v___y_2648_;
v___y_2639_ = v___y_2650_;
v___y_2640_ = v___y_2649_;
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2652_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2654_; 
lean_dec_ref(v___x_2635_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v___x_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___y_2646_);
return v___x_2654_;
}
}
v___jp_2655_:
{
uint8_t v___x_2663_; 
v___x_2663_ = l_Lean_Exception_isInterrupt(v_a_2662_);
if (v___x_2663_ == 0)
{
uint8_t v___x_2664_; 
lean_inc_ref(v_a_2662_);
v___x_2664_ = l_Lean_Exception_isRuntime(v_a_2662_);
v___y_2646_ = v_a_2662_;
v___y_2647_ = v___y_2656_;
v___y_2648_ = v___y_2657_;
v___y_2649_ = v___y_2659_;
v___y_2650_ = v___y_2658_;
v___y_2651_ = v___y_2660_;
v___y_2652_ = v___y_2661_;
v___y_2653_ = v___x_2664_;
goto v___jp_2645_;
}
else
{
v___y_2646_ = v_a_2662_;
v___y_2647_ = v___y_2656_;
v___y_2648_ = v___y_2657_;
v___y_2649_ = v___y_2659_;
v___y_2650_ = v___y_2658_;
v___y_2651_ = v___y_2660_;
v___y_2652_ = v___y_2661_;
v___y_2653_ = v___x_2663_;
goto v___jp_2645_;
}
}
v___jp_2665_:
{
if (lean_obj_tag(v___y_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v_a_2674_ = lean_ctor_get(v___y_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___y_2673_, 1);
v___x_2675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2676_ = l_Lean_Expr_isConstOf(v_a_2674_, v___x_2675_);
lean_dec(v_a_2674_);
if (v___x_2676_ == 0)
{
lean_dec_ref(v___y_2670_);
v___y_2637_ = v___y_2666_;
v___y_2638_ = v___y_2667_;
v___y_2639_ = v___y_2669_;
v___y_2640_ = v___y_2668_;
v___y_2641_ = v___y_2671_;
v___y_2642_ = v___y_2672_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2677_; 
lean_inc_ref(v___y_2670_);
v___x_2677_ = l_Lean_Meta_mkEqRefl(v___y_2670_, v___y_2669_, v___y_2668_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
lean_inc(v_mvarId_2487_);
v___x_2679_ = l_Lean_MVarId_getType(v_mvarId_2487_, v___y_2669_, v___y_2668_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v_nargs_2681_; lean_object* v___x_2682_; lean_object* v_dummy_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v_nargs_2681_ = l_Lean_Expr_getAppNumArgs(v___y_2670_);
v___x_2682_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2681_);
v___x_2684_ = lean_mk_array(v_nargs_2681_, v_dummy_2683_);
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_sub(v_nargs_2681_, v___x_2685_);
lean_dec(v_nargs_2681_);
v___x_2687_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2670_, v___x_2684_, v___x_2686_);
v___x_2688_ = lean_array_push(v___x_2687_, v_a_2678_);
v___x_2689_ = l_Lean_mkAppN(v___x_2682_, v___x_2688_);
lean_dec_ref(v___x_2688_);
lean_inc(v_val_2518_);
v___x_2690_ = l_Lean_LocalDecl_toExpr(v_val_2518_);
v___x_2691_ = l_Lean_Meta_mkAbsurd(v_a_2680_, v___x_2690_, v___x_2689_, v___y_2669_, v___y_2668_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
lean_inc(v_mvarId_2487_);
v___x_2693_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2487_, v_a_2692_, v___y_2668_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v___x_2635_);
lean_dec(v_val_2518_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
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
v___x_2697_ = lean_box(v___x_2497_);
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
lean_ctor_set(v___x_2700_, 1, v___x_2522_);
v_a_2504_ = v___x_2700_;
goto v___jp_2503_;
}
}
}
else
{
lean_object* v_a_2704_; 
v_a_2704_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2693_, 1);
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2669_;
v___y_2659_ = v___y_2668_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2672_;
v_a_2662_ = v_a_2704_;
goto v___jp_2655_;
}
}
else
{
lean_object* v_a_2705_; 
v_a_2705_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2691_, 1);
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2669_;
v___y_2659_ = v___y_2668_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2672_;
v_a_2662_ = v_a_2705_;
goto v___jp_2655_;
}
}
else
{
lean_object* v_a_2706_; 
lean_dec(v_a_2678_);
lean_dec_ref(v___y_2670_);
v_a_2706_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2679_, 1);
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2669_;
v___y_2659_ = v___y_2668_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2672_;
v_a_2662_ = v_a_2706_;
goto v___jp_2655_;
}
}
else
{
lean_object* v_a_2707_; 
lean_dec_ref(v___y_2670_);
v_a_2707_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2677_, 1);
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2669_;
v___y_2659_ = v___y_2668_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2672_;
v_a_2662_ = v_a_2707_;
goto v___jp_2655_;
}
}
}
else
{
lean_object* v_a_2708_; 
lean_dec_ref(v___y_2670_);
v_a_2708_ = lean_ctor_get(v___y_2673_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___y_2673_, 1);
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2669_;
v___y_2659_ = v___y_2668_;
v___y_2660_ = v___y_2671_;
v___y_2661_ = v___y_2672_;
v_a_2662_ = v_a_2708_;
goto v___jp_2655_;
}
}
v___jp_2709_:
{
lean_object* v___x_2716_; 
lean_inc_ref(v___x_2635_);
v___x_2716_ = l_Lean_Meta_mkDecide(v___x_2635_, v___y_2713_, v___y_2712_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; uint8_t v_transparency_2719_; uint8_t v___x_2720_; uint8_t v___x_2721_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2718_ = l_Lean_Meta_Context_config(v___y_2713_);
v_transparency_2719_ = lean_ctor_get_uint8(v___x_2718_, 9);
lean_dec_ref(v___x_2718_);
v___x_2720_ = 1;
v___x_2721_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2719_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v_keyedConfig_2722_; uint8_t v_trackZetaDelta_2723_; lean_object* v_zetaDeltaSet_2724_; lean_object* v_lctx_2725_; lean_object* v_localInstances_2726_; lean_object* v_defEqCtx_x3f_2727_; lean_object* v_synthPendingDepth_2728_; lean_object* v_customCanUnfoldPredicate_x3f_2729_; uint8_t v_univApprox_2730_; uint8_t v_inTypeClassResolution_2731_; uint8_t v_cacheInferType_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_keyedConfig_2722_ = lean_ctor_get(v___y_2713_, 0);
v_trackZetaDelta_2723_ = lean_ctor_get_uint8(v___y_2713_, sizeof(void*)*7);
v_zetaDeltaSet_2724_ = lean_ctor_get(v___y_2713_, 1);
v_lctx_2725_ = lean_ctor_get(v___y_2713_, 2);
v_localInstances_2726_ = lean_ctor_get(v___y_2713_, 3);
v_defEqCtx_x3f_2727_ = lean_ctor_get(v___y_2713_, 4);
v_synthPendingDepth_2728_ = lean_ctor_get(v___y_2713_, 5);
v_customCanUnfoldPredicate_x3f_2729_ = lean_ctor_get(v___y_2713_, 6);
v_univApprox_2730_ = lean_ctor_get_uint8(v___y_2713_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2731_ = lean_ctor_get_uint8(v___y_2713_, sizeof(void*)*7 + 2);
v_cacheInferType_2732_ = lean_ctor_get_uint8(v___y_2713_, sizeof(void*)*7 + 3);
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
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
lean_inc(v___y_2712_);
lean_inc(v_a_2717_);
v___x_2735_ = lean_whnf(v_a_2717_, v___x_2734_, v___y_2712_, v___y_2714_, v___y_2715_);
v___y_2666_ = v___y_2710_;
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v___y_2669_ = v___y_2713_;
v___y_2670_ = v_a_2717_;
v___y_2671_ = v___y_2714_;
v___y_2672_ = v___y_2715_;
v___y_2673_ = v___x_2735_;
goto v___jp_2665_;
}
else
{
lean_object* v___x_2736_; 
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2713_);
lean_inc(v_a_2717_);
v___x_2736_ = lean_whnf(v_a_2717_, v___y_2713_, v___y_2712_, v___y_2714_, v___y_2715_);
v___y_2666_ = v___y_2710_;
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v___y_2669_ = v___y_2713_;
v___y_2670_ = v_a_2717_;
v___y_2671_ = v___y_2714_;
v___y_2672_ = v___y_2715_;
v___y_2673_ = v___x_2736_;
goto v___jp_2665_;
}
}
else
{
lean_object* v_a_2737_; 
v_a_2737_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2716_, 1);
v___y_2656_ = v___y_2710_;
v___y_2657_ = v___y_2711_;
v___y_2658_ = v___y_2713_;
v___y_2659_ = v___y_2712_;
v___y_2660_ = v___y_2714_;
v___y_2661_ = v___y_2715_;
v_a_2662_ = v_a_2737_;
goto v___jp_2655_;
}
}
v___jp_2738_:
{
if (v___y_2745_ == 0)
{
v___y_2637_ = v___y_2739_;
v___y_2638_ = v___y_2740_;
v___y_2639_ = v___y_2742_;
v___y_2640_ = v___y_2741_;
v___y_2641_ = v___y_2743_;
v___y_2642_ = v___y_2744_;
goto v___jp_2636_;
}
else
{
v___y_2710_ = v___y_2739_;
v___y_2711_ = v___y_2740_;
v___y_2712_ = v___y_2741_;
v___y_2713_ = v___y_2742_;
v___y_2714_ = v___y_2743_;
v___y_2715_ = v___y_2744_;
goto v___jp_2709_;
}
}
v___jp_2746_:
{
if (v___y_2754_ == 0)
{
lean_dec_ref(v___y_2747_);
v___y_2739_ = v___y_2748_;
v___y_2740_ = v___y_2749_;
v___y_2741_ = v___y_2751_;
v___y_2742_ = v___y_2750_;
v___y_2743_ = v___y_2752_;
v___y_2744_ = v___y_2753_;
v___y_2745_ = v___x_2591_;
goto v___jp_2738_;
}
else
{
uint8_t v___x_2755_; 
v___x_2755_ = l_Lean_Expr_hasFVar(v___y_2747_);
lean_dec_ref(v___y_2747_);
if (v___x_2755_ == 0)
{
v___y_2710_ = v___y_2748_;
v___y_2711_ = v___y_2749_;
v___y_2712_ = v___y_2751_;
v___y_2713_ = v___y_2750_;
v___y_2714_ = v___y_2752_;
v___y_2715_ = v___y_2753_;
goto v___jp_2709_;
}
else
{
v___y_2739_ = v___y_2748_;
v___y_2740_ = v___y_2749_;
v___y_2741_ = v___y_2751_;
v___y_2742_ = v___y_2750_;
v___y_2743_ = v___y_2752_;
v___y_2744_ = v___y_2753_;
v___y_2745_ = v___x_2591_;
goto v___jp_2738_;
}
}
}
v___jp_2756_:
{
lean_object* v___x_2764_; 
lean_inc_ref(v___x_2635_);
v___x_2764_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2635_, v___y_2760_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; uint8_t v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2766_ = l_Lean_Expr_hasMVar(v_a_2765_);
if (v___x_2766_ == 0)
{
v___y_2747_ = v_a_2765_;
v___y_2748_ = v___y_2757_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___y_2759_;
v___y_2751_ = v___y_2760_;
v___y_2752_ = v___y_2761_;
v___y_2753_ = v___y_2762_;
v___y_2754_ = v___y_2763_;
goto v___jp_2746_;
}
else
{
v___y_2747_ = v_a_2765_;
v___y_2748_ = v___y_2757_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___y_2759_;
v___y_2751_ = v___y_2760_;
v___y_2752_ = v___y_2761_;
v___y_2753_ = v___y_2762_;
v___y_2754_ = v___x_2591_;
goto v___jp_2746_;
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec_ref(v___x_2635_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_2767_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2764_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2764_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
v___jp_2775_:
{
if (v___y_2782_ == 0)
{
v___y_2637_ = v___y_2776_;
v___y_2638_ = v___y_2777_;
v___y_2639_ = v___y_2779_;
v___y_2640_ = v___y_2778_;
v___y_2641_ = v___y_2780_;
v___y_2642_ = v___y_2781_;
goto v___jp_2636_;
}
else
{
v___y_2757_ = v___y_2776_;
v___y_2758_ = v___y_2777_;
v___y_2759_ = v___y_2779_;
v___y_2760_ = v___y_2778_;
v___y_2761_ = v___y_2780_;
v___y_2762_ = v___y_2781_;
v___y_2763_ = v___y_2782_;
goto v___jp_2756_;
}
}
v___jp_2783_:
{
uint8_t v_useDecide_2790_; 
v_useDecide_2790_ = lean_ctor_get_uint8(v_config_2486_, sizeof(void*)*1);
if (v_useDecide_2790_ == 0)
{
v___y_2776_ = v_isHEq_2785_;
v___y_2777_ = v___y_2784_;
v___y_2778_ = v___y_2787_;
v___y_2779_ = v___y_2786_;
v___y_2780_ = v___y_2788_;
v___y_2781_ = v___y_2789_;
v___y_2782_ = v___x_2591_;
goto v___jp_2775_;
}
else
{
uint8_t v___x_2791_; 
v___x_2791_ = l_Lean_Expr_hasFVar(v___x_2635_);
if (v___x_2791_ == 0)
{
v___y_2757_ = v_isHEq_2785_;
v___y_2758_ = v___y_2784_;
v___y_2759_ = v___y_2786_;
v___y_2760_ = v___y_2787_;
v___y_2761_ = v___y_2788_;
v___y_2762_ = v___y_2789_;
v___y_2763_ = v_useDecide_2790_;
goto v___jp_2756_;
}
else
{
v___y_2776_ = v_isHEq_2785_;
v___y_2777_ = v___y_2784_;
v___y_2778_ = v___y_2787_;
v___y_2779_ = v___y_2786_;
v___y_2780_ = v___y_2788_;
v___y_2781_ = v___y_2789_;
v___y_2782_ = v___x_2591_;
goto v___jp_2775_;
}
}
}
v___jp_2792_:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Meta_isExprDefEq(v___y_2797_, v___y_2799_, v___y_2793_, v___y_2798_, v___y_2795_, v___y_2794_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; uint8_t v___x_2802_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
v___x_2802_ = lean_unbox(v_a_2801_);
lean_dec(v_a_2801_);
if (v___x_2802_ == 0)
{
v___y_2784_ = v___y_2796_;
v_isHEq_2785_ = v___x_2497_;
v___y_2786_ = v___y_2793_;
v___y_2787_ = v___y_2798_;
v___y_2788_ = v___y_2795_;
v___y_2789_ = v___y_2794_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2803_; 
lean_dec_ref(v___x_2635_);
lean_dec_ref(v_config_2486_);
lean_inc(v_mvarId_2487_);
v___x_2803_ = l_Lean_MVarId_getType(v_mvarId_2487_, v___y_2793_, v___y_2798_, v___y_2795_, v___y_2794_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v___x_2805_ = l_Lean_LocalDecl_toExpr(v_val_2518_);
v___x_2806_ = l_Lean_Meta_mkEqOfHEq(v___x_2805_, v___x_2497_, v___y_2793_, v___y_2798_, v___y_2795_, v___y_2794_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2808_ = l_Lean_Meta_mkNoConfusion(v_a_2804_, v_a_2807_, v___y_2793_, v___y_2798_, v___y_2795_, v___y_2794_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2487_, v_a_2809_, v___y_2798_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_dec_ref_known(v___x_2810_, 1);
v___x_2811_ = lean_box(v___x_2497_);
v___x_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v___x_2522_);
v_a_2504_ = v___x_2813_;
goto v___jp_2503_;
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
v_a_2814_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2810_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2810_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_2822_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2808_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2808_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_a_2804_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_2830_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2806_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2806_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_2838_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2803_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2803_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v___x_2635_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_2846_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2800_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2800_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
v___jp_2854_:
{
lean_object* v___x_2860_; 
lean_inc_ref(v___x_2635_);
v___x_2860_ = l_Lean_Meta_matchHEq_x3f(v___x_2635_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
if (lean_obj_tag(v_a_2861_) == 1)
{
lean_object* v_val_2862_; lean_object* v_snd_2863_; lean_object* v_snd_2864_; lean_object* v_fst_2865_; lean_object* v_fst_2866_; lean_object* v_fst_2867_; lean_object* v_snd_2868_; lean_object* v___x_2869_; 
v_val_2862_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_val_2862_);
lean_dec_ref_known(v_a_2861_, 1);
v_snd_2863_ = lean_ctor_get(v_val_2862_, 1);
lean_inc(v_snd_2863_);
v_snd_2864_ = lean_ctor_get(v_snd_2863_, 1);
lean_inc(v_snd_2864_);
v_fst_2865_ = lean_ctor_get(v_val_2862_, 0);
lean_inc(v_fst_2865_);
lean_dec(v_val_2862_);
v_fst_2866_ = lean_ctor_get(v_snd_2863_, 0);
lean_inc(v_fst_2866_);
lean_dec(v_snd_2863_);
v_fst_2867_ = lean_ctor_get(v_snd_2864_, 0);
lean_inc(v_fst_2867_);
v_snd_2868_ = lean_ctor_get(v_snd_2864_, 1);
lean_inc(v_snd_2868_);
lean_dec(v_snd_2864_);
v___x_2869_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2866_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
if (lean_obj_tag(v_a_2870_) == 1)
{
lean_object* v_val_2871_; lean_object* v___x_2872_; 
v_val_2871_ = lean_ctor_get(v_a_2870_, 0);
lean_inc(v_val_2871_);
lean_dec_ref_known(v_a_2870_, 1);
v___x_2872_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2868_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
if (lean_obj_tag(v_a_2873_) == 1)
{
lean_object* v_toConstantVal_2874_; lean_object* v_val_2875_; lean_object* v_toConstantVal_2876_; lean_object* v_name_2877_; lean_object* v_name_2878_; uint8_t v___x_2879_; 
v_toConstantVal_2874_ = lean_ctor_get(v_val_2871_, 0);
lean_inc_ref(v_toConstantVal_2874_);
lean_dec(v_val_2871_);
v_val_2875_ = lean_ctor_get(v_a_2873_, 0);
lean_inc(v_val_2875_);
lean_dec_ref_known(v_a_2873_, 1);
v_toConstantVal_2876_ = lean_ctor_get(v_val_2875_, 0);
lean_inc_ref(v_toConstantVal_2876_);
lean_dec(v_val_2875_);
v_name_2877_ = lean_ctor_get(v_toConstantVal_2874_, 0);
lean_inc(v_name_2877_);
lean_dec_ref(v_toConstantVal_2874_);
v_name_2878_ = lean_ctor_get(v_toConstantVal_2876_, 0);
lean_inc(v_name_2878_);
lean_dec_ref(v_toConstantVal_2876_);
v___x_2879_ = lean_name_eq(v_name_2877_, v_name_2878_);
lean_dec(v_name_2878_);
lean_dec(v_name_2877_);
if (v___x_2879_ == 0)
{
v___y_2793_ = v___y_2856_;
v___y_2794_ = v___y_2859_;
v___y_2795_ = v___y_2858_;
v___y_2796_ = v_isEq_2855_;
v___y_2797_ = v_fst_2865_;
v___y_2798_ = v___y_2857_;
v___y_2799_ = v_fst_2867_;
goto v___jp_2792_;
}
else
{
if (v___x_2591_ == 0)
{
lean_dec(v_fst_2867_);
lean_dec(v_fst_2865_);
v___y_2784_ = v_isEq_2855_;
v_isHEq_2785_ = v___x_2497_;
v___y_2786_ = v___y_2856_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
goto v___jp_2783_;
}
else
{
v___y_2793_ = v___y_2856_;
v___y_2794_ = v___y_2859_;
v___y_2795_ = v___y_2858_;
v___y_2796_ = v_isEq_2855_;
v___y_2797_ = v_fst_2865_;
v___y_2798_ = v___y_2857_;
v___y_2799_ = v_fst_2867_;
goto v___jp_2792_;
}
}
}
else
{
lean_dec(v_a_2873_);
lean_dec(v_val_2871_);
lean_dec(v_fst_2867_);
lean_dec(v_fst_2865_);
v___y_2784_ = v_isEq_2855_;
v_isHEq_2785_ = v___x_2497_;
v___y_2786_ = v___y_2856_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
goto v___jp_2783_;
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_val_2871_);
lean_dec(v_fst_2867_);
lean_dec(v_fst_2865_);
lean_dec_ref(v___x_2635_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_2880_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2872_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2872_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_dec(v_a_2870_);
lean_dec(v_snd_2868_);
lean_dec(v_fst_2867_);
lean_dec(v_fst_2865_);
v___y_2784_ = v_isEq_2855_;
v_isHEq_2785_ = v___x_2497_;
v___y_2786_ = v___y_2856_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
goto v___jp_2783_;
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_snd_2868_);
lean_dec(v_fst_2867_);
lean_dec(v_fst_2865_);
lean_dec_ref(v___x_2635_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_2888_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2869_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2869_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_dec(v_a_2861_);
v___y_2784_ = v_isEq_2855_;
v_isHEq_2785_ = v___x_2591_;
v___y_2786_ = v___y_2856_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
v___y_2789_ = v___y_2859_;
goto v___jp_2783_;
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref(v___x_2635_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_2896_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2860_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2860_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
v___jp_2904_:
{
lean_object* v___x_2909_; 
lean_inc_ref(v___x_2635_);
v___x_2909_ = l_Lean_Meta_matchEq_x3f(v___x_2635_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 1);
if (lean_obj_tag(v_a_2910_) == 1)
{
lean_object* v_val_2911_; lean_object* v_snd_2912_; lean_object* v_fst_2913_; lean_object* v_snd_2914_; lean_object* v___x_2915_; 
v_val_2911_ = lean_ctor_get(v_a_2910_, 0);
lean_inc(v_val_2911_);
lean_dec_ref_known(v_a_2910_, 1);
v_snd_2912_ = lean_ctor_get(v_val_2911_, 1);
lean_inc(v_snd_2912_);
lean_dec(v_val_2911_);
v_fst_2913_ = lean_ctor_get(v_snd_2912_, 0);
lean_inc(v_fst_2913_);
v_snd_2914_ = lean_ctor_get(v_snd_2912_, 1);
lean_inc(v_snd_2914_);
lean_dec(v_snd_2912_);
v___x_2915_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2913_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
if (lean_obj_tag(v_a_2916_) == 1)
{
lean_object* v_val_2917_; lean_object* v___x_2918_; 
v_val_2917_ = lean_ctor_get(v_a_2916_, 0);
lean_inc(v_val_2917_);
lean_dec_ref_known(v_a_2916_, 1);
v___x_2918_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2914_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
if (lean_obj_tag(v_a_2919_) == 1)
{
lean_object* v_toConstantVal_2920_; lean_object* v_val_2921_; lean_object* v_toConstantVal_2922_; lean_object* v_name_2923_; lean_object* v_name_2924_; uint8_t v___x_2925_; 
v_toConstantVal_2920_ = lean_ctor_get(v_val_2917_, 0);
lean_inc_ref(v_toConstantVal_2920_);
lean_dec(v_val_2917_);
v_val_2921_ = lean_ctor_get(v_a_2919_, 0);
lean_inc(v_val_2921_);
lean_dec_ref_known(v_a_2919_, 1);
v_toConstantVal_2922_ = lean_ctor_get(v_val_2921_, 0);
lean_inc_ref(v_toConstantVal_2922_);
lean_dec(v_val_2921_);
v_name_2923_ = lean_ctor_get(v_toConstantVal_2920_, 0);
lean_inc(v_name_2923_);
lean_dec_ref(v_toConstantVal_2920_);
v_name_2924_ = lean_ctor_get(v_toConstantVal_2922_, 0);
lean_inc(v_name_2924_);
lean_dec_ref(v_toConstantVal_2922_);
v___x_2925_ = lean_name_eq(v_name_2923_, v_name_2924_);
lean_dec(v_name_2924_);
lean_dec(v_name_2923_);
if (v___x_2925_ == 0)
{
lean_dec_ref(v___x_2635_);
lean_dec_ref(v_config_2486_);
v___y_2524_ = v___y_2907_;
v___y_2525_ = v___y_2908_;
v___y_2526_ = v___y_2906_;
v___y_2527_ = v___y_2905_;
goto v___jp_2523_;
}
else
{
if (v___x_2591_ == 0)
{
lean_del_object(v___x_2520_);
v_isEq_2855_ = v___x_2497_;
v___y_2856_ = v___y_2905_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
goto v___jp_2854_;
}
else
{
lean_dec_ref(v___x_2635_);
lean_dec_ref(v_config_2486_);
v___y_2524_ = v___y_2907_;
v___y_2525_ = v___y_2908_;
v___y_2526_ = v___y_2906_;
v___y_2527_ = v___y_2905_;
goto v___jp_2523_;
}
}
}
else
{
lean_dec(v_a_2919_);
lean_dec(v_val_2917_);
lean_del_object(v___x_2520_);
v_isEq_2855_ = v___x_2497_;
v___y_2856_ = v___y_2905_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
goto v___jp_2854_;
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_val_2917_);
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_2926_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2918_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2918_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_dec(v_a_2916_);
lean_dec(v_snd_2914_);
lean_del_object(v___x_2520_);
v_isEq_2855_ = v___x_2497_;
v___y_2856_ = v___y_2905_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
goto v___jp_2854_;
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_snd_2914_);
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_2934_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2915_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2915_);
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
else
{
lean_dec(v_a_2910_);
lean_del_object(v___x_2520_);
v_isEq_2855_ = v___x_2591_;
v___y_2856_ = v___y_2905_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
v___y_2859_ = v___y_2908_;
goto v___jp_2854_;
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_2942_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2909_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2909_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
v___jp_2950_:
{
lean_object* v___x_2955_; 
lean_inc_ref(v___x_2635_);
v___x_2955_ = l_Lean_refutableHasNotBit_x3f(v___x_2635_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
if (lean_obj_tag(v_a_2956_) == 1)
{
lean_object* v_val_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec_ref(v_config_2486_);
v_val_2957_ = lean_ctor_get(v_a_2956_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_a_2956_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2959_ = v_a_2956_;
v_isShared_2960_ = v_isSharedCheck_2996_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_val_2957_);
lean_dec(v_a_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2996_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; 
lean_inc(v_mvarId_2487_);
v___x_2961_ = l_Lean_MVarId_getType(v_mvarId_2487_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v___x_2963_ = l_Lean_LocalDecl_toExpr(v_val_2518_);
v___x_2964_ = l_Lean_Meta_mkAbsurd(v_a_2962_, v_val_2957_, v___x_2963_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2966_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2487_, v_a_2965_, v___y_2952_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
lean_dec_ref_known(v___x_2966_, 1);
v___x_2967_ = lean_box(v___x_2497_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2967_);
v___x_2969_ = v___x_2959_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; 
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v___x_2522_);
v_a_2504_ = v___x_2970_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_del_object(v___x_2959_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
v_a_2972_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2966_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2966_);
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
lean_del_object(v___x_2959_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_2980_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2964_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2964_);
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
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_del_object(v___x_2959_);
lean_dec(v_val_2957_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_2988_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2961_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2961_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
}
else
{
lean_object* v___x_2997_; 
lean_dec(v_a_2956_);
lean_inc_ref(v___x_2635_);
v___x_2997_ = l_Lean_Meta_matchNe_x3f(v___x_2635_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
if (lean_obj_tag(v_a_2998_) == 1)
{
lean_object* v_val_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3068_; 
v_val_2999_ = lean_ctor_get(v_a_2998_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_a_2998_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3001_ = v_a_2998_;
v_isShared_3002_ = v_isSharedCheck_3068_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_val_2999_);
lean_dec(v_a_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3068_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v_snd_3003_; lean_object* v_fst_3004_; lean_object* v_snd_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3067_; 
v_snd_3003_ = lean_ctor_get(v_val_2999_, 1);
lean_inc(v_snd_3003_);
lean_dec(v_val_2999_);
v_fst_3004_ = lean_ctor_get(v_snd_3003_, 0);
v_snd_3005_ = lean_ctor_get(v_snd_3003_, 1);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_snd_3003_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3007_ = v_snd_3003_;
v_isShared_3008_ = v_isSharedCheck_3067_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_snd_3005_);
lean_inc(v_fst_3004_);
lean_dec(v_snd_3003_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3067_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; 
lean_inc(v_fst_3004_);
v___x_3009_ = l_Lean_Meta_isExprDefEq(v_fst_3004_, v_snd_3005_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; uint8_t v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3011_ = lean_unbox(v_a_3010_);
lean_dec(v_a_3010_);
if (v___x_3011_ == 0)
{
lean_del_object(v___x_3007_);
lean_dec(v_fst_3004_);
lean_del_object(v___x_3001_);
v___y_2905_ = v___y_2951_;
v___y_2906_ = v___y_2952_;
v___y_2907_ = v___y_2953_;
v___y_2908_ = v___y_2954_;
goto v___jp_2904_;
}
else
{
lean_object* v___x_3012_; 
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec_ref(v_config_2486_);
lean_inc(v_mvarId_2487_);
v___x_3012_ = l_Lean_MVarId_getType(v_mvarId_2487_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = l_Lean_Meta_mkEqRefl(v_fst_3004_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = l_Lean_LocalDecl_toExpr(v_val_2518_);
v___x_3017_ = l_Lean_Meta_mkAbsurd(v_a_3013_, v_a_3015_, v___x_3016_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2487_, v_a_3018_, v___y_2952_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3022_; 
lean_dec_ref_known(v___x_3019_, 1);
v___x_3020_ = lean_box(v___x_2497_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3020_);
v___x_3022_ = v___x_3001_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3024_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v___x_2522_);
lean_ctor_set(v___x_3007_, 0, v___x_3022_);
v___x_3024_ = v___x_3007_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v___x_2522_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
v_a_2504_ = v___x_3024_;
goto v___jp_2503_;
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_del_object(v___x_3007_);
lean_del_object(v___x_3001_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
v_a_3027_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3019_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3019_);
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
lean_del_object(v___x_3007_);
lean_del_object(v___x_3001_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_3035_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3017_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3017_);
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
lean_dec(v_a_3013_);
lean_del_object(v___x_3007_);
lean_del_object(v___x_3001_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_3043_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3014_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3014_);
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
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_del_object(v___x_3007_);
lean_dec(v_fst_3004_);
lean_del_object(v___x_3001_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_3051_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3012_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3012_);
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
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_del_object(v___x_3007_);
lean_dec(v_fst_3004_);
lean_del_object(v___x_3001_);
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_3059_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3009_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3009_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2998_);
v___y_2905_ = v___y_2951_;
v___y_2906_ = v___y_2952_;
v___y_2907_ = v___y_2953_;
v___y_2908_ = v___y_2954_;
goto v___jp_2904_;
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_3069_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_2997_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_2997_);
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
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec_ref(v___x_2635_);
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_3077_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_2955_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_2955_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
else
{
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
v_a_2512_ = v___x_2563_;
goto v___jp_2511_;
}
v___jp_2523_:
{
lean_object* v___x_2528_; 
lean_inc(v_mvarId_2487_);
v___x_2528_ = l_Lean_MVarId_getType(v_mvarId_2487_, v___y_2527_, v___y_2526_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = l_Lean_LocalDecl_toExpr(v_val_2518_);
v___x_2531_ = l_Lean_Meta_mkNoConfusion(v_a_2529_, v___x_2530_, v___y_2527_, v___y_2526_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2487_, v_a_2532_, v___y_2526_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_dec_ref_known(v___x_2533_, 1);
v___x_2534_ = lean_box(v___x_2497_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2534_);
v___x_2536_ = v___x_2520_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v___x_2522_);
v_a_2504_ = v___x_2537_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_del_object(v___x_2520_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
v_a_2539_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2533_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2533_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_del_object(v___x_2520_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_2547_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2531_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2531_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_del_object(v___x_2520_);
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
v_a_2555_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2528_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2528_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
v___jp_2564_:
{
lean_object* v_searchFuel_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_searchFuel_2569_ = lean_ctor_get(v_config_2486_, 0);
v___x_2570_ = l_Lean_LocalDecl_fvarId(v_val_2518_);
lean_dec(v_val_2518_);
lean_inc(v_searchFuel_2569_);
lean_inc(v_mvarId_2487_);
v___x_2571_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2487_, v___x_2570_, v_searchFuel_2569_, v___y_2566_, v___y_2565_, v___y_2567_, v___y_2568_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; uint8_t v___x_2573_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2573_ = lean_unbox(v_a_2572_);
lean_dec(v_a_2572_);
if (v___x_2573_ == 0)
{
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
v_a_2512_ = v___x_2563_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v___x_2574_ = lean_box(v___x_2497_);
v___x_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v___x_2522_);
v_a_2504_ = v___x_2576_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v_a_2577_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2571_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2571_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
v___jp_2585_:
{
if (v___y_2590_ == 0)
{
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
v_a_2512_ = v___x_2563_;
goto v___jp_2511_;
}
else
{
v___y_2565_ = v___y_2586_;
v___y_2566_ = v___y_2587_;
v___y_2567_ = v___y_2588_;
v___y_2568_ = v___y_2589_;
goto v___jp_2564_;
}
}
v___jp_2592_:
{
if (v___y_2595_ == 0)
{
v___y_2565_ = v___y_2593_;
v___y_2566_ = v___y_2594_;
v___y_2567_ = v___y_2596_;
v___y_2568_ = v___y_2597_;
goto v___jp_2564_;
}
else
{
v___y_2586_ = v___y_2593_;
v___y_2587_ = v___y_2594_;
v___y_2588_ = v___y_2596_;
v___y_2589_ = v___y_2597_;
v___y_2590_ = v___x_2591_;
goto v___jp_2585_;
}
}
v___jp_2598_:
{
if (v___y_2604_ == 0)
{
v___y_2586_ = v___y_2599_;
v___y_2587_ = v___y_2600_;
v___y_2588_ = v___y_2602_;
v___y_2589_ = v___y_2603_;
v___y_2590_ = v___x_2591_;
goto v___jp_2585_;
}
else
{
v___y_2593_ = v___y_2599_;
v___y_2594_ = v___y_2600_;
v___y_2595_ = v___y_2601_;
v___y_2596_ = v___y_2602_;
v___y_2597_ = v___y_2603_;
goto v___jp_2592_;
}
}
v___jp_2605_:
{
uint8_t v_emptyType_2612_; 
v_emptyType_2612_ = lean_ctor_get_uint8(v_config_2486_, sizeof(void*)*1 + 1);
if (v_emptyType_2612_ == 0)
{
v___y_2599_ = v___y_2609_;
v___y_2600_ = v___y_2608_;
v___y_2601_ = v___y_2606_;
v___y_2602_ = v___y_2610_;
v___y_2603_ = v___y_2611_;
v___y_2604_ = v___x_2591_;
goto v___jp_2598_;
}
else
{
if (v___y_2607_ == 0)
{
v___y_2593_ = v___y_2609_;
v___y_2594_ = v___y_2608_;
v___y_2595_ = v___y_2606_;
v___y_2596_ = v___y_2610_;
v___y_2597_ = v___y_2611_;
goto v___jp_2592_;
}
else
{
v___y_2599_ = v___y_2609_;
v___y_2600_ = v___y_2608_;
v___y_2601_ = v___y_2606_;
v___y_2602_ = v___y_2610_;
v___y_2603_ = v___y_2611_;
v___y_2604_ = v___x_2591_;
goto v___jp_2598_;
}
}
}
v___jp_2613_:
{
if (v___y_2620_ == 0)
{
v___y_2606_ = v___y_2614_;
v___y_2607_ = v___y_2615_;
v___y_2608_ = v___y_2617_;
v___y_2609_ = v___y_2618_;
v___y_2610_ = v___y_2619_;
v___y_2611_ = v___y_2616_;
goto v___jp_2605_;
}
else
{
lean_object* v___x_2621_; 
lean_inc(v_val_2518_);
lean_inc(v_mvarId_2487_);
v___x_2621_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2487_, v_val_2518_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2616_);
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
v___y_2606_ = v___y_2614_;
v___y_2607_ = v___y_2615_;
v___y_2608_ = v___y_2617_;
v___y_2609_ = v___y_2618_;
v___y_2610_ = v___y_2619_;
v___y_2611_ = v___y_2616_;
goto v___jp_2605_;
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec(v_val_2518_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
v___x_2624_ = lean_box(v___x_2497_);
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v___x_2522_);
v_a_2504_ = v___x_2626_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_val_2518_);
lean_del_object(v___x_2501_);
lean_dec(v_snd_2499_);
lean_dec(v_mvarId_2487_);
lean_dec_ref(v_config_2486_);
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
}
v___jp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2507_; 
v___x_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_a_2504_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2505_);
v___x_2507_ = v___x_2501_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_snd_2499_);
v___x_2507_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
v___jp_2511_:
{
lean_object* v___x_2513_; size_t v___x_2514_; size_t v___x_2515_; lean_object* v___x_2516_; 
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2510_);
lean_ctor_set(v___x_2513_, 1, v_a_2512_);
v___x_2514_ = ((size_t)1ULL);
v___x_2515_ = lean_usize_add(v_i_2490_, v___x_2514_);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2486_, v_mvarId_2487_, v_as_2488_, v_sz_2489_, v___x_2515_, v___x_2513_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3151_, lean_object* v_mvarId_3152_, lean_object* v_as_3153_, lean_object* v_sz_3154_, lean_object* v_i_3155_, lean_object* v_b_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
size_t v_sz_boxed_3162_; size_t v_i_boxed_3163_; lean_object* v_res_3164_; 
v_sz_boxed_3162_ = lean_unbox_usize(v_sz_3154_);
lean_dec(v_sz_3154_);
v_i_boxed_3163_ = lean_unbox_usize(v_i_3155_);
lean_dec(v_i_3155_);
v_res_3164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3151_, v_mvarId_3152_, v_as_3153_, v_sz_boxed_3162_, v_i_boxed_3163_, v_b_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec_ref(v_as_3153_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3168_, lean_object* v_mvarId_3169_, lean_object* v_as_3170_, size_t v_sz_3171_, size_t v_i_3172_, lean_object* v_b_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
uint8_t v___x_3179_; 
v___x_3179_ = lean_usize_dec_lt(v_i_3172_, v_sz_3171_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; 
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v_b_3173_);
return v___x_3180_;
}
else
{
lean_object* v_snd_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3851_; 
v_snd_3181_ = lean_ctor_get(v_b_3173_, 1);
v_isSharedCheck_3851_ = !lean_is_exclusive(v_b_3173_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; 
v_unused_3852_ = lean_ctor_get(v_b_3173_, 0);
lean_dec(v_unused_3852_);
v___x_3183_ = v_b_3173_;
v_isShared_3184_ = v_isSharedCheck_3851_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_snd_3181_);
lean_dec(v_b_3173_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3851_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_a_3186_; lean_object* v___x_3192_; lean_object* v_a_3194_; lean_object* v_a_3199_; 
v___x_3192_ = lean_box(0);
v_a_3199_ = lean_array_uget(v_as_3170_, v_i_3172_);
if (lean_obj_tag(v_a_3199_) == 0)
{
lean_del_object(v___x_3183_);
v_a_3194_ = v_snd_3181_;
goto v___jp_3193_;
}
else
{
lean_object* v_val_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3850_; 
v_val_3200_ = lean_ctor_get(v_a_3199_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_a_3199_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3202_ = v_a_3199_;
v_isShared_3203_ = v_isSharedCheck_3850_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_val_3200_);
lean_dec(v_a_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3850_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___x_3246_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; uint8_t v___y_3274_; uint8_t v___x_3275_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; uint8_t v___y_3281_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; uint8_t v___y_3287_; uint8_t v___y_3288_; uint8_t v___y_3290_; uint8_t v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3298_; uint8_t v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; uint8_t v___y_3303_; uint8_t v___y_3304_; 
v___x_3204_ = lean_box(0);
v___x_3246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3275_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3200_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3320_; uint8_t v___y_3322_; uint8_t v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3331_; lean_object* v___y_3332_; uint8_t v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; uint8_t v___y_3336_; lean_object* v___y_3337_; uint8_t v___y_3338_; lean_object* v___y_3341_; lean_object* v___y_3342_; uint8_t v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; uint8_t v___y_3346_; lean_object* v_a_3347_; lean_object* v___y_3351_; lean_object* v___y_3352_; uint8_t v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; uint8_t v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___y_3404_; lean_object* v___y_3405_; uint8_t v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3431_; lean_object* v___y_3432_; uint8_t v___y_3433_; lean_object* v___y_3434_; uint8_t v___y_3435_; lean_object* v___y_3436_; uint8_t v___y_3437_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; uint8_t v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; uint8_t v___y_3445_; uint8_t v___y_3446_; lean_object* v___y_3449_; lean_object* v___y_3450_; uint8_t v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; uint8_t v___y_3454_; uint8_t v___y_3455_; lean_object* v___y_3468_; lean_object* v___y_3469_; uint8_t v___y_3470_; lean_object* v___y_3471_; uint8_t v___y_3472_; lean_object* v___y_3473_; uint8_t v___y_3474_; uint8_t v___y_3476_; uint8_t v_isHEq_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; uint8_t v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; uint8_t v_isEq_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___x_3780_; 
v___x_3320_ = l_Lean_LocalDecl_type(v_val_3200_);
lean_inc_ref(v___x_3320_);
v___x_3780_ = l_Lean_Meta_matchNot_x3f(v___x_3320_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3780_, 1);
if (lean_obj_tag(v_a_3781_) == 1)
{
lean_object* v_val_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3841_; 
v_val_3782_ = lean_ctor_get(v_a_3781_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_a_3781_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3784_ = v_a_3781_;
v_isShared_3785_ = v_isSharedCheck_3841_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_val_3782_);
lean_dec(v_a_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3841_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3782_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v___x_3786_, 1);
if (lean_obj_tag(v_a_3787_) == 1)
{
lean_object* v_val_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec_ref(v_config_3168_);
v_val_3788_ = lean_ctor_get(v_a_3787_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_a_3787_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3790_ = v_a_3787_;
v_isShared_3791_ = v_isSharedCheck_3832_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_val_3788_);
lean_dec(v_a_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3832_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3792_; 
lean_inc(v_mvarId_3169_);
v___x_3792_ = l_Lean_MVarId_getType(v_mvarId_3169_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___x_3794_ = l_Lean_LocalDecl_toExpr(v_val_3200_);
v___x_3795_ = l_Lean_mkFVar(v_val_3788_);
v___x_3796_ = l_Lean_Expr_app___override(v___x_3794_, v___x_3795_);
v___x_3797_ = l_Lean_Meta_mkFalseElim(v_a_3793_, v___x_3796_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3799_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v___x_3799_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3169_, v_a_3798_, v___y_3175_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v___x_3800_; lean_object* v___x_3802_; 
lean_dec_ref_known(v___x_3799_, 1);
v___x_3800_ = lean_box(v___x_3179_);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v___x_3800_);
v___x_3802_ = v___x_3790_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
lean_ctor_set(v___x_3803_, 1, v___x_3204_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set_tag(v___x_3784_, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3803_);
v___x_3805_ = v___x_3784_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
v_a_3186_ = v___x_3805_;
goto v___jp_3185_;
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_del_object(v___x_3790_);
lean_del_object(v___x_3784_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
v_a_3808_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3799_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3799_);
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
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_del_object(v___x_3790_);
lean_del_object(v___x_3784_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3816_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3797_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3797_);
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
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_del_object(v___x_3790_);
lean_dec(v_val_3788_);
lean_del_object(v___x_3784_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3824_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3792_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3792_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
else
{
lean_dec(v_a_3787_);
lean_del_object(v___x_3784_);
v___y_3644_ = v___y_3174_;
v___y_3645_ = v___y_3175_;
v___y_3646_ = v___y_3176_;
v___y_3647_ = v___y_3177_;
goto v___jp_3643_;
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_del_object(v___x_3784_);
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3833_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3786_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3786_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
else
{
lean_dec(v_a_3781_);
v___y_3644_ = v___y_3174_;
v___y_3645_ = v___y_3175_;
v___y_3646_ = v___y_3176_;
v___y_3647_ = v___y_3177_;
goto v___jp_3643_;
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3842_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3780_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3780_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
v___jp_3321_:
{
uint8_t v_genDiseq_3328_; 
v_genDiseq_3328_ = lean_ctor_get_uint8(v_config_3168_, sizeof(void*)*1 + 2);
if (v_genDiseq_3328_ == 0)
{
lean_dec_ref(v___x_3320_);
v___y_3298_ = v___y_3326_;
v___y_3299_ = v___y_3322_;
v___y_3300_ = v___y_3327_;
v___y_3301_ = v___y_3325_;
v___y_3302_ = v___y_3324_;
v___y_3303_ = v___y_3323_;
v___y_3304_ = v___x_3275_;
goto v___jp_3297_;
}
else
{
uint8_t v___x_3329_; 
v___x_3329_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3320_);
v___y_3298_ = v___y_3326_;
v___y_3299_ = v___y_3322_;
v___y_3300_ = v___y_3327_;
v___y_3301_ = v___y_3325_;
v___y_3302_ = v___y_3324_;
v___y_3303_ = v___y_3323_;
v___y_3304_ = v___x_3329_;
goto v___jp_3297_;
}
}
v___jp_3330_:
{
if (v___y_3338_ == 0)
{
lean_dec_ref(v___y_3335_);
v___y_3322_ = v___y_3333_;
v___y_3323_ = v___y_3336_;
v___y_3324_ = v___y_3334_;
v___y_3325_ = v___y_3332_;
v___y_3326_ = v___y_3337_;
v___y_3327_ = v___y_3331_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3339_; 
lean_dec_ref(v___x_3320_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v___x_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___y_3335_);
return v___x_3339_;
}
}
v___jp_3340_:
{
uint8_t v___x_3348_; 
v___x_3348_ = l_Lean_Exception_isInterrupt(v_a_3347_);
if (v___x_3348_ == 0)
{
uint8_t v___x_3349_; 
lean_inc_ref(v_a_3347_);
v___x_3349_ = l_Lean_Exception_isRuntime(v_a_3347_);
v___y_3331_ = v___y_3341_;
v___y_3332_ = v___y_3342_;
v___y_3333_ = v___y_3343_;
v___y_3334_ = v___y_3344_;
v___y_3335_ = v_a_3347_;
v___y_3336_ = v___y_3346_;
v___y_3337_ = v___y_3345_;
v___y_3338_ = v___x_3349_;
goto v___jp_3330_;
}
else
{
v___y_3331_ = v___y_3341_;
v___y_3332_ = v___y_3342_;
v___y_3333_ = v___y_3343_;
v___y_3334_ = v___y_3344_;
v___y_3335_ = v_a_3347_;
v___y_3336_ = v___y_3346_;
v___y_3337_ = v___y_3345_;
v___y_3338_ = v___x_3348_;
goto v___jp_3330_;
}
}
v___jp_3350_:
{
if (lean_obj_tag(v___y_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v_a_3359_ = lean_ctor_get(v___y_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___y_3358_, 1);
v___x_3360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3361_ = l_Lean_Expr_isConstOf(v_a_3359_, v___x_3360_);
lean_dec(v_a_3359_);
if (v___x_3361_ == 0)
{
lean_dec_ref(v___y_3355_);
v___y_3322_ = v___y_3353_;
v___y_3323_ = v___y_3356_;
v___y_3324_ = v___y_3354_;
v___y_3325_ = v___y_3352_;
v___y_3326_ = v___y_3357_;
v___y_3327_ = v___y_3351_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3362_; 
lean_inc_ref(v___y_3355_);
v___x_3362_ = l_Lean_Meta_mkEqRefl(v___y_3355_, v___y_3354_, v___y_3352_, v___y_3357_, v___y_3351_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
lean_inc(v_mvarId_3169_);
v___x_3364_ = l_Lean_MVarId_getType(v_mvarId_3169_, v___y_3354_, v___y_3352_, v___y_3357_, v___y_3351_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v_nargs_3366_; lean_object* v___x_3367_; lean_object* v_dummy_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v_nargs_3366_ = l_Lean_Expr_getAppNumArgs(v___y_3355_);
v___x_3367_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3368_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_3366_);
v___x_3369_ = lean_mk_array(v_nargs_3366_, v_dummy_3368_);
v___x_3370_ = lean_unsigned_to_nat(1u);
v___x_3371_ = lean_nat_sub(v_nargs_3366_, v___x_3370_);
lean_dec(v_nargs_3366_);
v___x_3372_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3355_, v___x_3369_, v___x_3371_);
v___x_3373_ = lean_array_push(v___x_3372_, v_a_3363_);
v___x_3374_ = l_Lean_mkAppN(v___x_3367_, v___x_3373_);
lean_dec_ref(v___x_3373_);
lean_inc(v_val_3200_);
v___x_3375_ = l_Lean_LocalDecl_toExpr(v_val_3200_);
v___x_3376_ = l_Lean_Meta_mkAbsurd(v_a_3365_, v___x_3375_, v___x_3374_, v___y_3354_, v___y_3352_, v___y_3357_, v___y_3351_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3396_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3396_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3396_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; 
lean_inc(v_mvarId_3169_);
v___x_3381_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3169_, v_a_3377_, v___y_3352_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3393_; 
lean_dec_ref(v___x_3320_);
lean_dec(v_val_3200_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; 
v_unused_3394_ = lean_ctor_get(v___x_3381_, 0);
lean_dec(v_unused_3394_);
v___x_3383_ = v___x_3381_;
v_isShared_3384_ = v_isSharedCheck_3393_;
goto v_resetjp_3382_;
}
else
{
lean_dec(v___x_3381_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3393_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3385_ = lean_box(v___x_3179_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set_tag(v___x_3383_, 1);
lean_ctor_set(v___x_3383_, 0, v___x_3385_);
v___x_3387_ = v___x_3383_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___x_3204_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3388_);
v___x_3390_ = v___x_3379_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
v_a_3186_ = v___x_3390_;
goto v___jp_3185_;
}
}
}
}
else
{
lean_object* v_a_3395_; 
lean_del_object(v___x_3379_);
v_a_3395_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3381_, 1);
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v_a_3347_ = v_a_3395_;
goto v___jp_3340_;
}
}
}
else
{
lean_object* v_a_3397_; 
v_a_3397_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3376_, 1);
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v_a_3347_ = v_a_3397_;
goto v___jp_3340_;
}
}
else
{
lean_object* v_a_3398_; 
lean_dec(v_a_3363_);
lean_dec_ref(v___y_3355_);
v_a_3398_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3364_, 1);
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v_a_3347_ = v_a_3398_;
goto v___jp_3340_;
}
}
else
{
lean_object* v_a_3399_; 
lean_dec_ref(v___y_3355_);
v_a_3399_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3362_, 1);
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v_a_3347_ = v_a_3399_;
goto v___jp_3340_;
}
}
}
else
{
lean_object* v_a_3400_; 
lean_dec_ref(v___y_3355_);
v_a_3400_ = lean_ctor_get(v___y_3358_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___y_3358_, 1);
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v_a_3347_ = v_a_3400_;
goto v___jp_3340_;
}
}
v___jp_3401_:
{
lean_object* v___x_3408_; 
lean_inc_ref(v___x_3320_);
v___x_3408_ = l_Lean_Meta_mkDecide(v___x_3320_, v___y_3405_, v___y_3403_, v___y_3407_, v___y_3402_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; uint8_t v_transparency_3411_; uint8_t v___x_3412_; uint8_t v___x_3413_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v___x_3410_ = l_Lean_Meta_Context_config(v___y_3405_);
v_transparency_3411_ = lean_ctor_get_uint8(v___x_3410_, 9);
lean_dec_ref(v___x_3410_);
v___x_3412_ = 1;
v___x_3413_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
lean_object* v_keyedConfig_3414_; uint8_t v_trackZetaDelta_3415_; lean_object* v_zetaDeltaSet_3416_; lean_object* v_lctx_3417_; lean_object* v_localInstances_3418_; lean_object* v_defEqCtx_x3f_3419_; lean_object* v_synthPendingDepth_3420_; lean_object* v_customCanUnfoldPredicate_x3f_3421_; uint8_t v_univApprox_3422_; uint8_t v_inTypeClassResolution_3423_; uint8_t v_cacheInferType_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v_keyedConfig_3414_ = lean_ctor_get(v___y_3405_, 0);
v_trackZetaDelta_3415_ = lean_ctor_get_uint8(v___y_3405_, sizeof(void*)*7);
v_zetaDeltaSet_3416_ = lean_ctor_get(v___y_3405_, 1);
v_lctx_3417_ = lean_ctor_get(v___y_3405_, 2);
v_localInstances_3418_ = lean_ctor_get(v___y_3405_, 3);
v_defEqCtx_x3f_3419_ = lean_ctor_get(v___y_3405_, 4);
v_synthPendingDepth_3420_ = lean_ctor_get(v___y_3405_, 5);
v_customCanUnfoldPredicate_x3f_3421_ = lean_ctor_get(v___y_3405_, 6);
v_univApprox_3422_ = lean_ctor_get_uint8(v___y_3405_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3423_ = lean_ctor_get_uint8(v___y_3405_, sizeof(void*)*7 + 2);
v_cacheInferType_3424_ = lean_ctor_get_uint8(v___y_3405_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3414_);
v___x_3425_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3412_, v_keyedConfig_3414_);
lean_inc(v_customCanUnfoldPredicate_x3f_3421_);
lean_inc(v_synthPendingDepth_3420_);
lean_inc(v_defEqCtx_x3f_3419_);
lean_inc_ref(v_localInstances_3418_);
lean_inc_ref(v_lctx_3417_);
lean_inc(v_zetaDeltaSet_3416_);
v___x_3426_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
lean_ctor_set(v___x_3426_, 1, v_zetaDeltaSet_3416_);
lean_ctor_set(v___x_3426_, 2, v_lctx_3417_);
lean_ctor_set(v___x_3426_, 3, v_localInstances_3418_);
lean_ctor_set(v___x_3426_, 4, v_defEqCtx_x3f_3419_);
lean_ctor_set(v___x_3426_, 5, v_synthPendingDepth_3420_);
lean_ctor_set(v___x_3426_, 6, v_customCanUnfoldPredicate_x3f_3421_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*7, v_trackZetaDelta_3415_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*7 + 1, v_univApprox_3422_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3423_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*7 + 3, v_cacheInferType_3424_);
lean_inc(v___y_3402_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3403_);
lean_inc(v_a_3409_);
v___x_3427_ = lean_whnf(v_a_3409_, v___x_3426_, v___y_3403_, v___y_3407_, v___y_3402_);
v___y_3351_ = v___y_3402_;
v___y_3352_ = v___y_3403_;
v___y_3353_ = v___y_3404_;
v___y_3354_ = v___y_3405_;
v___y_3355_ = v_a_3409_;
v___y_3356_ = v___y_3406_;
v___y_3357_ = v___y_3407_;
v___y_3358_ = v___x_3427_;
goto v___jp_3350_;
}
else
{
lean_object* v___x_3428_; 
lean_inc(v___y_3402_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3403_);
lean_inc_ref(v___y_3405_);
lean_inc(v_a_3409_);
v___x_3428_ = lean_whnf(v_a_3409_, v___y_3405_, v___y_3403_, v___y_3407_, v___y_3402_);
v___y_3351_ = v___y_3402_;
v___y_3352_ = v___y_3403_;
v___y_3353_ = v___y_3404_;
v___y_3354_ = v___y_3405_;
v___y_3355_ = v_a_3409_;
v___y_3356_ = v___y_3406_;
v___y_3357_ = v___y_3407_;
v___y_3358_ = v___x_3428_;
goto v___jp_3350_;
}
}
else
{
lean_object* v_a_3429_; 
v_a_3429_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3408_, 1);
v___y_3341_ = v___y_3402_;
v___y_3342_ = v___y_3403_;
v___y_3343_ = v___y_3404_;
v___y_3344_ = v___y_3405_;
v___y_3345_ = v___y_3407_;
v___y_3346_ = v___y_3406_;
v_a_3347_ = v_a_3429_;
goto v___jp_3340_;
}
}
v___jp_3430_:
{
if (v___y_3437_ == 0)
{
v___y_3322_ = v___y_3433_;
v___y_3323_ = v___y_3435_;
v___y_3324_ = v___y_3434_;
v___y_3325_ = v___y_3432_;
v___y_3326_ = v___y_3436_;
v___y_3327_ = v___y_3431_;
goto v___jp_3321_;
}
else
{
v___y_3402_ = v___y_3431_;
v___y_3403_ = v___y_3432_;
v___y_3404_ = v___y_3433_;
v___y_3405_ = v___y_3434_;
v___y_3406_ = v___y_3435_;
v___y_3407_ = v___y_3436_;
goto v___jp_3401_;
}
}
v___jp_3438_:
{
if (v___y_3446_ == 0)
{
lean_dec_ref(v___y_3439_);
v___y_3431_ = v___y_3440_;
v___y_3432_ = v___y_3441_;
v___y_3433_ = v___y_3442_;
v___y_3434_ = v___y_3443_;
v___y_3435_ = v___y_3445_;
v___y_3436_ = v___y_3444_;
v___y_3437_ = v___x_3275_;
goto v___jp_3430_;
}
else
{
uint8_t v___x_3447_; 
v___x_3447_ = l_Lean_Expr_hasFVar(v___y_3439_);
lean_dec_ref(v___y_3439_);
if (v___x_3447_ == 0)
{
v___y_3402_ = v___y_3440_;
v___y_3403_ = v___y_3441_;
v___y_3404_ = v___y_3442_;
v___y_3405_ = v___y_3443_;
v___y_3406_ = v___y_3445_;
v___y_3407_ = v___y_3444_;
goto v___jp_3401_;
}
else
{
v___y_3431_ = v___y_3440_;
v___y_3432_ = v___y_3441_;
v___y_3433_ = v___y_3442_;
v___y_3434_ = v___y_3443_;
v___y_3435_ = v___y_3445_;
v___y_3436_ = v___y_3444_;
v___y_3437_ = v___x_3275_;
goto v___jp_3430_;
}
}
}
v___jp_3448_:
{
lean_object* v___x_3456_; 
lean_inc_ref(v___x_3320_);
v___x_3456_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3320_, v___y_3450_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; uint8_t v___x_3458_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = l_Lean_Expr_hasMVar(v_a_3457_);
if (v___x_3458_ == 0)
{
v___y_3439_ = v_a_3457_;
v___y_3440_ = v___y_3449_;
v___y_3441_ = v___y_3450_;
v___y_3442_ = v___y_3451_;
v___y_3443_ = v___y_3452_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3454_;
v___y_3446_ = v___y_3455_;
goto v___jp_3438_;
}
else
{
v___y_3439_ = v_a_3457_;
v___y_3440_ = v___y_3449_;
v___y_3441_ = v___y_3450_;
v___y_3442_ = v___y_3451_;
v___y_3443_ = v___y_3452_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3454_;
v___y_3446_ = v___x_3275_;
goto v___jp_3438_;
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v___x_3320_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3459_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3456_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3456_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
v___jp_3467_:
{
if (v___y_3474_ == 0)
{
v___y_3322_ = v___y_3470_;
v___y_3323_ = v___y_3472_;
v___y_3324_ = v___y_3471_;
v___y_3325_ = v___y_3469_;
v___y_3326_ = v___y_3473_;
v___y_3327_ = v___y_3468_;
goto v___jp_3321_;
}
else
{
v___y_3449_ = v___y_3468_;
v___y_3450_ = v___y_3469_;
v___y_3451_ = v___y_3470_;
v___y_3452_ = v___y_3471_;
v___y_3453_ = v___y_3473_;
v___y_3454_ = v___y_3472_;
v___y_3455_ = v___y_3474_;
goto v___jp_3448_;
}
}
v___jp_3475_:
{
uint8_t v_useDecide_3482_; 
v_useDecide_3482_ = lean_ctor_get_uint8(v_config_3168_, sizeof(void*)*1);
if (v_useDecide_3482_ == 0)
{
v___y_3468_ = v___y_3481_;
v___y_3469_ = v___y_3479_;
v___y_3470_ = v___y_3476_;
v___y_3471_ = v___y_3478_;
v___y_3472_ = v_isHEq_3477_;
v___y_3473_ = v___y_3480_;
v___y_3474_ = v___x_3275_;
goto v___jp_3467_;
}
else
{
uint8_t v___x_3483_; 
v___x_3483_ = l_Lean_Expr_hasFVar(v___x_3320_);
if (v___x_3483_ == 0)
{
v___y_3449_ = v___y_3481_;
v___y_3450_ = v___y_3479_;
v___y_3451_ = v___y_3476_;
v___y_3452_ = v___y_3478_;
v___y_3453_ = v___y_3480_;
v___y_3454_ = v_isHEq_3477_;
v___y_3455_ = v_useDecide_3482_;
goto v___jp_3448_;
}
else
{
v___y_3468_ = v___y_3481_;
v___y_3469_ = v___y_3479_;
v___y_3470_ = v___y_3476_;
v___y_3471_ = v___y_3478_;
v___y_3472_ = v_isHEq_3477_;
v___y_3473_ = v___y_3480_;
v___y_3474_ = v___x_3275_;
goto v___jp_3467_;
}
}
}
v___jp_3484_:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Meta_isExprDefEq(v___y_3486_, v___y_3487_, v___y_3489_, v___y_3485_, v___y_3491_, v___y_3490_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; uint8_t v___x_3494_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___x_3494_ = lean_unbox(v_a_3493_);
lean_dec(v_a_3493_);
if (v___x_3494_ == 0)
{
v___y_3476_ = v___y_3488_;
v_isHEq_3477_ = v___x_3179_;
v___y_3478_ = v___y_3489_;
v___y_3479_ = v___y_3485_;
v___y_3480_ = v___y_3491_;
v___y_3481_ = v___y_3490_;
goto v___jp_3475_;
}
else
{
lean_object* v___x_3495_; 
lean_dec_ref(v___x_3320_);
lean_dec_ref(v_config_3168_);
lean_inc(v_mvarId_3169_);
v___x_3495_ = l_Lean_MVarId_getType(v_mvarId_3169_, v___y_3489_, v___y_3485_, v___y_3491_, v___y_3490_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3497_ = l_Lean_LocalDecl_toExpr(v_val_3200_);
v___x_3498_ = l_Lean_Meta_mkEqOfHEq(v___x_3497_, v___x_3179_, v___y_3489_, v___y_3485_, v___y_3491_, v___y_3490_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3500_ = l_Lean_Meta_mkNoConfusion(v_a_3496_, v_a_3499_, v___y_3489_, v___y_3485_, v___y_3491_, v___y_3490_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3169_, v_a_3501_, v___y_3485_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_dec_ref_known(v___x_3502_, 1);
v___x_3503_ = lean_box(v___x_3179_);
v___x_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
v___x_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v___x_3204_);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
v_a_3186_ = v___x_3506_;
goto v___jp_3185_;
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
v_a_3507_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3502_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3502_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3515_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3500_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3500_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec(v_a_3496_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3523_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3498_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3498_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3531_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3495_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3495_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref(v___x_3320_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3539_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3492_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3492_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
v___jp_3547_:
{
lean_object* v___x_3553_; 
lean_inc_ref(v___x_3320_);
v___x_3553_ = l_Lean_Meta_matchHEq_x3f(v___x_3320_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
if (lean_obj_tag(v_a_3554_) == 1)
{
lean_object* v_val_3555_; lean_object* v_snd_3556_; lean_object* v_snd_3557_; lean_object* v_fst_3558_; lean_object* v_fst_3559_; lean_object* v_fst_3560_; lean_object* v_snd_3561_; lean_object* v___x_3562_; 
v_val_3555_ = lean_ctor_get(v_a_3554_, 0);
lean_inc(v_val_3555_);
lean_dec_ref_known(v_a_3554_, 1);
v_snd_3556_ = lean_ctor_get(v_val_3555_, 1);
lean_inc(v_snd_3556_);
v_snd_3557_ = lean_ctor_get(v_snd_3556_, 1);
lean_inc(v_snd_3557_);
v_fst_3558_ = lean_ctor_get(v_val_3555_, 0);
lean_inc(v_fst_3558_);
lean_dec(v_val_3555_);
v_fst_3559_ = lean_ctor_get(v_snd_3556_, 0);
lean_inc(v_fst_3559_);
lean_dec(v_snd_3556_);
v_fst_3560_ = lean_ctor_get(v_snd_3557_, 0);
lean_inc(v_fst_3560_);
v_snd_3561_ = lean_ctor_get(v_snd_3557_, 1);
lean_inc(v_snd_3561_);
lean_dec(v_snd_3557_);
v___x_3562_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3559_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3562_, 1);
if (lean_obj_tag(v_a_3563_) == 1)
{
lean_object* v_val_3564_; lean_object* v___x_3565_; 
v_val_3564_ = lean_ctor_get(v_a_3563_, 0);
lean_inc(v_val_3564_);
lean_dec_ref_known(v_a_3563_, 1);
v___x_3565_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3561_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
if (lean_obj_tag(v_a_3566_) == 1)
{
lean_object* v_toConstantVal_3567_; lean_object* v_val_3568_; lean_object* v_toConstantVal_3569_; lean_object* v_name_3570_; lean_object* v_name_3571_; uint8_t v___x_3572_; 
v_toConstantVal_3567_ = lean_ctor_get(v_val_3564_, 0);
lean_inc_ref(v_toConstantVal_3567_);
lean_dec(v_val_3564_);
v_val_3568_ = lean_ctor_get(v_a_3566_, 0);
lean_inc(v_val_3568_);
lean_dec_ref_known(v_a_3566_, 1);
v_toConstantVal_3569_ = lean_ctor_get(v_val_3568_, 0);
lean_inc_ref(v_toConstantVal_3569_);
lean_dec(v_val_3568_);
v_name_3570_ = lean_ctor_get(v_toConstantVal_3567_, 0);
lean_inc(v_name_3570_);
lean_dec_ref(v_toConstantVal_3567_);
v_name_3571_ = lean_ctor_get(v_toConstantVal_3569_, 0);
lean_inc(v_name_3571_);
lean_dec_ref(v_toConstantVal_3569_);
v___x_3572_ = lean_name_eq(v_name_3570_, v_name_3571_);
lean_dec(v_name_3571_);
lean_dec(v_name_3570_);
if (v___x_3572_ == 0)
{
v___y_3485_ = v___y_3550_;
v___y_3486_ = v_fst_3558_;
v___y_3487_ = v_fst_3560_;
v___y_3488_ = v_isEq_3548_;
v___y_3489_ = v___y_3549_;
v___y_3490_ = v___y_3552_;
v___y_3491_ = v___y_3551_;
goto v___jp_3484_;
}
else
{
if (v___x_3275_ == 0)
{
lean_dec(v_fst_3560_);
lean_dec(v_fst_3558_);
v___y_3476_ = v_isEq_3548_;
v_isHEq_3477_ = v___x_3179_;
v___y_3478_ = v___y_3549_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
goto v___jp_3475_;
}
else
{
v___y_3485_ = v___y_3550_;
v___y_3486_ = v_fst_3558_;
v___y_3487_ = v_fst_3560_;
v___y_3488_ = v_isEq_3548_;
v___y_3489_ = v___y_3549_;
v___y_3490_ = v___y_3552_;
v___y_3491_ = v___y_3551_;
goto v___jp_3484_;
}
}
}
else
{
lean_dec(v_a_3566_);
lean_dec(v_val_3564_);
lean_dec(v_fst_3560_);
lean_dec(v_fst_3558_);
v___y_3476_ = v_isEq_3548_;
v_isHEq_3477_ = v___x_3179_;
v___y_3478_ = v___y_3549_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
goto v___jp_3475_;
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec(v_val_3564_);
lean_dec(v_fst_3560_);
lean_dec(v_fst_3558_);
lean_dec_ref(v___x_3320_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3573_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3565_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3565_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
else
{
lean_dec(v_a_3563_);
lean_dec(v_snd_3561_);
lean_dec(v_fst_3560_);
lean_dec(v_fst_3558_);
v___y_3476_ = v_isEq_3548_;
v_isHEq_3477_ = v___x_3179_;
v___y_3478_ = v___y_3549_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
goto v___jp_3475_;
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v_snd_3561_);
lean_dec(v_fst_3560_);
lean_dec(v_fst_3558_);
lean_dec_ref(v___x_3320_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3581_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3562_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3562_);
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
else
{
lean_dec(v_a_3554_);
v___y_3476_ = v_isEq_3548_;
v_isHEq_3477_ = v___x_3275_;
v___y_3478_ = v___y_3549_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
v___y_3481_ = v___y_3552_;
goto v___jp_3475_;
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref(v___x_3320_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3589_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3553_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3553_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
v___jp_3597_:
{
lean_object* v___x_3602_; 
lean_inc_ref(v___x_3320_);
v___x_3602_ = l_Lean_Meta_matchEq_x3f(v___x_3320_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
if (lean_obj_tag(v_a_3603_) == 1)
{
lean_object* v_val_3604_; lean_object* v_snd_3605_; lean_object* v_fst_3606_; lean_object* v_snd_3607_; lean_object* v___x_3608_; 
v_val_3604_ = lean_ctor_get(v_a_3603_, 0);
lean_inc(v_val_3604_);
lean_dec_ref_known(v_a_3603_, 1);
v_snd_3605_ = lean_ctor_get(v_val_3604_, 1);
lean_inc(v_snd_3605_);
lean_dec(v_val_3604_);
v_fst_3606_ = lean_ctor_get(v_snd_3605_, 0);
lean_inc(v_fst_3606_);
v_snd_3607_ = lean_ctor_get(v_snd_3605_, 1);
lean_inc(v_snd_3607_);
lean_dec(v_snd_3605_);
v___x_3608_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3606_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
if (lean_obj_tag(v_a_3609_) == 1)
{
lean_object* v_val_3610_; lean_object* v___x_3611_; 
v_val_3610_ = lean_ctor_get(v_a_3609_, 0);
lean_inc(v_val_3610_);
lean_dec_ref_known(v_a_3609_, 1);
v___x_3611_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3607_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3611_, 1);
if (lean_obj_tag(v_a_3612_) == 1)
{
lean_object* v_toConstantVal_3613_; lean_object* v_val_3614_; lean_object* v_toConstantVal_3615_; lean_object* v_name_3616_; lean_object* v_name_3617_; uint8_t v___x_3618_; 
v_toConstantVal_3613_ = lean_ctor_get(v_val_3610_, 0);
lean_inc_ref(v_toConstantVal_3613_);
lean_dec(v_val_3610_);
v_val_3614_ = lean_ctor_get(v_a_3612_, 0);
lean_inc(v_val_3614_);
lean_dec_ref_known(v_a_3612_, 1);
v_toConstantVal_3615_ = lean_ctor_get(v_val_3614_, 0);
lean_inc_ref(v_toConstantVal_3615_);
lean_dec(v_val_3614_);
v_name_3616_ = lean_ctor_get(v_toConstantVal_3613_, 0);
lean_inc(v_name_3616_);
lean_dec_ref(v_toConstantVal_3613_);
v_name_3617_ = lean_ctor_get(v_toConstantVal_3615_, 0);
lean_inc(v_name_3617_);
lean_dec_ref(v_toConstantVal_3615_);
v___x_3618_ = lean_name_eq(v_name_3616_, v_name_3617_);
lean_dec(v_name_3617_);
lean_dec(v_name_3616_);
if (v___x_3618_ == 0)
{
lean_dec_ref(v___x_3320_);
lean_dec_ref(v_config_3168_);
v___y_3206_ = v___y_3600_;
v___y_3207_ = v___y_3601_;
v___y_3208_ = v___y_3598_;
v___y_3209_ = v___y_3599_;
goto v___jp_3205_;
}
else
{
if (v___x_3275_ == 0)
{
lean_del_object(v___x_3202_);
v_isEq_3548_ = v___x_3179_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
goto v___jp_3547_;
}
else
{
lean_dec_ref(v___x_3320_);
lean_dec_ref(v_config_3168_);
v___y_3206_ = v___y_3600_;
v___y_3207_ = v___y_3601_;
v___y_3208_ = v___y_3598_;
v___y_3209_ = v___y_3599_;
goto v___jp_3205_;
}
}
}
else
{
lean_dec(v_a_3612_);
lean_dec(v_val_3610_);
lean_del_object(v___x_3202_);
v_isEq_3548_ = v___x_3179_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
goto v___jp_3547_;
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec(v_val_3610_);
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3619_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3611_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3611_);
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
lean_dec(v_a_3609_);
lean_dec(v_snd_3607_);
lean_del_object(v___x_3202_);
v_isEq_3548_ = v___x_3179_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
goto v___jp_3547_;
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec(v_snd_3607_);
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3627_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3608_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3608_);
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
else
{
lean_dec(v_a_3603_);
lean_del_object(v___x_3202_);
v_isEq_3548_ = v___x_3275_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
v___y_3552_ = v___y_3601_;
goto v___jp_3547_;
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3635_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3602_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3602_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
v___jp_3643_:
{
lean_object* v___x_3648_; 
lean_inc_ref(v___x_3320_);
v___x_3648_ = l_Lean_refutableHasNotBit_x3f(v___x_3320_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref_known(v___x_3648_, 1);
if (lean_obj_tag(v_a_3649_) == 1)
{
lean_object* v_val_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec_ref(v_config_3168_);
v_val_3650_ = lean_ctor_get(v_a_3649_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_a_3649_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3652_ = v_a_3649_;
v_isShared_3653_ = v_isSharedCheck_3690_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_val_3650_);
lean_dec(v_a_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3690_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; 
lean_inc(v_mvarId_3169_);
v___x_3654_ = l_Lean_MVarId_getType(v_mvarId_3169_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3654_, 1);
v___x_3656_ = l_Lean_LocalDecl_toExpr(v_val_3200_);
v___x_3657_ = l_Lean_Meta_mkAbsurd(v_a_3655_, v_val_3650_, v___x_3656_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3659_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v___x_3657_, 1);
v___x_3659_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3169_, v_a_3658_, v___y_3645_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3662_; 
lean_dec_ref_known(v___x_3659_, 1);
v___x_3660_ = lean_box(v___x_3179_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3660_);
v___x_3662_ = v___x_3652_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
lean_ctor_set(v___x_3663_, 1, v___x_3204_);
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
v_a_3186_ = v___x_3664_;
goto v___jp_3185_;
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_del_object(v___x_3652_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
v_a_3666_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3659_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3659_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_del_object(v___x_3652_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3674_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3657_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3657_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_del_object(v___x_3652_);
lean_dec(v_val_3650_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3682_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3654_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3654_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
else
{
lean_object* v___x_3691_; 
lean_dec(v_a_3649_);
lean_inc_ref(v___x_3320_);
v___x_3691_ = l_Lean_Meta_matchNe_x3f(v___x_3320_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v___x_3691_, 1);
if (lean_obj_tag(v_a_3692_) == 1)
{
lean_object* v_val_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3763_; 
v_val_3693_ = lean_ctor_get(v_a_3692_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_a_3692_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3695_ = v_a_3692_;
v_isShared_3696_ = v_isSharedCheck_3763_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_val_3693_);
lean_dec(v_a_3692_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3763_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v_snd_3697_; lean_object* v_fst_3698_; lean_object* v_snd_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3762_; 
v_snd_3697_ = lean_ctor_get(v_val_3693_, 1);
lean_inc(v_snd_3697_);
lean_dec(v_val_3693_);
v_fst_3698_ = lean_ctor_get(v_snd_3697_, 0);
v_snd_3699_ = lean_ctor_get(v_snd_3697_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_snd_3697_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3701_ = v_snd_3697_;
v_isShared_3702_ = v_isSharedCheck_3762_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_snd_3699_);
lean_inc(v_fst_3698_);
lean_dec(v_snd_3697_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3762_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; 
lean_inc(v_fst_3698_);
v___x_3703_ = l_Lean_Meta_isExprDefEq(v_fst_3698_, v_snd_3699_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; uint8_t v___x_3705_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_a_3704_);
lean_dec_ref_known(v___x_3703_, 1);
v___x_3705_ = lean_unbox(v_a_3704_);
lean_dec(v_a_3704_);
if (v___x_3705_ == 0)
{
lean_del_object(v___x_3701_);
lean_dec(v_fst_3698_);
lean_del_object(v___x_3695_);
v___y_3598_ = v___y_3644_;
v___y_3599_ = v___y_3645_;
v___y_3600_ = v___y_3646_;
v___y_3601_ = v___y_3647_;
goto v___jp_3597_;
}
else
{
lean_object* v___x_3706_; 
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec_ref(v_config_3168_);
lean_inc(v_mvarId_3169_);
v___x_3706_ = l_Lean_MVarId_getType(v_mvarId_3169_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3708_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v___x_3708_ = l_Lean_Meta_mkEqRefl(v_fst_3698_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3710_ = l_Lean_LocalDecl_toExpr(v_val_3200_);
v___x_3711_ = l_Lean_Meta_mkAbsurd(v_a_3707_, v_a_3709_, v___x_3710_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v___x_3713_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3169_, v_a_3712_, v___y_3645_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3716_; 
lean_dec_ref_known(v___x_3713_, 1);
v___x_3714_ = lean_box(v___x_3179_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 0, v___x_3714_);
v___x_3716_ = v___x_3695_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3718_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___x_3204_);
lean_ctor_set(v___x_3701_, 0, v___x_3716_);
v___x_3718_ = v___x_3701_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3716_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v___x_3204_);
v___x_3718_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
v_a_3186_ = v___x_3719_;
goto v___jp_3185_;
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_del_object(v___x_3701_);
lean_del_object(v___x_3695_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
v_a_3722_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3713_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3713_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_del_object(v___x_3701_);
lean_del_object(v___x_3695_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3730_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3711_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3711_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3707_);
lean_del_object(v___x_3701_);
lean_del_object(v___x_3695_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3738_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3708_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3708_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_del_object(v___x_3701_);
lean_dec(v_fst_3698_);
lean_del_object(v___x_3695_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3746_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3706_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3706_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_del_object(v___x_3701_);
lean_dec(v_fst_3698_);
lean_del_object(v___x_3695_);
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3754_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3703_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3703_);
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
}
}
else
{
lean_dec(v_a_3692_);
v___y_3598_ = v___y_3644_;
v___y_3599_ = v___y_3645_;
v___y_3600_ = v___y_3646_;
v___y_3601_ = v___y_3647_;
goto v___jp_3597_;
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3764_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3691_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3691_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3772_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3648_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3648_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
else
{
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
v_a_3194_ = v___x_3246_;
goto v___jp_3193_;
}
v___jp_3205_:
{
lean_object* v___x_3210_; 
lean_inc(v_mvarId_3169_);
v___x_3210_ = l_Lean_MVarId_getType(v_mvarId_3169_, v___y_3208_, v___y_3209_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v___x_3212_ = l_Lean_LocalDecl_toExpr(v_val_3200_);
v___x_3213_ = l_Lean_Meta_mkNoConfusion(v_a_3211_, v___x_3212_, v___y_3208_, v___y_3209_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3215_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v___x_3215_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3169_, v_a_3214_, v___y_3209_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3218_; 
lean_dec_ref_known(v___x_3215_, 1);
v___x_3216_ = lean_box(v___x_3179_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3216_);
v___x_3218_ = v___x_3202_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
lean_ctor_set(v___x_3219_, 1, v___x_3204_);
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
v_a_3186_ = v___x_3220_;
goto v___jp_3185_;
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_del_object(v___x_3202_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
v_a_3222_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3215_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3215_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_del_object(v___x_3202_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3230_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3213_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3213_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_del_object(v___x_3202_);
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
v_a_3238_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3210_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3210_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
v___jp_3247_:
{
lean_object* v_searchFuel_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_searchFuel_3252_ = lean_ctor_get(v_config_3168_, 0);
v___x_3253_ = l_Lean_LocalDecl_fvarId(v_val_3200_);
lean_dec(v_val_3200_);
lean_inc(v_searchFuel_3252_);
lean_inc(v_mvarId_3169_);
v___x_3254_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3169_, v___x_3253_, v_searchFuel_3252_, v___y_3250_, v___y_3248_, v___y_3251_, v___y_3249_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; uint8_t v___x_3256_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___x_3254_, 1);
v___x_3256_ = lean_unbox(v_a_3255_);
lean_dec(v_a_3255_);
if (v___x_3256_ == 0)
{
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
v_a_3194_ = v___x_3246_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v___x_3257_ = lean_box(v___x_3179_);
v___x_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
v___x_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
lean_ctor_set(v___x_3259_, 1, v___x_3204_);
v___x_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
v_a_3186_ = v___x_3260_;
goto v___jp_3185_;
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3261_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3254_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3254_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
v___jp_3269_:
{
if (v___y_3274_ == 0)
{
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
v_a_3194_ = v___x_3246_;
goto v___jp_3193_;
}
else
{
v___y_3248_ = v___y_3270_;
v___y_3249_ = v___y_3271_;
v___y_3250_ = v___y_3272_;
v___y_3251_ = v___y_3273_;
goto v___jp_3247_;
}
}
v___jp_3276_:
{
if (v___y_3281_ == 0)
{
v___y_3248_ = v___y_3277_;
v___y_3249_ = v___y_3278_;
v___y_3250_ = v___y_3279_;
v___y_3251_ = v___y_3280_;
goto v___jp_3247_;
}
else
{
v___y_3270_ = v___y_3277_;
v___y_3271_ = v___y_3278_;
v___y_3272_ = v___y_3279_;
v___y_3273_ = v___y_3280_;
v___y_3274_ = v___x_3275_;
goto v___jp_3269_;
}
}
v___jp_3282_:
{
if (v___y_3288_ == 0)
{
v___y_3270_ = v___y_3283_;
v___y_3271_ = v___y_3284_;
v___y_3272_ = v___y_3285_;
v___y_3273_ = v___y_3286_;
v___y_3274_ = v___x_3275_;
goto v___jp_3269_;
}
else
{
v___y_3277_ = v___y_3283_;
v___y_3278_ = v___y_3284_;
v___y_3279_ = v___y_3285_;
v___y_3280_ = v___y_3286_;
v___y_3281_ = v___y_3287_;
goto v___jp_3276_;
}
}
v___jp_3289_:
{
uint8_t v_emptyType_3296_; 
v_emptyType_3296_ = lean_ctor_get_uint8(v_config_3168_, sizeof(void*)*1 + 1);
if (v_emptyType_3296_ == 0)
{
v___y_3283_ = v___y_3293_;
v___y_3284_ = v___y_3295_;
v___y_3285_ = v___y_3292_;
v___y_3286_ = v___y_3294_;
v___y_3287_ = v___y_3291_;
v___y_3288_ = v___x_3275_;
goto v___jp_3282_;
}
else
{
if (v___y_3290_ == 0)
{
v___y_3277_ = v___y_3293_;
v___y_3278_ = v___y_3295_;
v___y_3279_ = v___y_3292_;
v___y_3280_ = v___y_3294_;
v___y_3281_ = v___y_3291_;
goto v___jp_3276_;
}
else
{
v___y_3283_ = v___y_3293_;
v___y_3284_ = v___y_3295_;
v___y_3285_ = v___y_3292_;
v___y_3286_ = v___y_3294_;
v___y_3287_ = v___y_3291_;
v___y_3288_ = v___x_3275_;
goto v___jp_3282_;
}
}
}
v___jp_3297_:
{
if (v___y_3304_ == 0)
{
v___y_3290_ = v___y_3299_;
v___y_3291_ = v___y_3303_;
v___y_3292_ = v___y_3302_;
v___y_3293_ = v___y_3301_;
v___y_3294_ = v___y_3298_;
v___y_3295_ = v___y_3300_;
goto v___jp_3289_;
}
else
{
lean_object* v___x_3305_; 
lean_inc(v_val_3200_);
lean_inc(v_mvarId_3169_);
v___x_3305_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3169_, v_val_3200_, v___y_3302_, v___y_3301_, v___y_3298_, v___y_3300_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; uint8_t v___x_3307_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3307_ = lean_unbox(v_a_3306_);
lean_dec(v_a_3306_);
if (v___x_3307_ == 0)
{
v___y_3290_ = v___y_3299_;
v___y_3291_ = v___y_3303_;
v___y_3292_ = v___y_3302_;
v___y_3293_ = v___y_3301_;
v___y_3294_ = v___y_3298_;
v___y_3295_ = v___y_3300_;
goto v___jp_3289_;
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec(v_val_3200_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v___x_3308_ = lean_box(v___x_3179_);
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
lean_ctor_set(v___x_3310_, 1, v___x_3204_);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
v_a_3186_ = v___x_3311_;
goto v___jp_3185_;
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec(v_val_3200_);
lean_del_object(v___x_3183_);
lean_dec(v_snd_3181_);
lean_dec(v_mvarId_3169_);
lean_dec_ref(v_config_3168_);
v_a_3312_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3305_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3305_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
}
}
v___jp_3185_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_a_3186_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3187_);
v___x_3189_ = v___x_3183_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_snd_3181_);
v___x_3189_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
return v___x_3190_;
}
}
v___jp_3193_:
{
lean_object* v___x_3195_; size_t v___x_3196_; size_t v___x_3197_; 
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3192_);
lean_ctor_set(v___x_3195_, 1, v_a_3194_);
v___x_3196_ = ((size_t)1ULL);
v___x_3197_ = lean_usize_add(v_i_3172_, v___x_3196_);
v_i_3172_ = v___x_3197_;
v_b_3173_ = v___x_3195_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3853_, lean_object* v_mvarId_3854_, lean_object* v_as_3855_, lean_object* v_sz_3856_, lean_object* v_i_3857_, lean_object* v_b_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
size_t v_sz_boxed_3864_; size_t v_i_boxed_3865_; lean_object* v_res_3866_; 
v_sz_boxed_3864_ = lean_unbox_usize(v_sz_3856_);
lean_dec(v_sz_3856_);
v_i_boxed_3865_ = lean_unbox_usize(v_i_3857_);
lean_dec(v_i_3857_);
v_res_3866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3853_, v_mvarId_3854_, v_as_3855_, v_sz_boxed_3864_, v_i_boxed_3865_, v_b_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec_ref(v_as_3855_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3867_, lean_object* v_mvarId_3868_, lean_object* v_as_3869_, size_t v_sz_3870_, size_t v_i_3871_, lean_object* v_b_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
uint8_t v___x_3878_; 
v___x_3878_ = lean_usize_dec_lt(v_i_3871_, v_sz_3870_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; 
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v_b_3872_);
return v___x_3879_;
}
else
{
lean_object* v_snd_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_4550_; 
v_snd_3880_ = lean_ctor_get(v_b_3872_, 1);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_b_3872_);
if (v_isSharedCheck_4550_ == 0)
{
lean_object* v_unused_4551_; 
v_unused_4551_ = lean_ctor_get(v_b_3872_, 0);
lean_dec(v_unused_4551_);
v___x_3882_ = v_b_3872_;
v_isShared_3883_ = v_isSharedCheck_4550_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_snd_3880_);
lean_dec(v_b_3872_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_4550_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v_a_3885_; lean_object* v___x_3891_; lean_object* v_a_3893_; lean_object* v_a_3898_; 
v___x_3891_ = lean_box(0);
v_a_3898_ = lean_array_uget(v_as_3869_, v_i_3871_);
if (lean_obj_tag(v_a_3898_) == 0)
{
lean_del_object(v___x_3882_);
v_a_3893_ = v_snd_3880_;
goto v___jp_3892_;
}
else
{
lean_object* v_val_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_4549_; 
v_val_3899_ = lean_ctor_get(v_a_3898_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v_a_3898_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_3901_ = v_a_3898_;
v_isShared_3902_ = v_isSharedCheck_4549_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_val_3899_);
lean_dec(v_a_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_4549_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___x_3945_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; uint8_t v___y_3973_; uint8_t v___x_3974_; lean_object* v___y_3976_; lean_object* v___y_3977_; uint8_t v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; uint8_t v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; uint8_t v___y_3987_; uint8_t v___y_3989_; uint8_t v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; uint8_t v___y_4001_; uint8_t v___y_4002_; uint8_t v___y_4003_; 
v___x_3903_ = lean_box(0);
v___x_3945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3974_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3899_);
if (v___x_3974_ == 0)
{
lean_object* v___x_4019_; uint8_t v___y_4021_; uint8_t v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4030_; lean_object* v___y_4031_; uint8_t v___y_4032_; lean_object* v___y_4033_; uint8_t v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; uint8_t v___y_4037_; lean_object* v___y_4040_; lean_object* v___y_4041_; uint8_t v___y_4042_; lean_object* v___y_4043_; uint8_t v___y_4044_; lean_object* v___y_4045_; lean_object* v_a_4046_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; uint8_t v___y_4053_; uint8_t v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4101_; lean_object* v___y_4102_; uint8_t v___y_4103_; uint8_t v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4130_; lean_object* v___y_4131_; uint8_t v___y_4132_; uint8_t v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; uint8_t v___y_4136_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; uint8_t v___y_4141_; lean_object* v___y_4142_; uint8_t v___y_4143_; lean_object* v___y_4144_; uint8_t v___y_4145_; lean_object* v___y_4148_; lean_object* v___y_4149_; uint8_t v___y_4150_; uint8_t v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; uint8_t v___y_4154_; lean_object* v___y_4167_; lean_object* v___y_4168_; uint8_t v___y_4169_; uint8_t v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; uint8_t v___y_4173_; uint8_t v___y_4175_; uint8_t v_isHEq_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; uint8_t v___y_4190_; uint8_t v_isEq_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___x_4479_; 
v___x_4019_ = l_Lean_LocalDecl_type(v_val_3899_);
lean_inc_ref(v___x_4019_);
v___x_4479_ = l_Lean_Meta_matchNot_x3f(v___x_4019_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref_known(v___x_4479_, 1);
if (lean_obj_tag(v_a_4480_) == 1)
{
lean_object* v_val_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4540_; 
v_val_4481_ = lean_ctor_get(v_a_4480_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v_a_4480_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4483_ = v_a_4480_;
v_isShared_4484_ = v_isSharedCheck_4540_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_val_4481_);
lean_dec(v_a_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4540_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4485_; 
v___x_4485_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4481_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
if (lean_obj_tag(v_a_4486_) == 1)
{
lean_object* v_val_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4531_; 
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec_ref(v_config_3867_);
v_val_4487_ = lean_ctor_get(v_a_4486_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v_a_4486_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4489_ = v_a_4486_;
v_isShared_4490_ = v_isSharedCheck_4531_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_val_4487_);
lean_dec(v_a_4486_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4531_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; 
lean_inc(v_mvarId_3868_);
v___x_4491_ = l_Lean_MVarId_getType(v_mvarId_3868_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v___x_4493_ = l_Lean_LocalDecl_toExpr(v_val_3899_);
v___x_4494_ = l_Lean_mkFVar(v_val_4487_);
v___x_4495_ = l_Lean_Expr_app___override(v___x_4493_, v___x_4494_);
v___x_4496_ = l_Lean_Meta_mkFalseElim(v_a_4492_, v___x_4495_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; lean_object* v___x_4498_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref_known(v___x_4496_, 1);
v___x_4498_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3868_, v_a_4497_, v___y_3874_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v___x_4499_; lean_object* v___x_4501_; 
lean_dec_ref_known(v___x_4498_, 1);
v___x_4499_ = lean_box(v___x_3878_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v___x_4499_);
v___x_4501_ = v___x_4489_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4499_);
v___x_4501_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4502_; lean_object* v___x_4504_; 
v___x_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
lean_ctor_set(v___x_4502_, 1, v___x_3903_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set_tag(v___x_4483_, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4502_);
v___x_4504_ = v___x_4483_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
v_a_3885_ = v___x_4504_;
goto v___jp_3884_;
}
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_del_object(v___x_4489_);
lean_del_object(v___x_4483_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
v_a_4507_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4498_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4498_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
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
lean_del_object(v___x_4489_);
lean_del_object(v___x_4483_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4515_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4496_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4496_);
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
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_del_object(v___x_4489_);
lean_dec(v_val_4487_);
lean_del_object(v___x_4483_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4523_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4491_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4491_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
}
else
{
lean_dec(v_a_4486_);
lean_del_object(v___x_4483_);
v___y_4343_ = v___y_3873_;
v___y_4344_ = v___y_3874_;
v___y_4345_ = v___y_3875_;
v___y_4346_ = v___y_3876_;
goto v___jp_4342_;
}
}
else
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4539_; 
lean_del_object(v___x_4483_);
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4532_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4534_ = v___x_4485_;
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4485_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4537_; 
if (v_isShared_4535_ == 0)
{
v___x_4537_ = v___x_4534_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
}
}
else
{
lean_dec(v_a_4480_);
v___y_4343_ = v___y_3873_;
v___y_4344_ = v___y_3874_;
v___y_4345_ = v___y_3875_;
v___y_4346_ = v___y_3876_;
goto v___jp_4342_;
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4541_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4479_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4479_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
v___jp_4020_:
{
uint8_t v_genDiseq_4027_; 
v_genDiseq_4027_ = lean_ctor_get_uint8(v_config_3867_, sizeof(void*)*1 + 2);
if (v_genDiseq_4027_ == 0)
{
lean_dec_ref(v___x_4019_);
v___y_3997_ = v___y_4026_;
v___y_3998_ = v___y_4025_;
v___y_3999_ = v___y_4024_;
v___y_4000_ = v___y_4023_;
v___y_4001_ = v___y_4021_;
v___y_4002_ = v___y_4022_;
v___y_4003_ = v___x_3974_;
goto v___jp_3996_;
}
else
{
uint8_t v___x_4028_; 
v___x_4028_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4019_);
v___y_3997_ = v___y_4026_;
v___y_3998_ = v___y_4025_;
v___y_3999_ = v___y_4024_;
v___y_4000_ = v___y_4023_;
v___y_4001_ = v___y_4021_;
v___y_4002_ = v___y_4022_;
v___y_4003_ = v___x_4028_;
goto v___jp_3996_;
}
}
v___jp_4029_:
{
if (v___y_4037_ == 0)
{
lean_dec_ref(v___y_4033_);
v___y_4021_ = v___y_4032_;
v___y_4022_ = v___y_4034_;
v___y_4023_ = v___y_4031_;
v___y_4024_ = v___y_4035_;
v___y_4025_ = v___y_4036_;
v___y_4026_ = v___y_4030_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4038_; 
lean_dec_ref(v___x_4019_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v___x_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___y_4033_);
return v___x_4038_;
}
}
v___jp_4039_:
{
uint8_t v___x_4047_; 
v___x_4047_ = l_Lean_Exception_isInterrupt(v_a_4046_);
if (v___x_4047_ == 0)
{
uint8_t v___x_4048_; 
lean_inc_ref(v_a_4046_);
v___x_4048_ = l_Lean_Exception_isRuntime(v_a_4046_);
v___y_4030_ = v___y_4040_;
v___y_4031_ = v___y_4041_;
v___y_4032_ = v___y_4042_;
v___y_4033_ = v_a_4046_;
v___y_4034_ = v___y_4044_;
v___y_4035_ = v___y_4043_;
v___y_4036_ = v___y_4045_;
v___y_4037_ = v___x_4048_;
goto v___jp_4029_;
}
else
{
v___y_4030_ = v___y_4040_;
v___y_4031_ = v___y_4041_;
v___y_4032_ = v___y_4042_;
v___y_4033_ = v_a_4046_;
v___y_4034_ = v___y_4044_;
v___y_4035_ = v___y_4043_;
v___y_4036_ = v___y_4045_;
v___y_4037_ = v___x_4047_;
goto v___jp_4029_;
}
}
v___jp_4049_:
{
if (lean_obj_tag(v___y_4057_) == 0)
{
lean_object* v_a_4058_; lean_object* v___x_4059_; uint8_t v___x_4060_; 
v_a_4058_ = lean_ctor_get(v___y_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref_known(v___y_4057_, 1);
v___x_4059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4060_ = l_Lean_Expr_isConstOf(v_a_4058_, v___x_4059_);
lean_dec(v_a_4058_);
if (v___x_4060_ == 0)
{
lean_dec_ref(v___y_4051_);
v___y_4021_ = v___y_4053_;
v___y_4022_ = v___y_4054_;
v___y_4023_ = v___y_4052_;
v___y_4024_ = v___y_4055_;
v___y_4025_ = v___y_4056_;
v___y_4026_ = v___y_4050_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4061_; 
lean_inc_ref(v___y_4051_);
v___x_4061_ = l_Lean_Meta_mkEqRefl(v___y_4051_, v___y_4052_, v___y_4055_, v___y_4056_, v___y_4050_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4063_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
lean_inc(v_mvarId_3868_);
v___x_4063_ = l_Lean_MVarId_getType(v_mvarId_3868_, v___y_4052_, v___y_4055_, v___y_4056_, v___y_4050_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v_nargs_4065_; lean_object* v___x_4066_; lean_object* v_dummy_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v_nargs_4065_ = l_Lean_Expr_getAppNumArgs(v___y_4051_);
v___x_4066_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_4065_);
v___x_4068_ = lean_mk_array(v_nargs_4065_, v_dummy_4067_);
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4070_ = lean_nat_sub(v_nargs_4065_, v___x_4069_);
lean_dec(v_nargs_4065_);
v___x_4071_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_4051_, v___x_4068_, v___x_4070_);
v___x_4072_ = lean_array_push(v___x_4071_, v_a_4062_);
v___x_4073_ = l_Lean_mkAppN(v___x_4066_, v___x_4072_);
lean_dec_ref(v___x_4072_);
lean_inc(v_val_3899_);
v___x_4074_ = l_Lean_LocalDecl_toExpr(v_val_3899_);
v___x_4075_ = l_Lean_Meta_mkAbsurd(v_a_4064_, v___x_4074_, v___x_4073_, v___y_4052_, v___y_4055_, v___y_4056_, v___y_4050_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4095_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4095_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4095_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4080_; 
lean_inc(v_mvarId_3868_);
v___x_4080_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3868_, v_a_4076_, v___y_4055_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4092_; 
lean_dec_ref(v___x_4019_);
lean_dec(v_val_3899_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v___x_4080_, 0);
lean_dec(v_unused_4093_);
v___x_4082_ = v___x_4080_;
v_isShared_4083_ = v_isSharedCheck_4092_;
goto v_resetjp_4081_;
}
else
{
lean_dec(v___x_4080_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4092_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; lean_object* v___x_4086_; 
v___x_4084_ = lean_box(v___x_3878_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set_tag(v___x_4082_, 1);
lean_ctor_set(v___x_4082_, 0, v___x_4084_);
v___x_4086_ = v___x_4082_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4084_);
v___x_4086_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
lean_object* v___x_4087_; lean_object* v___x_4089_; 
v___x_4087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
lean_ctor_set(v___x_4087_, 1, v___x_3903_);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 0, v___x_4087_);
v___x_4089_ = v___x_4078_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
v_a_3885_ = v___x_4089_;
goto v___jp_3884_;
}
}
}
}
else
{
lean_object* v_a_4094_; 
lean_del_object(v___x_4078_);
v_a_4094_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v___x_4080_, 1);
v___y_4040_ = v___y_4050_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4055_;
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4056_;
v_a_4046_ = v_a_4094_;
goto v___jp_4039_;
}
}
}
else
{
lean_object* v_a_4096_; 
v_a_4096_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4075_, 1);
v___y_4040_ = v___y_4050_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4055_;
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4056_;
v_a_4046_ = v_a_4096_;
goto v___jp_4039_;
}
}
else
{
lean_object* v_a_4097_; 
lean_dec(v_a_4062_);
lean_dec_ref(v___y_4051_);
v_a_4097_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4063_, 1);
v___y_4040_ = v___y_4050_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4055_;
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4056_;
v_a_4046_ = v_a_4097_;
goto v___jp_4039_;
}
}
else
{
lean_object* v_a_4098_; 
lean_dec_ref(v___y_4051_);
v_a_4098_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4061_, 1);
v___y_4040_ = v___y_4050_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4055_;
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4056_;
v_a_4046_ = v_a_4098_;
goto v___jp_4039_;
}
}
}
else
{
lean_object* v_a_4099_; 
lean_dec_ref(v___y_4051_);
v_a_4099_ = lean_ctor_get(v___y_4057_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___y_4057_, 1);
v___y_4040_ = v___y_4050_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4053_;
v___y_4043_ = v___y_4055_;
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4056_;
v_a_4046_ = v_a_4099_;
goto v___jp_4039_;
}
}
v___jp_4100_:
{
lean_object* v___x_4107_; 
lean_inc_ref(v___x_4019_);
v___x_4107_ = l_Lean_Meta_mkDecide(v___x_4019_, v___y_4102_, v___y_4105_, v___y_4106_, v___y_4101_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4109_; uint8_t v_transparency_4110_; uint8_t v___x_4111_; uint8_t v___x_4112_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_a_4108_);
lean_dec_ref_known(v___x_4107_, 1);
v___x_4109_ = l_Lean_Meta_Context_config(v___y_4102_);
v_transparency_4110_ = lean_ctor_get_uint8(v___x_4109_, 9);
lean_dec_ref(v___x_4109_);
v___x_4111_ = 1;
v___x_4112_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4110_, v___x_4111_);
if (v___x_4112_ == 0)
{
lean_object* v_keyedConfig_4113_; uint8_t v_trackZetaDelta_4114_; lean_object* v_zetaDeltaSet_4115_; lean_object* v_lctx_4116_; lean_object* v_localInstances_4117_; lean_object* v_defEqCtx_x3f_4118_; lean_object* v_synthPendingDepth_4119_; lean_object* v_customCanUnfoldPredicate_x3f_4120_; uint8_t v_univApprox_4121_; uint8_t v_inTypeClassResolution_4122_; uint8_t v_cacheInferType_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v_keyedConfig_4113_ = lean_ctor_get(v___y_4102_, 0);
v_trackZetaDelta_4114_ = lean_ctor_get_uint8(v___y_4102_, sizeof(void*)*7);
v_zetaDeltaSet_4115_ = lean_ctor_get(v___y_4102_, 1);
v_lctx_4116_ = lean_ctor_get(v___y_4102_, 2);
v_localInstances_4117_ = lean_ctor_get(v___y_4102_, 3);
v_defEqCtx_x3f_4118_ = lean_ctor_get(v___y_4102_, 4);
v_synthPendingDepth_4119_ = lean_ctor_get(v___y_4102_, 5);
v_customCanUnfoldPredicate_x3f_4120_ = lean_ctor_get(v___y_4102_, 6);
v_univApprox_4121_ = lean_ctor_get_uint8(v___y_4102_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4122_ = lean_ctor_get_uint8(v___y_4102_, sizeof(void*)*7 + 2);
v_cacheInferType_4123_ = lean_ctor_get_uint8(v___y_4102_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4113_);
v___x_4124_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4111_, v_keyedConfig_4113_);
lean_inc(v_customCanUnfoldPredicate_x3f_4120_);
lean_inc(v_synthPendingDepth_4119_);
lean_inc(v_defEqCtx_x3f_4118_);
lean_inc_ref(v_localInstances_4117_);
lean_inc_ref(v_lctx_4116_);
lean_inc(v_zetaDeltaSet_4115_);
v___x_4125_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
lean_ctor_set(v___x_4125_, 1, v_zetaDeltaSet_4115_);
lean_ctor_set(v___x_4125_, 2, v_lctx_4116_);
lean_ctor_set(v___x_4125_, 3, v_localInstances_4117_);
lean_ctor_set(v___x_4125_, 4, v_defEqCtx_x3f_4118_);
lean_ctor_set(v___x_4125_, 5, v_synthPendingDepth_4119_);
lean_ctor_set(v___x_4125_, 6, v_customCanUnfoldPredicate_x3f_4120_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*7, v_trackZetaDelta_4114_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*7 + 1, v_univApprox_4121_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4122_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*7 + 3, v_cacheInferType_4123_);
lean_inc(v___y_4101_);
lean_inc_ref(v___y_4106_);
lean_inc(v___y_4105_);
lean_inc(v_a_4108_);
v___x_4126_ = lean_whnf(v_a_4108_, v___x_4125_, v___y_4105_, v___y_4106_, v___y_4101_);
v___y_4050_ = v___y_4101_;
v___y_4051_ = v_a_4108_;
v___y_4052_ = v___y_4102_;
v___y_4053_ = v___y_4103_;
v___y_4054_ = v___y_4104_;
v___y_4055_ = v___y_4105_;
v___y_4056_ = v___y_4106_;
v___y_4057_ = v___x_4126_;
goto v___jp_4049_;
}
else
{
lean_object* v___x_4127_; 
lean_inc(v___y_4101_);
lean_inc_ref(v___y_4106_);
lean_inc(v___y_4105_);
lean_inc_ref(v___y_4102_);
lean_inc(v_a_4108_);
v___x_4127_ = lean_whnf(v_a_4108_, v___y_4102_, v___y_4105_, v___y_4106_, v___y_4101_);
v___y_4050_ = v___y_4101_;
v___y_4051_ = v_a_4108_;
v___y_4052_ = v___y_4102_;
v___y_4053_ = v___y_4103_;
v___y_4054_ = v___y_4104_;
v___y_4055_ = v___y_4105_;
v___y_4056_ = v___y_4106_;
v___y_4057_ = v___x_4127_;
goto v___jp_4049_;
}
}
else
{
lean_object* v_a_4128_; 
v_a_4128_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4107_, 1);
v___y_4040_ = v___y_4101_;
v___y_4041_ = v___y_4102_;
v___y_4042_ = v___y_4103_;
v___y_4043_ = v___y_4105_;
v___y_4044_ = v___y_4104_;
v___y_4045_ = v___y_4106_;
v_a_4046_ = v_a_4128_;
goto v___jp_4039_;
}
}
v___jp_4129_:
{
if (v___y_4136_ == 0)
{
v___y_4021_ = v___y_4132_;
v___y_4022_ = v___y_4133_;
v___y_4023_ = v___y_4131_;
v___y_4024_ = v___y_4134_;
v___y_4025_ = v___y_4135_;
v___y_4026_ = v___y_4130_;
goto v___jp_4020_;
}
else
{
v___y_4101_ = v___y_4130_;
v___y_4102_ = v___y_4131_;
v___y_4103_ = v___y_4132_;
v___y_4104_ = v___y_4133_;
v___y_4105_ = v___y_4134_;
v___y_4106_ = v___y_4135_;
goto v___jp_4100_;
}
}
v___jp_4137_:
{
if (v___y_4145_ == 0)
{
lean_dec_ref(v___y_4139_);
v___y_4130_ = v___y_4138_;
v___y_4131_ = v___y_4140_;
v___y_4132_ = v___y_4141_;
v___y_4133_ = v___y_4143_;
v___y_4134_ = v___y_4142_;
v___y_4135_ = v___y_4144_;
v___y_4136_ = v___x_3974_;
goto v___jp_4129_;
}
else
{
uint8_t v___x_4146_; 
v___x_4146_ = l_Lean_Expr_hasFVar(v___y_4139_);
lean_dec_ref(v___y_4139_);
if (v___x_4146_ == 0)
{
v___y_4101_ = v___y_4138_;
v___y_4102_ = v___y_4140_;
v___y_4103_ = v___y_4141_;
v___y_4104_ = v___y_4143_;
v___y_4105_ = v___y_4142_;
v___y_4106_ = v___y_4144_;
goto v___jp_4100_;
}
else
{
v___y_4130_ = v___y_4138_;
v___y_4131_ = v___y_4140_;
v___y_4132_ = v___y_4141_;
v___y_4133_ = v___y_4143_;
v___y_4134_ = v___y_4142_;
v___y_4135_ = v___y_4144_;
v___y_4136_ = v___x_3974_;
goto v___jp_4129_;
}
}
}
v___jp_4147_:
{
lean_object* v___x_4155_; 
lean_inc_ref(v___x_4019_);
v___x_4155_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4019_, v___y_4152_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; uint8_t v___x_4157_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
v___x_4157_ = l_Lean_Expr_hasMVar(v_a_4156_);
if (v___x_4157_ == 0)
{
v___y_4138_ = v___y_4148_;
v___y_4139_ = v_a_4156_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___y_4150_;
v___y_4142_ = v___y_4152_;
v___y_4143_ = v___y_4151_;
v___y_4144_ = v___y_4153_;
v___y_4145_ = v___y_4154_;
goto v___jp_4137_;
}
else
{
v___y_4138_ = v___y_4148_;
v___y_4139_ = v_a_4156_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___y_4150_;
v___y_4142_ = v___y_4152_;
v___y_4143_ = v___y_4151_;
v___y_4144_ = v___y_4153_;
v___y_4145_ = v___x_3974_;
goto v___jp_4137_;
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec_ref(v___x_4019_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4158_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4155_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4155_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
v___jp_4166_:
{
if (v___y_4173_ == 0)
{
v___y_4021_ = v___y_4169_;
v___y_4022_ = v___y_4170_;
v___y_4023_ = v___y_4168_;
v___y_4024_ = v___y_4171_;
v___y_4025_ = v___y_4172_;
v___y_4026_ = v___y_4167_;
goto v___jp_4020_;
}
else
{
v___y_4148_ = v___y_4167_;
v___y_4149_ = v___y_4168_;
v___y_4150_ = v___y_4169_;
v___y_4151_ = v___y_4170_;
v___y_4152_ = v___y_4171_;
v___y_4153_ = v___y_4172_;
v___y_4154_ = v___y_4173_;
goto v___jp_4147_;
}
}
v___jp_4174_:
{
uint8_t v_useDecide_4181_; 
v_useDecide_4181_ = lean_ctor_get_uint8(v_config_3867_, sizeof(void*)*1);
if (v_useDecide_4181_ == 0)
{
v___y_4167_ = v___y_4180_;
v___y_4168_ = v___y_4177_;
v___y_4169_ = v_isHEq_4176_;
v___y_4170_ = v___y_4175_;
v___y_4171_ = v___y_4178_;
v___y_4172_ = v___y_4179_;
v___y_4173_ = v___x_3974_;
goto v___jp_4166_;
}
else
{
uint8_t v___x_4182_; 
v___x_4182_ = l_Lean_Expr_hasFVar(v___x_4019_);
if (v___x_4182_ == 0)
{
v___y_4148_ = v___y_4180_;
v___y_4149_ = v___y_4177_;
v___y_4150_ = v_isHEq_4176_;
v___y_4151_ = v___y_4175_;
v___y_4152_ = v___y_4178_;
v___y_4153_ = v___y_4179_;
v___y_4154_ = v_useDecide_4181_;
goto v___jp_4147_;
}
else
{
v___y_4167_ = v___y_4180_;
v___y_4168_ = v___y_4177_;
v___y_4169_ = v_isHEq_4176_;
v___y_4170_ = v___y_4175_;
v___y_4171_ = v___y_4178_;
v___y_4172_ = v___y_4179_;
v___y_4173_ = v___x_3974_;
goto v___jp_4166_;
}
}
}
v___jp_4183_:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_Meta_isExprDefEq(v___y_4189_, v___y_4188_, v___y_4187_, v___y_4186_, v___y_4184_, v___y_4185_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; uint8_t v___x_4193_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v___x_4191_, 1);
v___x_4193_ = lean_unbox(v_a_4192_);
lean_dec(v_a_4192_);
if (v___x_4193_ == 0)
{
v___y_4175_ = v___y_4190_;
v_isHEq_4176_ = v___x_3878_;
v___y_4177_ = v___y_4187_;
v___y_4178_ = v___y_4186_;
v___y_4179_ = v___y_4184_;
v___y_4180_ = v___y_4185_;
goto v___jp_4174_;
}
else
{
lean_object* v___x_4194_; 
lean_dec_ref(v___x_4019_);
lean_dec_ref(v_config_3867_);
lean_inc(v_mvarId_3868_);
v___x_4194_ = l_Lean_MVarId_getType(v_mvarId_3868_, v___y_4187_, v___y_4186_, v___y_4184_, v___y_4185_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v___x_4196_ = l_Lean_LocalDecl_toExpr(v_val_3899_);
v___x_4197_ = l_Lean_Meta_mkEqOfHEq(v___x_4196_, v___x_3878_, v___y_4187_, v___y_4186_, v___y_4184_, v___y_4185_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4199_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4197_, 1);
v___x_4199_ = l_Lean_Meta_mkNoConfusion(v_a_4195_, v_a_4198_, v___y_4187_, v___y_4186_, v___y_4184_, v___y_4185_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3868_, v_a_4200_, v___y_4186_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec_ref_known(v___x_4201_, 1);
v___x_4202_ = lean_box(v___x_3878_);
v___x_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
lean_ctor_set(v___x_4204_, 1, v___x_3903_);
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
v_a_3885_ = v___x_4205_;
goto v___jp_3884_;
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
v_a_4206_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4201_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4201_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4214_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4199_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4199_);
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
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec(v_a_4195_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4222_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4197_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4197_);
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
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4230_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4194_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4194_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec_ref(v___x_4019_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4238_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4191_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4191_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
v___jp_4246_:
{
lean_object* v___x_4252_; 
lean_inc_ref(v___x_4019_);
v___x_4252_ = l_Lean_Meta_matchHEq_x3f(v___x_4019_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref_known(v___x_4252_, 1);
if (lean_obj_tag(v_a_4253_) == 1)
{
lean_object* v_val_4254_; lean_object* v_snd_4255_; lean_object* v_snd_4256_; lean_object* v_fst_4257_; lean_object* v_fst_4258_; lean_object* v_fst_4259_; lean_object* v_snd_4260_; lean_object* v___x_4261_; 
v_val_4254_ = lean_ctor_get(v_a_4253_, 0);
lean_inc(v_val_4254_);
lean_dec_ref_known(v_a_4253_, 1);
v_snd_4255_ = lean_ctor_get(v_val_4254_, 1);
lean_inc(v_snd_4255_);
v_snd_4256_ = lean_ctor_get(v_snd_4255_, 1);
lean_inc(v_snd_4256_);
v_fst_4257_ = lean_ctor_get(v_val_4254_, 0);
lean_inc(v_fst_4257_);
lean_dec(v_val_4254_);
v_fst_4258_ = lean_ctor_get(v_snd_4255_, 0);
lean_inc(v_fst_4258_);
lean_dec(v_snd_4255_);
v_fst_4259_ = lean_ctor_get(v_snd_4256_, 0);
lean_inc(v_fst_4259_);
v_snd_4260_ = lean_ctor_get(v_snd_4256_, 1);
lean_inc(v_snd_4260_);
lean_dec(v_snd_4256_);
v___x_4261_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4258_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___x_4261_, 1);
if (lean_obj_tag(v_a_4262_) == 1)
{
lean_object* v_val_4263_; lean_object* v___x_4264_; 
v_val_4263_ = lean_ctor_get(v_a_4262_, 0);
lean_inc(v_val_4263_);
lean_dec_ref_known(v_a_4262_, 1);
v___x_4264_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4260_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4264_, 1);
if (lean_obj_tag(v_a_4265_) == 1)
{
lean_object* v_toConstantVal_4266_; lean_object* v_val_4267_; lean_object* v_toConstantVal_4268_; lean_object* v_name_4269_; lean_object* v_name_4270_; uint8_t v___x_4271_; 
v_toConstantVal_4266_ = lean_ctor_get(v_val_4263_, 0);
lean_inc_ref(v_toConstantVal_4266_);
lean_dec(v_val_4263_);
v_val_4267_ = lean_ctor_get(v_a_4265_, 0);
lean_inc(v_val_4267_);
lean_dec_ref_known(v_a_4265_, 1);
v_toConstantVal_4268_ = lean_ctor_get(v_val_4267_, 0);
lean_inc_ref(v_toConstantVal_4268_);
lean_dec(v_val_4267_);
v_name_4269_ = lean_ctor_get(v_toConstantVal_4266_, 0);
lean_inc(v_name_4269_);
lean_dec_ref(v_toConstantVal_4266_);
v_name_4270_ = lean_ctor_get(v_toConstantVal_4268_, 0);
lean_inc(v_name_4270_);
lean_dec_ref(v_toConstantVal_4268_);
v___x_4271_ = lean_name_eq(v_name_4269_, v_name_4270_);
lean_dec(v_name_4270_);
lean_dec(v_name_4269_);
if (v___x_4271_ == 0)
{
v___y_4184_ = v___y_4250_;
v___y_4185_ = v___y_4251_;
v___y_4186_ = v___y_4249_;
v___y_4187_ = v___y_4248_;
v___y_4188_ = v_fst_4259_;
v___y_4189_ = v_fst_4257_;
v___y_4190_ = v_isEq_4247_;
goto v___jp_4183_;
}
else
{
if (v___x_3974_ == 0)
{
lean_dec(v_fst_4259_);
lean_dec(v_fst_4257_);
v___y_4175_ = v_isEq_4247_;
v_isHEq_4176_ = v___x_3878_;
v___y_4177_ = v___y_4248_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
goto v___jp_4174_;
}
else
{
v___y_4184_ = v___y_4250_;
v___y_4185_ = v___y_4251_;
v___y_4186_ = v___y_4249_;
v___y_4187_ = v___y_4248_;
v___y_4188_ = v_fst_4259_;
v___y_4189_ = v_fst_4257_;
v___y_4190_ = v_isEq_4247_;
goto v___jp_4183_;
}
}
}
else
{
lean_dec(v_a_4265_);
lean_dec(v_val_4263_);
lean_dec(v_fst_4259_);
lean_dec(v_fst_4257_);
v___y_4175_ = v_isEq_4247_;
v_isHEq_4176_ = v___x_3878_;
v___y_4177_ = v___y_4248_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
goto v___jp_4174_;
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec(v_val_4263_);
lean_dec(v_fst_4259_);
lean_dec(v_fst_4257_);
lean_dec_ref(v___x_4019_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4272_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4264_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4264_);
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
lean_dec(v_a_4262_);
lean_dec(v_snd_4260_);
lean_dec(v_fst_4259_);
lean_dec(v_fst_4257_);
v___y_4175_ = v_isEq_4247_;
v_isHEq_4176_ = v___x_3878_;
v___y_4177_ = v___y_4248_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
goto v___jp_4174_;
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec(v_snd_4260_);
lean_dec(v_fst_4259_);
lean_dec(v_fst_4257_);
lean_dec_ref(v___x_4019_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4280_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4261_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4261_);
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
else
{
lean_dec(v_a_4253_);
v___y_4175_ = v_isEq_4247_;
v_isHEq_4176_ = v___x_3974_;
v___y_4177_ = v___y_4248_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
v___y_4180_ = v___y_4251_;
goto v___jp_4174_;
}
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v___x_4019_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4288_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4252_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4252_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
v___jp_4296_:
{
lean_object* v___x_4301_; 
lean_inc_ref(v___x_4019_);
v___x_4301_ = l_Lean_Meta_matchEq_x3f(v___x_4019_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4301_, 1);
if (lean_obj_tag(v_a_4302_) == 1)
{
lean_object* v_val_4303_; lean_object* v_snd_4304_; lean_object* v_fst_4305_; lean_object* v_snd_4306_; lean_object* v___x_4307_; 
v_val_4303_ = lean_ctor_get(v_a_4302_, 0);
lean_inc(v_val_4303_);
lean_dec_ref_known(v_a_4302_, 1);
v_snd_4304_ = lean_ctor_get(v_val_4303_, 1);
lean_inc(v_snd_4304_);
lean_dec(v_val_4303_);
v_fst_4305_ = lean_ctor_get(v_snd_4304_, 0);
lean_inc(v_fst_4305_);
v_snd_4306_ = lean_ctor_get(v_snd_4304_, 1);
lean_inc(v_snd_4306_);
lean_dec(v_snd_4304_);
v___x_4307_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4305_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4307_, 1);
if (lean_obj_tag(v_a_4308_) == 1)
{
lean_object* v_val_4309_; lean_object* v___x_4310_; 
v_val_4309_ = lean_ctor_get(v_a_4308_, 0);
lean_inc(v_val_4309_);
lean_dec_ref_known(v_a_4308_, 1);
v___x_4310_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4306_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4310_, 1);
if (lean_obj_tag(v_a_4311_) == 1)
{
lean_object* v_toConstantVal_4312_; lean_object* v_val_4313_; lean_object* v_toConstantVal_4314_; lean_object* v_name_4315_; lean_object* v_name_4316_; uint8_t v___x_4317_; 
v_toConstantVal_4312_ = lean_ctor_get(v_val_4309_, 0);
lean_inc_ref(v_toConstantVal_4312_);
lean_dec(v_val_4309_);
v_val_4313_ = lean_ctor_get(v_a_4311_, 0);
lean_inc(v_val_4313_);
lean_dec_ref_known(v_a_4311_, 1);
v_toConstantVal_4314_ = lean_ctor_get(v_val_4313_, 0);
lean_inc_ref(v_toConstantVal_4314_);
lean_dec(v_val_4313_);
v_name_4315_ = lean_ctor_get(v_toConstantVal_4312_, 0);
lean_inc(v_name_4315_);
lean_dec_ref(v_toConstantVal_4312_);
v_name_4316_ = lean_ctor_get(v_toConstantVal_4314_, 0);
lean_inc(v_name_4316_);
lean_dec_ref(v_toConstantVal_4314_);
v___x_4317_ = lean_name_eq(v_name_4315_, v_name_4316_);
lean_dec(v_name_4316_);
lean_dec(v_name_4315_);
if (v___x_4317_ == 0)
{
lean_dec_ref(v___x_4019_);
lean_dec_ref(v_config_3867_);
v___y_3905_ = v___y_4299_;
v___y_3906_ = v___y_4297_;
v___y_3907_ = v___y_4298_;
v___y_3908_ = v___y_4300_;
goto v___jp_3904_;
}
else
{
if (v___x_3974_ == 0)
{
lean_del_object(v___x_3901_);
v_isEq_4247_ = v___x_3878_;
v___y_4248_ = v___y_4297_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
goto v___jp_4246_;
}
else
{
lean_dec_ref(v___x_4019_);
lean_dec_ref(v_config_3867_);
v___y_3905_ = v___y_4299_;
v___y_3906_ = v___y_4297_;
v___y_3907_ = v___y_4298_;
v___y_3908_ = v___y_4300_;
goto v___jp_3904_;
}
}
}
else
{
lean_dec(v_a_4311_);
lean_dec(v_val_4309_);
lean_del_object(v___x_3901_);
v_isEq_4247_ = v___x_3878_;
v___y_4248_ = v___y_4297_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
goto v___jp_4246_;
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec(v_val_4309_);
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4318_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4310_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4310_);
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
lean_dec(v_a_4308_);
lean_dec(v_snd_4306_);
lean_del_object(v___x_3901_);
v_isEq_4247_ = v___x_3878_;
v___y_4248_ = v___y_4297_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
goto v___jp_4246_;
}
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec(v_snd_4306_);
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4326_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4307_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4307_);
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
lean_dec(v_a_4302_);
lean_del_object(v___x_3901_);
v_isEq_4247_ = v___x_3974_;
v___y_4248_ = v___y_4297_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
v___y_4251_ = v___y_4300_;
goto v___jp_4246_;
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4334_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4301_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4301_);
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
v___jp_4342_:
{
lean_object* v___x_4347_; 
lean_inc_ref(v___x_4019_);
v___x_4347_ = l_Lean_refutableHasNotBit_x3f(v___x_4019_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4347_, 1);
if (lean_obj_tag(v_a_4348_) == 1)
{
lean_object* v_val_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4389_; 
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec_ref(v_config_3867_);
v_val_4349_ = lean_ctor_get(v_a_4348_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v_a_4348_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4351_ = v_a_4348_;
v_isShared_4352_ = v_isSharedCheck_4389_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_val_4349_);
lean_dec(v_a_4348_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4389_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4353_; 
lean_inc(v_mvarId_3868_);
v___x_4353_ = l_Lean_MVarId_getType(v_mvarId_3868_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4355_ = l_Lean_LocalDecl_toExpr(v_val_3899_);
v___x_4356_ = l_Lean_Meta_mkAbsurd(v_a_4354_, v_val_4349_, v___x_4355_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4358_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
v___x_4358_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3868_, v_a_4357_, v___y_4344_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v___x_4359_; lean_object* v___x_4361_; 
lean_dec_ref_known(v___x_4358_, 1);
v___x_4359_ = lean_box(v___x_3878_);
if (v_isShared_4352_ == 0)
{
lean_ctor_set(v___x_4351_, 0, v___x_4359_);
v___x_4361_ = v___x_4351_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4359_);
v___x_4361_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
lean_ctor_set(v___x_4362_, 1, v___x_3903_);
v___x_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
v_a_3885_ = v___x_4363_;
goto v___jp_3884_;
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_del_object(v___x_4351_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
v_a_4365_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4358_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4358_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_del_object(v___x_4351_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4373_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4356_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4356_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_del_object(v___x_4351_);
lean_dec(v_val_4349_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4381_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4353_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4353_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
else
{
lean_object* v___x_4390_; 
lean_dec(v_a_4348_);
lean_inc_ref(v___x_4019_);
v___x_4390_ = l_Lean_Meta_matchNe_x3f(v___x_4019_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v___x_4390_, 1);
if (lean_obj_tag(v_a_4391_) == 1)
{
lean_object* v_val_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4462_; 
v_val_4392_ = lean_ctor_get(v_a_4391_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_a_4391_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4394_ = v_a_4391_;
v_isShared_4395_ = v_isSharedCheck_4462_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_val_4392_);
lean_dec(v_a_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4462_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v_snd_4396_; lean_object* v_fst_4397_; lean_object* v_snd_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4461_; 
v_snd_4396_ = lean_ctor_get(v_val_4392_, 1);
lean_inc(v_snd_4396_);
lean_dec(v_val_4392_);
v_fst_4397_ = lean_ctor_get(v_snd_4396_, 0);
v_snd_4398_ = lean_ctor_get(v_snd_4396_, 1);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_snd_4396_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4400_ = v_snd_4396_;
v_isShared_4401_ = v_isSharedCheck_4461_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_snd_4398_);
lean_inc(v_fst_4397_);
lean_dec(v_snd_4396_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4461_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4402_; 
lean_inc(v_fst_4397_);
v___x_4402_ = l_Lean_Meta_isExprDefEq(v_fst_4397_, v_snd_4398_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; uint8_t v___x_4404_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4402_, 1);
v___x_4404_ = lean_unbox(v_a_4403_);
lean_dec(v_a_4403_);
if (v___x_4404_ == 0)
{
lean_del_object(v___x_4400_);
lean_dec(v_fst_4397_);
lean_del_object(v___x_4394_);
v___y_4297_ = v___y_4343_;
v___y_4298_ = v___y_4344_;
v___y_4299_ = v___y_4345_;
v___y_4300_ = v___y_4346_;
goto v___jp_4296_;
}
else
{
lean_object* v___x_4405_; 
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec_ref(v_config_3867_);
lean_inc(v_mvarId_3868_);
v___x_4405_ = l_Lean_MVarId_getType(v_mvarId_3868_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4407_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v___x_4407_ = l_Lean_Meta_mkEqRefl(v_fst_4397_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref_known(v___x_4407_, 1);
v___x_4409_ = l_Lean_LocalDecl_toExpr(v_val_3899_);
v___x_4410_ = l_Lean_Meta_mkAbsurd(v_a_4406_, v_a_4408_, v___x_4409_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v___x_4412_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3868_, v_a_4411_, v___y_4344_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v___x_4413_; lean_object* v___x_4415_; 
lean_dec_ref_known(v___x_4412_, 1);
v___x_4413_ = lean_box(v___x_3878_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v___x_4413_);
v___x_4415_ = v___x_4394_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4417_; 
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 1, v___x_3903_);
lean_ctor_set(v___x_4400_, 0, v___x_4415_);
v___x_4417_ = v___x_4400_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4415_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v___x_3903_);
v___x_4417_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
lean_object* v___x_4418_; 
v___x_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4417_);
v_a_3885_ = v___x_4418_;
goto v___jp_3884_;
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_del_object(v___x_4400_);
lean_del_object(v___x_4394_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
v_a_4421_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4412_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4412_);
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
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_del_object(v___x_4400_);
lean_del_object(v___x_4394_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4429_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4410_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4410_);
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
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec(v_a_4406_);
lean_del_object(v___x_4400_);
lean_del_object(v___x_4394_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4437_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4407_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4407_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_del_object(v___x_4400_);
lean_dec(v_fst_4397_);
lean_del_object(v___x_4394_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_4445_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4405_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4405_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_del_object(v___x_4400_);
lean_dec(v_fst_4397_);
lean_del_object(v___x_4394_);
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4453_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4402_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4402_);
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
}
}
else
{
lean_dec(v_a_4391_);
v___y_4297_ = v___y_4343_;
v___y_4298_ = v___y_4344_;
v___y_4299_ = v___y_4345_;
v___y_4300_ = v___y_4346_;
goto v___jp_4296_;
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4463_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4390_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4390_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
lean_dec_ref(v___x_4019_);
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4471_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4347_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4347_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
}
else
{
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
v_a_3893_ = v___x_3945_;
goto v___jp_3892_;
}
v___jp_3904_:
{
lean_object* v___x_3909_; 
lean_inc(v_mvarId_3868_);
v___x_3909_ = l_Lean_MVarId_getType(v_mvarId_3868_, v___y_3906_, v___y_3907_, v___y_3905_, v___y_3908_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = l_Lean_LocalDecl_toExpr(v_val_3899_);
v___x_3912_ = l_Lean_Meta_mkNoConfusion(v_a_3910_, v___x_3911_, v___y_3906_, v___y_3907_, v___y_3905_, v___y_3908_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3868_, v_a_3913_, v___y_3907_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v___x_3915_; lean_object* v___x_3917_; 
lean_dec_ref_known(v___x_3914_, 1);
v___x_3915_ = lean_box(v___x_3878_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3915_);
v___x_3917_ = v___x_3901_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
lean_ctor_set(v___x_3918_, 1, v___x_3903_);
v___x_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
v_a_3885_ = v___x_3919_;
goto v___jp_3884_;
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_del_object(v___x_3901_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
v_a_3921_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3914_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3914_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_del_object(v___x_3901_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_3929_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3912_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3912_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_3937_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3909_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3909_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
v___jp_3946_:
{
lean_object* v_searchFuel_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_searchFuel_3951_ = lean_ctor_get(v_config_3867_, 0);
v___x_3952_ = l_Lean_LocalDecl_fvarId(v_val_3899_);
lean_dec(v_val_3899_);
lean_inc(v_searchFuel_3951_);
lean_inc(v_mvarId_3868_);
v___x_3953_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3868_, v___x_3952_, v_searchFuel_3951_, v___y_3950_, v___y_3949_, v___y_3948_, v___y_3947_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; uint8_t v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = lean_unbox(v_a_3954_);
lean_dec(v_a_3954_);
if (v___x_3955_ == 0)
{
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
v_a_3893_ = v___x_3945_;
goto v___jp_3892_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v___x_3956_ = lean_box(v___x_3878_);
v___x_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
v___x_3958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
lean_ctor_set(v___x_3958_, 1, v___x_3903_);
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
v_a_3885_ = v___x_3959_;
goto v___jp_3884_;
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_3960_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3953_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3953_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
v___jp_3968_:
{
if (v___y_3973_ == 0)
{
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
v_a_3893_ = v___x_3945_;
goto v___jp_3892_;
}
else
{
v___y_3947_ = v___y_3970_;
v___y_3948_ = v___y_3969_;
v___y_3949_ = v___y_3971_;
v___y_3950_ = v___y_3972_;
goto v___jp_3946_;
}
}
v___jp_3975_:
{
if (v___y_3978_ == 0)
{
v___y_3947_ = v___y_3977_;
v___y_3948_ = v___y_3976_;
v___y_3949_ = v___y_3979_;
v___y_3950_ = v___y_3980_;
goto v___jp_3946_;
}
else
{
v___y_3969_ = v___y_3976_;
v___y_3970_ = v___y_3977_;
v___y_3971_ = v___y_3979_;
v___y_3972_ = v___y_3980_;
v___y_3973_ = v___x_3974_;
goto v___jp_3968_;
}
}
v___jp_3981_:
{
if (v___y_3987_ == 0)
{
v___y_3969_ = v___y_3984_;
v___y_3970_ = v___y_3983_;
v___y_3971_ = v___y_3985_;
v___y_3972_ = v___y_3986_;
v___y_3973_ = v___x_3974_;
goto v___jp_3968_;
}
else
{
v___y_3976_ = v___y_3984_;
v___y_3977_ = v___y_3983_;
v___y_3978_ = v___y_3982_;
v___y_3979_ = v___y_3985_;
v___y_3980_ = v___y_3986_;
goto v___jp_3975_;
}
}
v___jp_3988_:
{
uint8_t v_emptyType_3995_; 
v_emptyType_3995_ = lean_ctor_get_uint8(v_config_3867_, sizeof(void*)*1 + 1);
if (v_emptyType_3995_ == 0)
{
v___y_3982_ = v___y_3989_;
v___y_3983_ = v___y_3994_;
v___y_3984_ = v___y_3993_;
v___y_3985_ = v___y_3992_;
v___y_3986_ = v___y_3991_;
v___y_3987_ = v___x_3974_;
goto v___jp_3981_;
}
else
{
if (v___y_3990_ == 0)
{
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___y_3989_;
v___y_3979_ = v___y_3992_;
v___y_3980_ = v___y_3991_;
goto v___jp_3975_;
}
else
{
v___y_3982_ = v___y_3989_;
v___y_3983_ = v___y_3994_;
v___y_3984_ = v___y_3993_;
v___y_3985_ = v___y_3992_;
v___y_3986_ = v___y_3991_;
v___y_3987_ = v___x_3974_;
goto v___jp_3981_;
}
}
}
v___jp_3996_:
{
if (v___y_4003_ == 0)
{
v___y_3989_ = v___y_4001_;
v___y_3990_ = v___y_4002_;
v___y_3991_ = v___y_4000_;
v___y_3992_ = v___y_3999_;
v___y_3993_ = v___y_3998_;
v___y_3994_ = v___y_3997_;
goto v___jp_3988_;
}
else
{
lean_object* v___x_4004_; 
lean_inc(v_val_3899_);
lean_inc(v_mvarId_3868_);
v___x_4004_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3868_, v_val_3899_, v___y_4000_, v___y_3999_, v___y_3998_, v___y_3997_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; uint8_t v___x_4006_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v___x_4006_ = lean_unbox(v_a_4005_);
lean_dec(v_a_4005_);
if (v___x_4006_ == 0)
{
v___y_3989_ = v___y_4001_;
v___y_3990_ = v___y_4002_;
v___y_3991_ = v___y_4000_;
v___y_3992_ = v___y_3999_;
v___y_3993_ = v___y_3998_;
v___y_3994_ = v___y_3997_;
goto v___jp_3988_;
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
lean_dec(v_val_3899_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v___x_4007_ = lean_box(v___x_3878_);
v___x_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
v___x_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
lean_ctor_set(v___x_4009_, 1, v___x_3903_);
v___x_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
v_a_3885_ = v___x_4010_;
goto v___jp_3884_;
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v_val_3899_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
lean_dec_ref(v_config_3867_);
v_a_4011_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_4004_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4004_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
}
}
v___jp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_a_3885_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v___x_3886_);
v___x_3888_ = v___x_3882_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v_snd_3880_);
v___x_3888_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
return v___x_3889_;
}
}
v___jp_3892_:
{
lean_object* v___x_3894_; size_t v___x_3895_; size_t v___x_3896_; lean_object* v___x_3897_; 
v___x_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3891_);
lean_ctor_set(v___x_3894_, 1, v_a_3893_);
v___x_3895_ = ((size_t)1ULL);
v___x_3896_ = lean_usize_add(v_i_3871_, v___x_3895_);
v___x_3897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3867_, v_mvarId_3868_, v_as_3869_, v_sz_3870_, v___x_3896_, v___x_3894_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
return v___x_3897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4552_, lean_object* v_mvarId_4553_, lean_object* v_as_4554_, lean_object* v_sz_4555_, lean_object* v_i_4556_, lean_object* v_b_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
size_t v_sz_boxed_4563_; size_t v_i_boxed_4564_; lean_object* v_res_4565_; 
v_sz_boxed_4563_ = lean_unbox_usize(v_sz_4555_);
lean_dec(v_sz_4555_);
v_i_boxed_4564_ = lean_unbox_usize(v_i_4556_);
lean_dec(v_i_4556_);
v_res_4565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4552_, v_mvarId_4553_, v_as_4554_, v_sz_boxed_4563_, v_i_boxed_4564_, v_b_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec_ref(v_as_4554_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4566_, lean_object* v_config_4567_, lean_object* v_mvarId_4568_, lean_object* v_n_4569_, lean_object* v_b_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
if (lean_obj_tag(v_n_4569_) == 0)
{
lean_object* v_cs_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; size_t v_sz_4579_; size_t v___x_4580_; lean_object* v___x_4581_; 
v_cs_4576_ = lean_ctor_get(v_n_4569_, 0);
v___x_4577_ = lean_box(0);
v___x_4578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
lean_ctor_set(v___x_4578_, 1, v_b_4570_);
v_sz_4579_ = lean_array_size(v_cs_4576_);
v___x_4580_ = ((size_t)0ULL);
v___x_4581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4566_, v_config_4567_, v_mvarId_4568_, v_cs_4576_, v_sz_4579_, v___x_4580_, v___x_4578_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4596_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4584_ = v___x_4581_;
v_isShared_4585_ = v_isSharedCheck_4596_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4596_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v_fst_4586_; 
v_fst_4586_ = lean_ctor_get(v_a_4582_, 0);
if (lean_obj_tag(v_fst_4586_) == 0)
{
lean_object* v_snd_4587_; lean_object* v___x_4588_; lean_object* v___x_4590_; 
v_snd_4587_ = lean_ctor_get(v_a_4582_, 1);
lean_inc(v_snd_4587_);
lean_dec(v_a_4582_);
v___x_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4588_, 0, v_snd_4587_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v___x_4588_);
v___x_4590_ = v___x_4584_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4588_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
else
{
lean_object* v_val_4592_; lean_object* v___x_4594_; 
lean_inc_ref(v_fst_4586_);
lean_dec(v_a_4582_);
v_val_4592_ = lean_ctor_get(v_fst_4586_, 0);
lean_inc(v_val_4592_);
lean_dec_ref_known(v_fst_4586_, 1);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v_val_4592_);
v___x_4594_ = v___x_4584_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_val_4592_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
v_a_4597_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4581_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4581_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
else
{
lean_object* v_vs_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; size_t v_sz_4608_; size_t v___x_4609_; lean_object* v___x_4610_; 
v_vs_4605_ = lean_ctor_get(v_n_4569_, 0);
v___x_4606_ = lean_box(0);
v___x_4607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
lean_ctor_set(v___x_4607_, 1, v_b_4570_);
v_sz_4608_ = lean_array_size(v_vs_4605_);
v___x_4609_ = ((size_t)0ULL);
v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4567_, v_mvarId_4568_, v_vs_4605_, v_sz_4608_, v___x_4609_, v___x_4607_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4625_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4625_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4625_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v_fst_4615_; 
v_fst_4615_ = lean_ctor_get(v_a_4611_, 0);
if (lean_obj_tag(v_fst_4615_) == 0)
{
lean_object* v_snd_4616_; lean_object* v___x_4617_; lean_object* v___x_4619_; 
v_snd_4616_ = lean_ctor_get(v_a_4611_, 1);
lean_inc(v_snd_4616_);
lean_dec(v_a_4611_);
v___x_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4617_, 0, v_snd_4616_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4617_);
v___x_4619_ = v___x_4613_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
else
{
lean_object* v_val_4621_; lean_object* v___x_4623_; 
lean_inc_ref(v_fst_4615_);
lean_dec(v_a_4611_);
v_val_4621_ = lean_ctor_get(v_fst_4615_, 0);
lean_inc(v_val_4621_);
lean_dec_ref_known(v_fst_4615_, 1);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v_val_4621_);
v___x_4623_ = v___x_4613_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_val_4621_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4633_; 
v_a_4626_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4628_ = v___x_4610_;
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4610_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4634_, lean_object* v_config_4635_, lean_object* v_mvarId_4636_, lean_object* v_as_4637_, size_t v_sz_4638_, size_t v_i_4639_, lean_object* v_b_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
uint8_t v___x_4646_; 
v___x_4646_ = lean_usize_dec_lt(v_i_4639_, v_sz_4638_);
if (v___x_4646_ == 0)
{
lean_object* v___x_4647_; 
lean_dec(v_mvarId_4636_);
lean_dec_ref(v_config_4635_);
v___x_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4647_, 0, v_b_4640_);
return v___x_4647_;
}
else
{
lean_object* v_snd_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4682_; 
v_snd_4648_ = lean_ctor_get(v_b_4640_, 1);
v_isSharedCheck_4682_ = !lean_is_exclusive(v_b_4640_);
if (v_isSharedCheck_4682_ == 0)
{
lean_object* v_unused_4683_; 
v_unused_4683_ = lean_ctor_get(v_b_4640_, 0);
lean_dec(v_unused_4683_);
v___x_4650_ = v_b_4640_;
v_isShared_4651_ = v_isSharedCheck_4682_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_snd_4648_);
lean_dec(v_b_4640_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4682_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v_a_4652_; lean_object* v___x_4653_; 
v_a_4652_ = lean_array_uget_borrowed(v_as_4637_, v_i_4639_);
lean_inc(v_snd_4648_);
lean_inc(v_mvarId_4636_);
lean_inc_ref(v_config_4635_);
v___x_4653_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4634_, v_config_4635_, v_mvarId_4636_, v_a_4652_, v_snd_4648_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4673_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4656_ = v___x_4653_;
v_isShared_4657_ = v_isSharedCheck_4673_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4653_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4673_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
if (lean_obj_tag(v_a_4654_) == 0)
{
lean_object* v___x_4658_; lean_object* v___x_4660_; 
lean_dec(v_mvarId_4636_);
lean_dec_ref(v_config_4635_);
v___x_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4658_, 0, v_a_4654_);
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 0, v___x_4658_);
v___x_4660_ = v___x_4650_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4658_);
lean_ctor_set(v_reuseFailAlloc_4664_, 1, v_snd_4648_);
v___x_4660_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4662_; 
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 0, v___x_4660_);
v___x_4662_ = v___x_4656_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4660_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4666_; lean_object* v___x_4668_; 
lean_del_object(v___x_4656_);
lean_dec(v_snd_4648_);
v_a_4665_ = lean_ctor_get(v_a_4654_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v_a_4654_, 1);
v___x_4666_ = lean_box(0);
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 1, v_a_4665_);
lean_ctor_set(v___x_4650_, 0, v___x_4666_);
v___x_4668_ = v___x_4650_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4666_);
lean_ctor_set(v_reuseFailAlloc_4672_, 1, v_a_4665_);
v___x_4668_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
size_t v___x_4669_; size_t v___x_4670_; 
v___x_4669_ = ((size_t)1ULL);
v___x_4670_ = lean_usize_add(v_i_4639_, v___x_4669_);
v_i_4639_ = v___x_4670_;
v_b_4640_ = v___x_4668_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
lean_del_object(v___x_4650_);
lean_dec(v_snd_4648_);
lean_dec(v_mvarId_4636_);
lean_dec_ref(v_config_4635_);
v_a_4674_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4676_ = v___x_4653_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4653_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4684_, lean_object* v_config_4685_, lean_object* v_mvarId_4686_, lean_object* v_as_4687_, lean_object* v_sz_4688_, lean_object* v_i_4689_, lean_object* v_b_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
size_t v_sz_boxed_4696_; size_t v_i_boxed_4697_; lean_object* v_res_4698_; 
v_sz_boxed_4696_ = lean_unbox_usize(v_sz_4688_);
lean_dec(v_sz_4688_);
v_i_boxed_4697_ = lean_unbox_usize(v_i_4689_);
lean_dec(v_i_4689_);
v_res_4698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4684_, v_config_4685_, v_mvarId_4686_, v_as_4687_, v_sz_boxed_4696_, v_i_boxed_4697_, v_b_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec_ref(v_as_4687_);
lean_dec_ref(v_init_4684_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4699_, lean_object* v_config_4700_, lean_object* v_mvarId_4701_, lean_object* v_n_4702_, lean_object* v_b_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4699_, v_config_4700_, v_mvarId_4701_, v_n_4702_, v_b_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec_ref(v_n_4702_);
lean_dec_ref(v_init_4699_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4710_, lean_object* v_mvarId_4711_, lean_object* v_t_4712_, lean_object* v_init_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v_root_4719_; lean_object* v_tail_4720_; lean_object* v___x_4721_; 
v_root_4719_ = lean_ctor_get(v_t_4712_, 0);
v_tail_4720_ = lean_ctor_get(v_t_4712_, 1);
lean_inc(v_mvarId_4711_);
lean_inc_ref(v_config_4710_);
lean_inc_ref(v_init_4713_);
v___x_4721_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4713_, v_config_4710_, v_mvarId_4711_, v_root_4719_, v_init_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
lean_dec_ref(v_init_4713_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4758_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4758_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4758_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
if (lean_obj_tag(v_a_4722_) == 0)
{
lean_object* v_a_4726_; lean_object* v___x_4728_; 
lean_dec(v_mvarId_4711_);
lean_dec_ref(v_config_4710_);
v_a_4726_ = lean_ctor_get(v_a_4722_, 0);
lean_inc(v_a_4726_);
lean_dec_ref_known(v_a_4722_, 1);
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 0, v_a_4726_);
v___x_4728_ = v___x_4724_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_a_4726_);
v___x_4728_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
return v___x_4728_;
}
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; size_t v_sz_4733_; size_t v___x_4734_; lean_object* v___x_4735_; 
lean_del_object(v___x_4724_);
v_a_4730_ = lean_ctor_get(v_a_4722_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v_a_4722_, 1);
v___x_4731_ = lean_box(0);
v___x_4732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4731_);
lean_ctor_set(v___x_4732_, 1, v_a_4730_);
v_sz_4733_ = lean_array_size(v_tail_4720_);
v___x_4734_ = ((size_t)0ULL);
v___x_4735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4710_, v_mvarId_4711_, v_tail_4720_, v_sz_4733_, v___x_4734_, v___x_4732_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4749_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4738_ = v___x_4735_;
v_isShared_4739_ = v_isSharedCheck_4749_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4735_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4749_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v_fst_4740_; 
v_fst_4740_ = lean_ctor_get(v_a_4736_, 0);
if (lean_obj_tag(v_fst_4740_) == 0)
{
lean_object* v_snd_4741_; lean_object* v___x_4743_; 
v_snd_4741_ = lean_ctor_get(v_a_4736_, 1);
lean_inc(v_snd_4741_);
lean_dec(v_a_4736_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v_snd_4741_);
v___x_4743_ = v___x_4738_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_snd_4741_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
else
{
lean_object* v_val_4745_; lean_object* v___x_4747_; 
lean_inc_ref(v_fst_4740_);
lean_dec(v_a_4736_);
v_val_4745_ = lean_ctor_get(v_fst_4740_, 0);
lean_inc(v_val_4745_);
lean_dec_ref_known(v_fst_4740_, 1);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v_val_4745_);
v___x_4747_ = v___x_4738_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_val_4745_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
v_a_4750_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4735_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4735_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
}
}
else
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
lean_dec(v_mvarId_4711_);
lean_dec_ref(v_config_4710_);
v_a_4759_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4721_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4721_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4767_, lean_object* v_mvarId_4768_, lean_object* v_t_4769_, lean_object* v_init_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4767_, v_mvarId_4768_, v_t_4769_, v_init_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec_ref(v_t_4769_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4777_, lean_object* v___x_4778_, lean_object* v_config_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
lean_object* v___x_4785_; 
lean_inc(v_mvarId_4777_);
v___x_4785_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4777_, v___x_4778_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v___x_4786_; 
lean_dec_ref_known(v___x_4785_, 1);
lean_inc(v_mvarId_4777_);
v___x_4786_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4777_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4820_; 
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4789_ = v___x_4786_;
v_isShared_4790_ = v_isSharedCheck_4820_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4786_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4820_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
uint8_t v___x_4791_; 
v___x_4791_ = lean_unbox(v_a_4787_);
if (v___x_4791_ == 0)
{
lean_object* v_lctx_4792_; lean_object* v_decls_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
lean_del_object(v___x_4789_);
v_lctx_4792_ = lean_ctor_get(v___y_4780_, 2);
v_decls_4793_ = lean_ctor_get(v_lctx_4792_, 1);
v___x_4794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4795_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4779_, v_mvarId_4777_, v_decls_4793_, v___x_4794_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4808_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4798_ = v___x_4795_;
v_isShared_4799_ = v_isSharedCheck_4808_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v___x_4795_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4808_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v_fst_4800_; 
v_fst_4800_ = lean_ctor_get(v_a_4796_, 0);
lean_inc(v_fst_4800_);
lean_dec(v_a_4796_);
if (lean_obj_tag(v_fst_4800_) == 0)
{
lean_object* v___x_4802_; 
if (v_isShared_4799_ == 0)
{
lean_ctor_set(v___x_4798_, 0, v_a_4787_);
v___x_4802_ = v___x_4798_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4787_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
else
{
lean_object* v_val_4804_; lean_object* v___x_4806_; 
lean_dec(v_a_4787_);
v_val_4804_ = lean_ctor_get(v_fst_4800_, 0);
lean_inc(v_val_4804_);
lean_dec_ref_known(v_fst_4800_, 1);
if (v_isShared_4799_ == 0)
{
lean_ctor_set(v___x_4798_, 0, v_val_4804_);
v___x_4806_ = v___x_4798_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_val_4804_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
else
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
lean_dec(v_a_4787_);
v_a_4809_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4795_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4795_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4814_; 
if (v_isShared_4812_ == 0)
{
v___x_4814_ = v___x_4811_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_a_4809_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
}
else
{
lean_object* v___x_4818_; 
lean_dec_ref(v_config_4779_);
lean_dec(v_mvarId_4777_);
if (v_isShared_4790_ == 0)
{
v___x_4818_ = v___x_4789_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4787_);
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
lean_dec_ref(v_config_4779_);
lean_dec(v_mvarId_4777_);
return v___x_4786_;
}
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_dec_ref(v_config_4779_);
lean_dec(v_mvarId_4777_);
v_a_4821_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4785_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4785_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4829_, lean_object* v___x_4830_, lean_object* v_config_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4829_, v___x_4830_, v_config_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4840_, lean_object* v_config_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v___x_4847_; lean_object* v___f_4848_; lean_object* v___x_4849_; 
v___x_4847_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4840_);
v___f_4848_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4848_, 0, v_mvarId_4840_);
lean_closure_set(v___f_4848_, 1, v___x_4847_);
lean_closure_set(v___f_4848_, 2, v_config_4841_);
v___x_4849_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4840_, v___f_4848_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4850_, lean_object* v_config_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l_Lean_MVarId_contradictionCore(v_mvarId_4850_, v_config_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4858_, lean_object* v_config_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v___x_4865_; 
lean_inc(v_mvarId_4858_);
v___x_4865_ = l_Lean_MVarId_contradictionCore(v_mvarId_4858_, v_config_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4878_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4868_ = v___x_4865_;
v_isShared_4869_ = v_isSharedCheck_4878_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4865_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4878_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
uint8_t v___x_4870_; 
v___x_4870_ = lean_unbox(v_a_4866_);
lean_dec(v_a_4866_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
lean_del_object(v___x_4868_);
v___x_4871_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4872_ = lean_box(0);
v___x_4873_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4871_, v_mvarId_4858_, v___x_4872_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_);
return v___x_4873_;
}
else
{
lean_object* v___x_4874_; lean_object* v___x_4876_; 
lean_dec(v_mvarId_4858_);
v___x_4874_ = lean_box(0);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 0, v___x_4874_);
v___x_4876_ = v___x_4868_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4874_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
lean_dec(v_mvarId_4858_);
v_a_4879_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4865_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4865_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4887_, lean_object* v_config_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Lean_MVarId_contradiction(v_mvarId_4887_, v_config_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_);
lean_dec(v_a_4892_);
lean_dec_ref(v_a_4891_);
lean_dec(v_a_4890_);
lean_dec_ref(v_a_4889_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4957_; uint8_t v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4957_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4958_ = 0;
v___x_4959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4960_ = l_Lean_registerTraceClass(v___x_4957_, v___x_4958_, v___x_4959_);
return v___x_4960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4962_;
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
