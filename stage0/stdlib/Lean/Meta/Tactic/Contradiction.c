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
lean_dec_ref(v___y_503_);
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
lean_ctor_set(v___x_507_, 0, v___y_502_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___y_502_);
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
lean_dec_ref(v___y_502_);
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
lean_dec_ref(v___y_502_);
lean_dec(v_a_500_);
return v___y_503_;
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
v___y_502_ = v_a_524_;
v___y_503_ = v___y_523_;
v___y_504_ = v___x_526_;
goto v___jp_501_;
}
else
{
v___y_502_ = v_a_524_;
v___y_503_ = v___y_523_;
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
lean_object* v___x_570_; lean_object* v_env_571_; lean_object* v___x_572_; lean_object* v_mctx_573_; lean_object* v_lctx_574_; lean_object* v_options_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_570_ = lean_st_ref_get(v___y_568_);
v_env_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_env_571_);
lean_dec(v___x_570_);
v___x_572_ = lean_st_ref_get(v___y_566_);
v_mctx_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_mctx_573_);
lean_dec(v___x_572_);
v_lctx_574_ = lean_ctor_get(v___y_565_, 2);
v_options_575_ = lean_ctor_get(v___y_567_, 1);
lean_inc_ref(v_options_575_);
lean_inc_ref(v_lctx_574_);
v___x_576_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_576_, 0, v_env_571_);
lean_ctor_set(v___x_576_, 1, v_mctx_573_);
lean_ctor_set(v___x_576_, 2, v_lctx_574_);
lean_ctor_set(v___x_576_, 3, v_options_575_);
v___x_577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_msgData_564_);
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
lean_object* v_ref_598_; lean_object* v___x_599_; lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_644_; 
v_ref_598_ = lean_ctor_get(v___y_595_, 4);
v___x_599_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_644_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_644_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_644_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v_traceState_605_; lean_object* v_env_606_; lean_object* v_nextMacroScope_607_; lean_object* v_ngen_608_; lean_object* v_auxDeclNGen_609_; lean_object* v_cache_610_; lean_object* v_messages_611_; lean_object* v_infoState_612_; lean_object* v_snapshotTasks_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_643_; 
v___x_604_ = lean_st_ref_take(v___y_596_);
v_traceState_605_ = lean_ctor_get(v___x_604_, 4);
v_env_606_ = lean_ctor_get(v___x_604_, 0);
v_nextMacroScope_607_ = lean_ctor_get(v___x_604_, 1);
v_ngen_608_ = lean_ctor_get(v___x_604_, 2);
v_auxDeclNGen_609_ = lean_ctor_get(v___x_604_, 3);
v_cache_610_ = lean_ctor_get(v___x_604_, 5);
v_messages_611_ = lean_ctor_get(v___x_604_, 6);
v_infoState_612_ = lean_ctor_get(v___x_604_, 7);
v_snapshotTasks_613_ = lean_ctor_get(v___x_604_, 8);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_643_ == 0)
{
v___x_615_ = v___x_604_;
v_isShared_616_ = v_isSharedCheck_643_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_snapshotTasks_613_);
lean_inc(v_infoState_612_);
lean_inc(v_messages_611_);
lean_inc(v_cache_610_);
lean_inc(v_traceState_605_);
lean_inc(v_auxDeclNGen_609_);
lean_inc(v_ngen_608_);
lean_inc(v_nextMacroScope_607_);
lean_inc(v_env_606_);
lean_dec(v___x_604_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_643_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint64_t v_tid_617_; lean_object* v_traces_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_642_; 
v_tid_617_ = lean_ctor_get_uint64(v_traceState_605_, sizeof(void*)*1);
v_traces_618_ = lean_ctor_get(v_traceState_605_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_traceState_605_);
if (v_isSharedCheck_642_ == 0)
{
v___x_620_ = v_traceState_605_;
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_traces_618_);
lean_dec(v_traceState_605_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; double v___x_623_; uint8_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_622_ = lean_box(0);
v___x_623_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_624_ = 0;
v___x_625_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_626_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_626_, 0, v_cls_591_);
lean_ctor_set(v___x_626_, 1, v___x_622_);
lean_ctor_set(v___x_626_, 2, v___x_625_);
lean_ctor_set_float(v___x_626_, sizeof(void*)*3, v___x_623_);
lean_ctor_set_float(v___x_626_, sizeof(void*)*3 + 8, v___x_623_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*3 + 16, v___x_624_);
v___x_627_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_628_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v_a_600_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_inc(v_ref_598_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_ref_598_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = l_Lean_PersistentArray_push___redArg(v_traces_618_, v___x_629_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_630_);
v___x_632_ = v___x_620_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_630_);
lean_ctor_set_uint64(v_reuseFailAlloc_641_, sizeof(void*)*1, v_tid_617_);
v___x_632_ = v_reuseFailAlloc_641_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 4, v___x_632_);
v___x_634_ = v___x_615_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_env_606_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_nextMacroScope_607_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_ngen_608_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v_auxDeclNGen_609_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_640_, 5, v_cache_610_);
lean_ctor_set(v_reuseFailAlloc_640_, 6, v_messages_611_);
lean_ctor_set(v_reuseFailAlloc_640_, 7, v_infoState_612_);
lean_ctor_set(v_reuseFailAlloc_640_, 8, v_snapshotTasks_613_);
v___x_634_ = v_reuseFailAlloc_640_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_635_ = lean_st_ref_put(v___y_596_, v___x_634_);
v___x_636_ = lean_box(0);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_636_);
v___x_638_ = v___x_602_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
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
size_t v_sz_boxed_673_; size_t v___x_15878__boxed_674_; uint8_t v___x_15880__boxed_675_; lean_object* v_res_676_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_663_);
lean_dec(v_sz_663_);
v___x_15878__boxed_674_ = lean_unbox_usize(v___x_664_);
lean_dec(v___x_664_);
v___x_15880__boxed_675_ = lean_unbox(v___x_666_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_660_, v_mvarId_661_, v_fields_662_, v_sz_boxed_673_, v___x_15878__boxed_674_, v___x_665_, v___x_15880__boxed_675_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
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
lean_object* v_a_764_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v_options_797_; uint8_t v_hasTrace_798_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v_options_797_ = lean_ctor_get(v___y_760_, 1);
v_hasTrace_798_ = lean_ctor_get_uint8(v_options_797_, sizeof(void*)*1);
if (v_hasTrace_798_ == 0)
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
lean_object* v_toCold_799_; lean_object* v_inheritedTraceOptions_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_toCold_799_ = lean_ctor_get(v___y_760_, 0);
v_inheritedTraceOptions_800_ = lean_ctor_get(v_toCold_799_, 4);
v___x_801_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_802_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_803_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_800_, v_options_797_, v___x_802_);
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
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_864_; 
v_a_819_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_864_ == 0)
{
v___x_821_ = v___x_763_;
v_isShared_822_ = v_isSharedCheck_864_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_763_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_864_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___y_824_; uint8_t v___x_862_; 
v___x_862_ = l_Lean_Exception_isInterrupt(v_a_819_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
lean_inc(v_a_819_);
v___x_863_ = l_Lean_Exception_isRuntime(v_a_819_);
v___y_824_ = v___x_863_;
goto v___jp_823_;
}
else
{
v___y_824_ = v___x_862_;
goto v___jp_823_;
}
v___jp_823_:
{
if (v___y_824_ == 0)
{
lean_object* v_options_825_; uint8_t v_hasTrace_826_; 
v_options_825_ = lean_ctor_get(v___y_760_, 1);
v_hasTrace_826_ = lean_ctor_get_uint8(v_options_825_, sizeof(void*)*1);
if (v_hasTrace_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec(v_a_819_);
v___x_827_ = lean_box(v___x_753_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v___x_827_);
v___x_829_ = v___x_821_;
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
lean_object* v_toCold_831_; lean_object* v_inheritedTraceOptions_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_toCold_831_ = lean_ctor_get(v___y_760_, 0);
v_inheritedTraceOptions_832_ = lean_ctor_get(v_toCold_831_, 4);
v___x_833_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_834_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_835_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_832_, v_options_825_, v___x_834_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_865_, lean_object* v_fvarId_866_, lean_object* v___x_867_, lean_object* v___x_868_, lean_object* v___x_869_, lean_object* v_val_870_, lean_object* v___x_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v___x_16000__boxed_878_; uint8_t v___x_16003__boxed_879_; lean_object* v_res_880_; 
v___x_16000__boxed_878_ = lean_unbox(v___x_868_);
v___x_16003__boxed_879_ = lean_unbox(v___x_871_);
v_res_880_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_865_, v_fvarId_866_, v___x_867_, v___x_16000__boxed_878_, v___x_869_, v_val_870_, v___x_16003__boxed_879_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
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
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; 
v___x_899_ = lean_st_ref_take(v_a_886_);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_sub(v___x_899_, v___x_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_st_ref_put(v_a_886_, v___x_901_);
v___x_903_ = 1;
v___x_904_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_905_ = lean_box(0);
v___x_906_ = lean_box(v___x_898_);
v___x_907_ = lean_box(v___x_903_);
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
lean_object* v_options_910_; uint8_t v_hasTrace_911_; 
lean_dec(v___x_896_);
lean_dec(v_fvarId_885_);
lean_dec(v_mvarId_884_);
v_options_910_ = lean_ctor_get(v_a_889_, 1);
v_hasTrace_911_ = lean_ctor_get_uint8(v_options_910_, sizeof(void*)*1);
if (v_hasTrace_911_ == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v_toCold_912_; lean_object* v_inheritedTraceOptions_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_toCold_912_ = lean_ctor_get(v_a_889_, 0);
v_inheritedTraceOptions_913_ = lean_ctor_get(v_toCold_912_, 4);
v___x_914_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_915_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_916_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_913_, v_options_910_, v___x_915_);
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
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_967_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_967_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
uint8_t v___x_961_; 
v___x_961_ = lean_unbox(v_a_957_);
if (v___x_961_ == 0)
{
lean_del_object(v___x_959_);
lean_dec(v_a_957_);
v_a_940_ = v___x_948_;
goto v___jp_939_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
lean_dec(v___x_928_);
lean_dec_ref(v___x_927_);
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v_a_957_);
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___x_947_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_963_);
v___x_965_ = v___x_959_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec(v___x_928_);
lean_dec_ref(v___x_927_);
v_a_968_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_956_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_956_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v___x_952_);
lean_dec(v___x_928_);
lean_dec_ref(v___x_927_);
v_a_976_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_953_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_953_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_984_, lean_object* v_mvarId_985_, lean_object* v_fields_986_, size_t v_sz_987_, size_t v___x_988_, lean_object* v___x_989_, uint8_t v___x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_984_, v_mvarId_985_, v_fields_986_, v_sz_987_, v___x_988_, v___x_989_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1011_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_fst_1002_; 
v_fst_1002_ = lean_ctor_get(v_a_998_, 0);
lean_inc(v_fst_1002_);
lean_dec(v_a_998_);
if (lean_obj_tag(v_fst_1002_) == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_box(v___x_990_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1003_);
v___x_1005_ = v___x_1000_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v_val_1007_; lean_object* v___x_1009_; 
v_val_1007_ = lean_ctor_get(v_fst_1002_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v_fst_1002_, 1);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_val_1007_);
v___x_1009_ = v___x_1000_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_val_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_997_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_997_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1020_, lean_object* v_as_1021_, lean_object* v_sz_1022_, lean_object* v_i_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
size_t v_sz_boxed_1031_; size_t v_i_boxed_1032_; lean_object* v_res_1033_; 
v_sz_boxed_1031_ = lean_unbox_usize(v_sz_1022_);
lean_dec(v_sz_1022_);
v_i_boxed_1032_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_res_1033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1020_, v_as_1021_, v_sz_boxed_1031_, v_i_boxed_1032_, v_b_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v_as_1021_);
lean_dec(v_val_1020_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v_as_1036_, lean_object* v_sz_1037_, lean_object* v_i_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
size_t v_sz_boxed_1046_; size_t v_i_boxed_1047_; lean_object* v_res_1048_; 
v_sz_boxed_1046_ = lean_unbox_usize(v_sz_1037_);
lean_dec(v_sz_1037_);
v_i_boxed_1047_ = lean_unbox_usize(v_i_1038_);
lean_dec(v_i_1038_);
v_res_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1034_, v___x_1035_, v_as_1036_, v_sz_boxed_1046_, v_i_boxed_1047_, v_b_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v_as_1036_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1049_, lean_object* v_fvarId_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1049_, v_fvarId_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1058_, lean_object* v_msg_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1058_, v_msg_1059_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1067_, lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1067_, v_msg_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Meta_saveState___redArg(v___y_1078_, v___y_1080_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___y_1085_; lean_object* v___y_1086_; uint8_t v___y_1087_; lean_object* v___y_1106_; lean_object* v_a_1107_; lean_object* v___x_1110_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
v___x_1110_ = lean_apply_5(v_x_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, lean_box(0));
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; uint8_t v___x_1112_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
v___x_1112_ = lean_unbox(v_a_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref_known(v___x_1110_, 1);
v___x_1113_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1083_, v___y_1078_, v___y_1080_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_a_1083_);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; 
v_unused_1121_ = lean_ctor_get(v___x_1113_, 0);
lean_dec(v_unused_1121_);
v___x_1115_ = v___x_1113_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_dec(v___x_1113_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v_a_1111_);
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1111_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_a_1111_);
v_a_1122_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1113_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1113_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
lean_inc(v_a_1122_);
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v___y_1106_ = v___x_1127_;
v_a_1107_ = v_a_1122_;
goto v___jp_1105_;
}
}
}
}
else
{
lean_dec(v_a_1111_);
lean_dec(v_a_1083_);
return v___x_1110_;
}
}
else
{
lean_object* v_a_1130_; 
v_a_1130_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1130_);
v___y_1106_ = v___x_1110_;
v_a_1107_ = v_a_1130_;
goto v___jp_1105_;
}
v___jp_1084_:
{
if (v___y_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec_ref(v___y_1086_);
v___x_1088_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1083_, v___y_1078_, v___y_1080_);
lean_dec(v_a_1083_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v___x_1088_, 0);
lean_dec(v_unused_1096_);
v___x_1090_ = v___x_1088_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v___x_1088_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 1);
lean_ctor_set(v___x_1090_, 0, v___y_1085_);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___y_1085_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___y_1085_);
v_a_1097_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1088_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1088_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_dec_ref(v___y_1085_);
lean_dec(v_a_1083_);
return v___y_1086_;
}
}
v___jp_1105_:
{
uint8_t v___x_1108_; 
v___x_1108_ = l_Lean_Exception_isInterrupt(v_a_1107_);
if (v___x_1108_ == 0)
{
uint8_t v___x_1109_; 
lean_inc_ref(v_a_1107_);
v___x_1109_ = l_Lean_Exception_isRuntime(v_a_1107_);
v___y_1085_ = v_a_1107_;
v___y_1086_ = v___y_1106_;
v___y_1087_ = v___x_1109_;
goto v___jp_1084_;
}
else
{
v___y_1085_ = v_a_1107_;
v___y_1086_ = v___y_1106_;
v___y_1087_ = v___x_1108_;
goto v___jp_1084_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_x_1076_);
v_a_1131_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1082_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1082_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1146_, lean_object* v_x_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1146_, v_x_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_a_1162_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1153_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1153_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1170_, v_x_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1178_, lean_object* v_mvarId_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1179_, v_x_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1187_, lean_object* v_mvarId_1188_, lean_object* v_x_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1187_, v_mvarId_1188_, v_x_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1196_, lean_object* v_fuel_1197_, lean_object* v_fvarId_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_MVarId_exfalso(v_mvarId_1196_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v___x_1206_ = lean_st_mk_ref(v_fuel_1197_);
v___x_1207_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1205_, v_fvarId_1198_, v___x_1206_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1216_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1210_ = v___x_1207_;
v_isShared_1211_ = v_isSharedCheck_1216_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1216_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_st_ref_get(v___x_1206_);
lean_dec(v___x_1206_);
lean_dec(v___x_1212_);
if (v_isShared_1211_ == 0)
{
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1208_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
lean_dec(v___x_1206_);
return v___x_1207_;
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_fvarId_1198_);
lean_dec(v_fuel_1197_);
v_a_1217_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1204_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1204_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1225_, lean_object* v_fuel_1226_, lean_object* v_fvarId_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1225_, v_fuel_1226_, v_fvarId_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1234_, lean_object* v___f_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1234_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; uint8_t v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
v___x_1243_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
if (v___x_1243_ == 0)
{
lean_dec_ref(v___f_1235_);
return v___x_1241_;
}
else
{
lean_object* v___x_1244_; 
lean_dec_ref_known(v___x_1241_, 1);
v___x_1244_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1244_;
}
}
else
{
lean_dec_ref(v___f_1235_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1245_, lean_object* v___f_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1245_, v___f_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1253_, lean_object* v_fvarId_1254_, lean_object* v_fuel_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; 
lean_inc(v_fvarId_1254_);
lean_inc(v_mvarId_1253_);
v___f_1261_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1261_, 0, v_mvarId_1253_);
lean_closure_set(v___f_1261_, 1, v_fuel_1255_);
lean_closure_set(v___f_1261_, 2, v_fvarId_1254_);
v___f_1262_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1262_, 0, v_fvarId_1254_);
lean_closure_set(v___f_1262_, 1, v___f_1261_);
v___x_1263_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1253_, v___f_1262_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1264_, lean_object* v_fvarId_1265_, lean_object* v_fuel_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1264_, v_fvarId_1265_, v_fuel_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
return v_res_1272_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1273_){
_start:
{
uint8_t v___x_1274_; 
v___x_1274_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1275_){
_start:
{
uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_res_1276_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1275_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1278_, lean_object* v_acc_1279_){
_start:
{
if (lean_obj_tag(v_e_1278_) == 7)
{
lean_object* v_binderType_1280_; lean_object* v_body_1281_; uint8_t v___y_1283_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_binderType_1280_ = lean_ctor_get(v_e_1278_, 1);
v_body_1281_ = lean_ctor_get(v_e_1278_, 2);
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_expr_has_loose_bvar(v_body_1281_, v___x_1287_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_Expr_isEq(v_binderType_1280_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = l_Lean_Expr_isHEq(v_binderType_1280_);
v___y_1283_ = v___x_1290_;
goto v___jp_1282_;
}
else
{
v___y_1283_ = v___x_1289_;
goto v___jp_1282_;
}
}
else
{
uint8_t v___x_1291_; 
v___x_1291_ = 0;
v___y_1283_ = v___x_1291_;
goto v___jp_1282_;
}
v___jp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_box(v___y_1283_);
v___x_1285_ = lean_array_push(v_acc_1279_, v___x_1284_);
v_e_1278_ = v_body_1281_;
v_acc_1279_ = v___x_1285_;
goto _start;
}
}
else
{
return v_acc_1279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1292_, lean_object* v_acc_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1292_, v_acc_1293_);
lean_dec_ref(v_e_1292_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1299_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1297_, v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Meta_mkGenDiseqMask(v_e_1300_);
lean_dec_ref(v_e_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___f_1309_; lean_object* v___x_4344__overap_1310_; lean_object* v___x_1311_; 
v___f_1309_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1310_ = lean_panic_fn_borrowed(v___f_1309_, v_msg_1303_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
v___x_1311_ = lean_apply_5(v___x_4344__overap_1310_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, lean_box(0));
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Lean_Expr_hasMVar(v_e_1319_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_e_1319_);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; lean_object* v_mctx_1325_; lean_object* v___x_1326_; lean_object* v_fst_1327_; lean_object* v_snd_1328_; lean_object* v___x_1329_; lean_object* v_cache_1330_; lean_object* v_zetaDeltaFVarIds_1331_; lean_object* v_postponed_1332_; lean_object* v_diag_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1342_; 
v___x_1324_ = lean_st_ref_get(v___y_1320_);
v_mctx_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc_ref(v_mctx_1325_);
lean_dec(v___x_1324_);
v___x_1326_ = l_Lean_instantiateMVarsCore(v_mctx_1325_, v_e_1319_);
v_fst_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_fst_1327_);
v_snd_1328_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_snd_1328_);
lean_dec_ref(v___x_1326_);
v___x_1329_ = lean_st_ref_take(v___y_1320_);
v_cache_1330_ = lean_ctor_get(v___x_1329_, 1);
v_zetaDeltaFVarIds_1331_ = lean_ctor_get(v___x_1329_, 2);
v_postponed_1332_ = lean_ctor_get(v___x_1329_, 3);
v_diag_1333_ = lean_ctor_get(v___x_1329_, 4);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v___x_1329_, 0);
lean_dec(v_unused_1343_);
v___x_1335_ = v___x_1329_;
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_diag_1333_);
lean_inc(v_postponed_1332_);
lean_inc(v_zetaDeltaFVarIds_1331_);
lean_inc(v_cache_1330_);
lean_dec(v___x_1329_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_snd_1328_);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_snd_1328_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_cache_1330_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_zetaDeltaFVarIds_1331_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_postponed_1332_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_diag_1333_);
v___x_1338_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_st_ref_put(v___y_1320_, v___x_1338_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_fst_1327_);
return v___x_1340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1344_, v___y_1345_);
lean_dec(v___y_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1348_, v___y_1350_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1362_, uint8_t v_allowLevelAssignments_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1363_, v_k_1362_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
v_a_1378_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1369_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1369_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1386_, lean_object* v_allowLevelAssignments_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1393_; lean_object* v_res_1394_; 
v_allowLevelAssignments_boxed_1393_ = lean_unbox(v_allowLevelAssignments_1387_);
v_res_1394_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1386_, v_allowLevelAssignments_boxed_1393_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1395_, lean_object* v_k_1396_, uint8_t v_allowLevelAssignments_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1396_, v_allowLevelAssignments_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_k_1405_, lean_object* v_allowLevelAssignments_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1412_; lean_object* v_res_1413_; 
v_allowLevelAssignments_boxed_1412_ = lean_unbox(v_allowLevelAssignments_1406_);
v_res_1413_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1404_, v_k_1405_, v_allowLevelAssignments_boxed_1412_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1416_, size_t v_sz_1417_, size_t v_i_1418_, lean_object* v_b_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_a_1426_; uint8_t v___x_1430_; 
v___x_1430_ = lean_usize_dec_lt(v_i_1418_, v_sz_1417_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_b_1419_);
return v___x_1431_;
}
else
{
lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1594_; 
v_snd_1432_ = lean_ctor_get(v_b_1419_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_b_1419_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v_b_1419_, 0);
lean_dec(v_unused_1595_);
v___x_1434_ = v_b_1419_;
v_isShared_1435_ = v_isSharedCheck_1594_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_dec(v_b_1419_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1594_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_array_1436_; lean_object* v_start_1437_; lean_object* v_stop_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v_array_1436_ = lean_ctor_get(v_snd_1432_, 0);
v_start_1437_ = lean_ctor_get(v_snd_1432_, 1);
v_stop_1438_ = lean_ctor_get(v_snd_1432_, 2);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_nat_dec_lt(v_start_1437_, v_stop_1438_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1442_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1439_);
v___x_1442_ = v___x_1434_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1432_);
v___x_1442_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
else
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1590_; 
lean_inc(v_stop_1438_);
lean_inc(v_start_1437_);
lean_inc_ref(v_array_1436_);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_snd_1432_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; 
v_unused_1591_ = lean_ctor_get(v_snd_1432_, 2);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_snd_1432_, 1);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_snd_1432_, 0);
lean_dec(v_unused_1593_);
v___x_1446_ = v_snd_1432_;
v_isShared_1447_ = v_isSharedCheck_1590_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v_snd_1432_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1590_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1448_ = lean_array_fget(v_array_1436_, v_start_1437_);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_add(v_start_1437_, v___x_1449_);
lean_dec(v_start_1437_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1450_);
v___x_1452_ = v___x_1446_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_array_1436_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_stop_1438_);
v___x_1452_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_unbox(v___x_1448_);
lean_dec(v___x_1448_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1455_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v___x_1452_);
lean_ctor_set(v___x_1434_, 0, v___x_1439_);
v___x_1455_ = v___x_1434_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1452_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
v_a_1426_ = v___x_1455_;
goto v___jp_1425_;
}
}
else
{
lean_object* v_a_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___x_1529_; 
v_a_1457_ = lean_array_uget_borrowed(v_as_1416_, v_i_1418_);
lean_inc(v___y_1423_);
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
lean_inc(v_a_1457_);
v___x_1529_ = lean_infer_type(v_a_1457_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = l_Lean_Meta_matchEq_x3f(v_a_1530_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
if (lean_obj_tag(v_a_1532_) == 1)
{
lean_object* v_val_1533_; lean_object* v_snd_1534_; lean_object* v_fst_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1571_; 
v_val_1533_ = lean_ctor_get(v_a_1532_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v_a_1532_, 1);
v_snd_1534_ = lean_ctor_get(v_val_1533_, 1);
lean_inc(v_snd_1534_);
lean_dec(v_val_1533_);
v_fst_1535_ = lean_ctor_get(v_snd_1534_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_snd_1534_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_snd_1534_, 1);
lean_dec(v_unused_1572_);
v___x_1537_ = v_snd_1534_;
v_isShared_1538_ = v_isSharedCheck_1571_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_fst_1535_);
lean_dec(v_snd_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1571_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_Meta_mkEqRefl(v_fst_1535_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
lean_inc(v_a_1457_);
v___x_1541_ = l_Lean_Meta_isExprDefEq(v_a_1457_, v_a_1540_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1554_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1554_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1554_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
lean_del_object(v___x_1434_);
v___x_1547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v___x_1452_);
lean_ctor_set(v___x_1537_, 0, v___x_1547_);
v___x_1549_ = v___x_1537_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1452_);
v___x_1549_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1549_);
v___x_1551_ = v___x_1544_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
else
{
lean_del_object(v___x_1544_);
lean_del_object(v___x_1537_);
v___y_1459_ = v___y_1420_;
v___y_1460_ = v___y_1421_;
v___y_1461_ = v___y_1422_;
v___y_1462_ = v___y_1423_;
goto v___jp_1458_;
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_del_object(v___x_1537_);
lean_dec_ref(v___x_1452_);
lean_del_object(v___x_1434_);
v_a_1555_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1541_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1541_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_del_object(v___x_1537_);
lean_dec_ref(v___x_1452_);
lean_del_object(v___x_1434_);
v_a_1563_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1539_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1539_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
else
{
lean_dec(v_a_1532_);
v___y_1459_ = v___y_1420_;
v___y_1460_ = v___y_1421_;
v___y_1461_ = v___y_1422_;
v___y_1462_ = v___y_1423_;
goto v___jp_1458_;
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v___x_1452_);
lean_del_object(v___x_1434_);
v_a_1573_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1531_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1531_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v___x_1452_);
lean_del_object(v___x_1434_);
v_a_1581_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1529_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1529_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
v___jp_1458_:
{
lean_object* v___x_1463_; 
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1460_);
lean_inc_ref(v___y_1459_);
lean_inc(v_a_1457_);
v___x_1463_ = lean_infer_type(v_a_1457_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = l_Lean_Meta_matchHEq_x3f(v_a_1464_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
if (lean_obj_tag(v_a_1466_) == 1)
{
lean_object* v_val_1467_; lean_object* v_snd_1468_; lean_object* v_fst_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1508_; 
lean_del_object(v___x_1434_);
v_val_1467_ = lean_ctor_get(v_a_1466_, 0);
lean_inc(v_val_1467_);
lean_dec_ref_known(v_a_1466_, 1);
v_snd_1468_ = lean_ctor_get(v_val_1467_, 1);
lean_inc(v_snd_1468_);
lean_dec(v_val_1467_);
v_fst_1469_ = lean_ctor_get(v_snd_1468_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_snd_1468_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v_snd_1468_, 1);
lean_dec(v_unused_1509_);
v___x_1471_ = v_snd_1468_;
v_isShared_1472_ = v_isSharedCheck_1508_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_fst_1469_);
lean_dec(v_snd_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1508_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Meta_mkHEqRefl(v_fst_1469_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
lean_inc(v_a_1457_);
v___x_1475_ = l_Lean_Meta_isExprDefEq(v_a_1457_, v_a_1474_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1491_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1491_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1491_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_unbox(v_a_1476_);
lean_dec(v_a_1476_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1452_);
lean_ctor_set(v___x_1471_, 0, v___x_1481_);
v___x_1483_ = v___x_1471_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1452_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1483_);
v___x_1485_ = v___x_1478_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
lean_object* v___x_1489_; 
lean_del_object(v___x_1478_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1452_);
lean_ctor_set(v___x_1471_, 0, v___x_1439_);
v___x_1489_ = v___x_1471_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1452_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
v_a_1426_ = v___x_1489_;
goto v___jp_1425_;
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_del_object(v___x_1471_);
lean_dec_ref(v___x_1452_);
v_a_1492_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1475_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1475_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_del_object(v___x_1471_);
lean_dec_ref(v___x_1452_);
v_a_1500_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1473_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1473_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_a_1466_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v___x_1452_);
lean_ctor_set(v___x_1434_, 0, v___x_1439_);
v___x_1511_ = v___x_1434_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1452_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
v_a_1426_ = v___x_1511_;
goto v___jp_1425_;
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v___x_1452_);
lean_del_object(v___x_1434_);
v_a_1513_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1465_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1465_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v___x_1452_);
lean_del_object(v___x_1434_);
v_a_1521_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1463_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1463_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
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
v___jp_1425_:
{
size_t v___x_1427_; size_t v___x_1428_; 
v___x_1427_ = ((size_t)1ULL);
v___x_1428_ = lean_usize_add(v_i_1418_, v___x_1427_);
v_i_1418_ = v___x_1428_;
v_b_1419_ = v_a_1426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1596_, lean_object* v_sz_1597_, lean_object* v_i_1598_, lean_object* v_b_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
size_t v_sz_boxed_1605_; size_t v_i_boxed_1606_; lean_object* v_res_1607_; 
v_sz_boxed_1605_ = lean_unbox_usize(v_sz_1597_);
lean_dec(v_sz_1597_);
v_i_boxed_1606_ = lean_unbox_usize(v_i_1598_);
lean_dec(v_i_1598_);
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1596_, v_sz_boxed_1605_, v_i_boxed_1606_, v_b_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v_as_1596_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1608_, uint8_t v___x_1609_, lean_object* v_localDecl_1610_, lean_object* v_mvarId_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
lean_inc_ref(v___x_1608_);
v___x_1617_ = l_Lean_Meta_forallMetaTelescope(v___x_1608_, v___x_1609_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v_fst_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1708_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v_fst_1619_ = lean_ctor_get(v_a_1618_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_a_1618_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v_a_1618_, 1);
lean_dec(v_unused_1709_);
v___x_1621_ = v_a_1618_;
v_isShared_1622_ = v_isSharedCheck_1708_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_fst_1619_);
lean_dec(v_a_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1708_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1623_ = l_Lean_Meta_mkGenDiseqMask(v___x_1608_);
lean_dec_ref(v___x_1608_);
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = lean_array_get_size(v___x_1623_);
v___x_1626_ = l_Array_toSubarray___redArg(v___x_1623_, v___x_1624_, v___x_1625_);
v___x_1627_ = lean_box(0);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 1, v___x_1626_);
lean_ctor_set(v___x_1621_, 0, v___x_1627_);
v___x_1629_ = v___x_1621_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1626_);
v___x_1629_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
size_t v_sz_1630_; size_t v___x_1631_; lean_object* v___x_1632_; 
v_sz_1630_ = lean_array_size(v_fst_1619_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1619_, v_sz_1630_, v___x_1631_, v___x_1629_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1698_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1698_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1698_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v_fst_1637_; 
v_fst_1637_ = lean_ctor_get(v_a_1633_, 0);
lean_inc(v_fst_1637_);
lean_dec(v_a_1633_);
if (lean_obj_tag(v_fst_1637_) == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1693_; 
lean_del_object(v___x_1635_);
v___x_1638_ = l_Lean_LocalDecl_toExpr(v_localDecl_1610_);
v___x_1639_ = l_Lean_mkAppN(v___x_1638_, v_fst_1619_);
lean_dec(v_fst_1619_);
v___x_1640_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1639_, v___y_1613_);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1693_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1693_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; 
lean_inc(v_a_1641_);
v___x_1645_ = l_Lean_Meta_hasAssignableMVar(v_a_1641_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1684_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1684_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1684_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_unbox(v_a_1646_);
lean_dec(v_a_1646_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; 
lean_del_object(v___x_1648_);
v___x_1651_ = l_Lean_MVarId_getType(v_mvarId_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1653_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = l_Lean_Meta_mkFalseElim(v_a_1652_, v_a_1641_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1664_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1664_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1664_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 1);
lean_ctor_set(v___x_1643_, 0, v_a_1654_);
v___x_1659_ = v___x_1643_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1659_);
v___x_1661_ = v___x_1656_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
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
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_del_object(v___x_1643_);
v_a_1665_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1653_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1653_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_del_object(v___x_1643_);
lean_dec(v_a_1641_);
v_a_1673_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1651_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1651_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
else
{
lean_object* v___x_1682_; 
lean_del_object(v___x_1643_);
lean_dec(v_a_1641_);
lean_dec(v_mvarId_1611_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1627_);
v___x_1682_ = v___x_1648_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1627_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_del_object(v___x_1643_);
lean_dec(v_a_1641_);
lean_dec(v_mvarId_1611_);
v_a_1685_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1645_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1645_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
else
{
lean_object* v_val_1694_; lean_object* v___x_1696_; 
lean_dec(v_fst_1619_);
lean_dec(v_mvarId_1611_);
lean_dec_ref(v_localDecl_1610_);
v_val_1694_ = lean_ctor_get(v_fst_1637_, 0);
lean_inc(v_val_1694_);
lean_dec_ref_known(v_fst_1637_, 1);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_val_1694_);
v___x_1696_ = v___x_1635_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_val_1694_);
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
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_fst_1619_);
lean_dec(v_mvarId_1611_);
lean_dec_ref(v_localDecl_1610_);
v_a_1699_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1632_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1632_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v_mvarId_1611_);
lean_dec_ref(v_localDecl_1610_);
lean_dec_ref(v___x_1608_);
v_a_1710_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1617_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1617_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1718_, lean_object* v___x_1719_, lean_object* v_localDecl_1720_, lean_object* v_mvarId_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v___x_6076__boxed_1727_; lean_object* v_res_1728_; 
v___x_6076__boxed_1727_ = lean_unbox(v___x_1719_);
v_res_1728_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1718_, v___x_6076__boxed_1727_, v_localDecl_1720_, v_mvarId_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1728_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1733_ = lean_unsigned_to_nat(2u);
v___x_1734_ = lean_unsigned_to_nat(120u);
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1737_ = l_mkPanicMessageWithDecl(v___x_1736_, v___x_1735_, v___x_1734_, v___x_1733_, v___x_1732_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1738_, lean_object* v_localDecl_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = l_Lean_LocalDecl_type(v_localDecl_1739_);
lean_inc_ref(v___x_1745_);
v___x_1746_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec_ref(v___x_1745_);
lean_dec_ref(v_localDecl_1739_);
lean_dec(v_mvarId_1738_);
v___x_1747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1748_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1747_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1748_;
}
else
{
uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___f_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1749_ = 0;
v___x_1750_ = lean_box(v___x_1749_);
lean_inc(v_mvarId_1738_);
v___f_1751_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1751_, 0, v___x_1745_);
lean_closure_set(v___f_1751_, 1, v___x_1750_);
lean_closure_set(v___f_1751_, 2, v_localDecl_1739_);
lean_closure_set(v___f_1751_, 3, v_mvarId_1738_);
v___x_1752_ = 0;
v___x_1753_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1751_, v___x_1752_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1773_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1773_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1773_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
if (lean_obj_tag(v_a_1754_) == 1)
{
lean_object* v_val_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1767_; 
lean_del_object(v___x_1756_);
v_val_1758_ = lean_ctor_get(v_a_1754_, 0);
lean_inc(v_val_1758_);
lean_dec_ref_known(v_a_1754_, 1);
v___x_1759_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1738_, v_val_1758_, v_a_1741_);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; 
v_unused_1768_ = lean_ctor_get(v___x_1759_, 0);
lean_dec(v_unused_1768_);
v___x_1761_ = v___x_1759_;
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
else
{
lean_dec(v___x_1759_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1763_ = lean_box(v___x_1746_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1763_);
v___x_1765_ = v___x_1761_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_dec(v_a_1754_);
lean_dec(v_mvarId_1738_);
v___x_1769_ = lean_box(v___x_1752_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1769_);
v___x_1771_ = v___x_1756_;
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
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec(v_mvarId_1738_);
v_a_1774_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1753_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1753_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1782_, lean_object* v_localDecl_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1782_, v_localDecl_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1789_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1803_ = l_Lean_mkConst(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1804_; lean_object* v_dummy_1805_; 
v___x_1804_ = lean_box(0);
v_dummy_1805_ = l_Lean_Expr_sort___override(v___x_1804_);
return v_dummy_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1806_, lean_object* v_mvarId_1807_, lean_object* v_as_1808_, size_t v_sz_1809_, size_t v_i_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_usize_dec_lt(v_i_1810_, v_sz_1809_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_b_1811_);
return v___x_1818_;
}
else
{
lean_object* v_snd_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_2469_; 
v_snd_1819_ = lean_ctor_get(v_b_1811_, 1);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_b_1811_);
if (v_isSharedCheck_2469_ == 0)
{
lean_object* v_unused_2470_; 
v_unused_2470_ = lean_ctor_get(v_b_1811_, 0);
lean_dec(v_unused_2470_);
v___x_1821_ = v_b_1811_;
v_isShared_1822_ = v_isSharedCheck_2469_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_snd_1819_);
lean_dec(v_b_1811_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_2469_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_a_1824_; lean_object* v___x_1830_; lean_object* v_a_1832_; lean_object* v_a_1837_; 
v___x_1830_ = lean_box(0);
v_a_1837_ = lean_array_uget(v_as_1808_, v_i_1810_);
if (lean_obj_tag(v_a_1837_) == 0)
{
lean_del_object(v___x_1821_);
v_a_1832_ = v_snd_1819_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_2468_; 
v_val_1838_ = lean_ctor_get(v_a_1837_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_a_1837_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_1840_ = v_a_1837_;
v_isShared_1841_ = v_isSharedCheck_2468_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_val_1838_);
lean_dec(v_a_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_2468_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___x_1883_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; uint8_t v___x_1911_; lean_object* v___y_1913_; uint8_t v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1919_; uint8_t v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; uint8_t v___y_1924_; uint8_t v___y_1926_; uint8_t v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; uint8_t v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; uint8_t v___y_1940_; 
v___x_1842_ = lean_box(0);
v___x_1883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1911_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1838_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1955_; uint8_t v___y_1957_; uint8_t v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1966_; lean_object* v___y_1967_; uint8_t v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; uint8_t v___y_1971_; lean_object* v___y_1972_; uint8_t v___y_1973_; lean_object* v___y_1976_; uint8_t v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; uint8_t v___y_1980_; lean_object* v___y_1981_; lean_object* v_a_1982_; lean_object* v___y_1986_; lean_object* v___y_1987_; uint8_t v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; uint8_t v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_2030_; uint8_t v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; uint8_t v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2059_; uint8_t v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2064_; uint8_t v___y_2065_; lean_object* v___y_2067_; uint8_t v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; uint8_t v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; uint8_t v___y_2074_; lean_object* v___y_2077_; uint8_t v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; uint8_t v___y_2081_; lean_object* v___y_2082_; uint8_t v___y_2083_; lean_object* v___y_2096_; uint8_t v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; uint8_t v___y_2100_; lean_object* v___y_2101_; uint8_t v___y_2102_; uint8_t v___y_2104_; uint8_t v_isHEq_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; uint8_t v___y_2119_; uint8_t v_isEq_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___x_2405_; 
v___x_1955_ = l_Lean_LocalDecl_type(v_val_1838_);
lean_inc_ref(v___x_1955_);
v___x_2405_ = l_Lean_Meta_matchNot_x3f(v___x_1955_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
if (lean_obj_tag(v_a_2406_) == 1)
{
lean_object* v_val_2407_; lean_object* v___x_2408_; 
v_val_2407_ = lean_ctor_get(v_a_2406_, 0);
lean_inc(v_val_2407_);
lean_dec_ref_known(v_a_2406_, 1);
v___x_2408_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2407_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
if (lean_obj_tag(v_a_2409_) == 1)
{
lean_object* v_val_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2451_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec_ref(v_config_1806_);
v_val_2410_ = lean_ctor_get(v_a_2409_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_a_2409_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2412_ = v_a_2409_;
v_isShared_2413_ = v_isSharedCheck_2451_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_val_2410_);
lean_dec(v_a_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2451_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; 
lean_inc(v_mvarId_1807_);
v___x_2414_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___x_2416_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2417_ = l_Lean_mkFVar(v_val_2410_);
v___x_2418_ = l_Lean_Expr_app___override(v___x_2416_, v___x_2417_);
v___x_2419_ = l_Lean_Meta_mkFalseElim(v_a_2415_, v___x_2418_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v___x_2421_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2420_, v___y_1813_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
lean_dec_ref_known(v___x_2421_, 1);
v___x_2422_ = lean_box(v___x_1817_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2422_);
v___x_2424_ = v___x_2412_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v___x_1842_);
v_a_1824_ = v___x_2425_;
goto v___jp_1823_;
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_del_object(v___x_2412_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_2427_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2421_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2421_);
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
lean_del_object(v___x_2412_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2435_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2419_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2419_);
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
lean_del_object(v___x_2412_);
lean_dec(v_val_2410_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2443_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2414_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2414_);
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
lean_dec(v_a_2409_);
v___y_2271_ = v___y_1812_;
v___y_2272_ = v___y_1813_;
v___y_2273_ = v___y_1814_;
v___y_2274_ = v___y_1815_;
goto v___jp_2270_;
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2452_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2408_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2408_);
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
else
{
lean_dec(v_a_2406_);
v___y_2271_ = v___y_1812_;
v___y_2272_ = v___y_1813_;
v___y_2273_ = v___y_1814_;
v___y_2274_ = v___y_1815_;
goto v___jp_2270_;
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2460_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2405_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2405_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
v___jp_1956_:
{
uint8_t v_genDiseq_1963_; 
v_genDiseq_1963_ = lean_ctor_get_uint8(v_config_1806_, sizeof(void*)*1 + 2);
if (v_genDiseq_1963_ == 0)
{
lean_dec_ref(v___x_1955_);
v___y_1934_ = v___y_1957_;
v___y_1935_ = v___y_1959_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1958_;
v___y_1938_ = v___y_1962_;
v___y_1939_ = v___y_1961_;
v___y_1940_ = v___x_1911_;
goto v___jp_1933_;
}
else
{
uint8_t v___x_1964_; 
v___x_1964_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1955_);
v___y_1934_ = v___y_1957_;
v___y_1935_ = v___y_1959_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1958_;
v___y_1938_ = v___y_1962_;
v___y_1939_ = v___y_1961_;
v___y_1940_ = v___x_1964_;
goto v___jp_1933_;
}
}
v___jp_1965_:
{
if (v___y_1973_ == 0)
{
lean_dec_ref(v___y_1967_);
v___y_1957_ = v___y_1968_;
v___y_1958_ = v___y_1971_;
v___y_1959_ = v___y_1970_;
v___y_1960_ = v___y_1969_;
v___y_1961_ = v___y_1972_;
v___y_1962_ = v___y_1966_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_1974_; 
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___y_1967_);
return v___x_1974_;
}
}
v___jp_1975_:
{
uint8_t v___x_1983_; 
v___x_1983_ = l_Lean_Exception_isInterrupt(v_a_1982_);
if (v___x_1983_ == 0)
{
uint8_t v___x_1984_; 
lean_inc_ref(v_a_1982_);
v___x_1984_ = l_Lean_Exception_isRuntime(v_a_1982_);
v___y_1966_ = v___y_1976_;
v___y_1967_ = v_a_1982_;
v___y_1968_ = v___y_1977_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1979_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___x_1984_;
goto v___jp_1965_;
}
else
{
v___y_1966_ = v___y_1976_;
v___y_1967_ = v_a_1982_;
v___y_1968_ = v___y_1977_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1979_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___x_1983_;
goto v___jp_1965_;
}
}
v___jp_1985_:
{
if (lean_obj_tag(v___y_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_a_1994_ = lean_ctor_get(v___y_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___y_1993_, 1);
v___x_1995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_1996_ = l_Lean_Expr_isConstOf(v_a_1994_, v___x_1995_);
lean_dec(v_a_1994_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v___y_1987_);
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1991_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1989_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1986_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_1997_; 
lean_inc_ref(v___y_1987_);
v___x_1997_ = l_Lean_Meta_mkEqRefl(v___y_1987_, v___y_1990_, v___y_1989_, v___y_1992_, v___y_1986_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_1999_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
lean_inc(v_mvarId_1807_);
v___x_1999_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_1990_, v___y_1989_, v___y_1992_, v___y_1986_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v_nargs_2001_; lean_object* v___x_2002_; lean_object* v_dummy_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v_nargs_2001_ = l_Lean_Expr_getAppNumArgs(v___y_1987_);
v___x_2002_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2003_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2001_);
v___x_2004_ = lean_mk_array(v_nargs_2001_, v_dummy_2003_);
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = lean_nat_sub(v_nargs_2001_, v___x_2005_);
lean_dec(v_nargs_2001_);
v___x_2007_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1987_, v___x_2004_, v___x_2006_);
v___x_2008_ = lean_array_push(v___x_2007_, v_a_1998_);
v___x_2009_ = l_Lean_mkAppN(v___x_2002_, v___x_2008_);
lean_dec_ref(v___x_2008_);
lean_inc(v_val_1838_);
v___x_2010_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2011_ = l_Lean_Meta_mkAbsurd(v_a_2000_, v___x_2010_, v___x_2009_, v___y_1990_, v___y_1989_, v___y_1992_, v___y_1986_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
lean_inc(v_mvarId_1807_);
v___x_2013_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2012_, v___y_1989_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; 
v_unused_2023_ = lean_ctor_get(v___x_2013_, 0);
lean_dec(v_unused_2023_);
v___x_2015_ = v___x_2013_;
v_isShared_2016_ = v_isSharedCheck_2022_;
goto v_resetjp_2014_;
}
else
{
lean_dec(v___x_2013_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2022_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = lean_box(v___x_1817_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set_tag(v___x_2015_, 1);
lean_ctor_set(v___x_2015_, 0, v___x_2017_);
v___x_2019_ = v___x_2015_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v___x_1842_);
v_a_1824_ = v___x_2020_;
goto v___jp_1823_;
}
}
}
else
{
lean_object* v_a_2024_; 
v_a_2024_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2013_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v_a_1982_ = v_a_2024_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2025_; 
v_a_2025_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v_a_1982_ = v_a_2025_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2026_; 
lean_dec(v_a_1998_);
lean_dec_ref(v___y_1987_);
v_a_2026_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_1999_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v_a_1982_ = v_a_2026_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2027_; 
lean_dec_ref(v___y_1987_);
v_a_2027_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_1997_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v_a_1982_ = v_a_2027_;
goto v___jp_1975_;
}
}
}
else
{
lean_object* v_a_2028_; 
lean_dec_ref(v___y_1987_);
v_a_2028_ = lean_ctor_get(v___y_1993_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___y_1993_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1989_;
v___y_1979_ = v___y_1990_;
v___y_1980_ = v___y_1991_;
v___y_1981_ = v___y_1992_;
v_a_1982_ = v_a_2028_;
goto v___jp_1975_;
}
}
v___jp_2029_:
{
lean_object* v___x_2036_; 
lean_inc_ref(v___x_1955_);
v___x_2036_ = l_Lean_Meta_mkDecide(v___x_1955_, v___y_2033_, v___y_2032_, v___y_2035_, v___y_2030_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; uint8_t v_transparency_2039_; uint8_t v___x_2040_; uint8_t v___x_2041_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = l_Lean_Meta_Context_config(v___y_2033_);
v_transparency_2039_ = lean_ctor_get_uint8(v___x_2038_, 9);
lean_dec_ref(v___x_2038_);
v___x_2040_ = 1;
v___x_2041_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2039_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v_keyedConfig_2042_; uint8_t v_trackZetaDelta_2043_; lean_object* v_zetaDeltaSet_2044_; lean_object* v_lctx_2045_; lean_object* v_localInstances_2046_; lean_object* v_defEqCtx_x3f_2047_; lean_object* v_synthPendingDepth_2048_; lean_object* v_customCanUnfoldPredicate_x3f_2049_; uint8_t v_univApprox_2050_; uint8_t v_inTypeClassResolution_2051_; uint8_t v_cacheInferType_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_keyedConfig_2042_ = lean_ctor_get(v___y_2033_, 0);
v_trackZetaDelta_2043_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*7);
v_zetaDeltaSet_2044_ = lean_ctor_get(v___y_2033_, 1);
v_lctx_2045_ = lean_ctor_get(v___y_2033_, 2);
v_localInstances_2046_ = lean_ctor_get(v___y_2033_, 3);
v_defEqCtx_x3f_2047_ = lean_ctor_get(v___y_2033_, 4);
v_synthPendingDepth_2048_ = lean_ctor_get(v___y_2033_, 5);
v_customCanUnfoldPredicate_x3f_2049_ = lean_ctor_get(v___y_2033_, 6);
v_univApprox_2050_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2051_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*7 + 2);
v_cacheInferType_2052_ = lean_ctor_get_uint8(v___y_2033_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2042_);
v___x_2053_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2040_, v_keyedConfig_2042_);
lean_inc(v_customCanUnfoldPredicate_x3f_2049_);
lean_inc(v_synthPendingDepth_2048_);
lean_inc(v_defEqCtx_x3f_2047_);
lean_inc_ref(v_localInstances_2046_);
lean_inc_ref(v_lctx_2045_);
lean_inc(v_zetaDeltaSet_2044_);
v___x_2054_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v_zetaDeltaSet_2044_);
lean_ctor_set(v___x_2054_, 2, v_lctx_2045_);
lean_ctor_set(v___x_2054_, 3, v_localInstances_2046_);
lean_ctor_set(v___x_2054_, 4, v_defEqCtx_x3f_2047_);
lean_ctor_set(v___x_2054_, 5, v_synthPendingDepth_2048_);
lean_ctor_set(v___x_2054_, 6, v_customCanUnfoldPredicate_x3f_2049_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*7, v_trackZetaDelta_2043_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*7 + 1, v_univApprox_2050_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2051_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*7 + 3, v_cacheInferType_2052_);
lean_inc(v___y_2030_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2032_);
lean_inc(v_a_2037_);
v___x_2055_ = lean_whnf(v_a_2037_, v___x_2054_, v___y_2032_, v___y_2035_, v___y_2030_);
v___y_1986_ = v___y_2030_;
v___y_1987_ = v_a_2037_;
v___y_1988_ = v___y_2031_;
v___y_1989_ = v___y_2032_;
v___y_1990_ = v___y_2033_;
v___y_1991_ = v___y_2034_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___x_2055_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2056_; 
lean_inc(v___y_2030_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2033_);
lean_inc(v_a_2037_);
v___x_2056_ = lean_whnf(v_a_2037_, v___y_2033_, v___y_2032_, v___y_2035_, v___y_2030_);
v___y_1986_ = v___y_2030_;
v___y_1987_ = v_a_2037_;
v___y_1988_ = v___y_2031_;
v___y_1989_ = v___y_2032_;
v___y_1990_ = v___y_2033_;
v___y_1991_ = v___y_2034_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___x_2056_;
goto v___jp_1985_;
}
}
else
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2036_, 1);
v___y_1976_ = v___y_2030_;
v___y_1977_ = v___y_2031_;
v___y_1978_ = v___y_2032_;
v___y_1979_ = v___y_2033_;
v___y_1980_ = v___y_2034_;
v___y_1981_ = v___y_2035_;
v_a_1982_ = v_a_2057_;
goto v___jp_1975_;
}
}
v___jp_2058_:
{
if (v___y_2065_ == 0)
{
v___y_1957_ = v___y_2060_;
v___y_1958_ = v___y_2063_;
v___y_1959_ = v___y_2062_;
v___y_1960_ = v___y_2061_;
v___y_1961_ = v___y_2064_;
v___y_1962_ = v___y_2059_;
goto v___jp_1956_;
}
else
{
v___y_2030_ = v___y_2059_;
v___y_2031_ = v___y_2060_;
v___y_2032_ = v___y_2061_;
v___y_2033_ = v___y_2062_;
v___y_2034_ = v___y_2063_;
v___y_2035_ = v___y_2064_;
goto v___jp_2029_;
}
}
v___jp_2066_:
{
if (v___y_2074_ == 0)
{
lean_dec_ref(v___y_2072_);
v___y_2059_ = v___y_2067_;
v___y_2060_ = v___y_2068_;
v___y_2061_ = v___y_2069_;
v___y_2062_ = v___y_2070_;
v___y_2063_ = v___y_2071_;
v___y_2064_ = v___y_2073_;
v___y_2065_ = v___x_1911_;
goto v___jp_2058_;
}
else
{
uint8_t v___x_2075_; 
v___x_2075_ = l_Lean_Expr_hasFVar(v___y_2072_);
lean_dec_ref(v___y_2072_);
if (v___x_2075_ == 0)
{
v___y_2030_ = v___y_2067_;
v___y_2031_ = v___y_2068_;
v___y_2032_ = v___y_2069_;
v___y_2033_ = v___y_2070_;
v___y_2034_ = v___y_2071_;
v___y_2035_ = v___y_2073_;
goto v___jp_2029_;
}
else
{
v___y_2059_ = v___y_2067_;
v___y_2060_ = v___y_2068_;
v___y_2061_ = v___y_2069_;
v___y_2062_ = v___y_2070_;
v___y_2063_ = v___y_2071_;
v___y_2064_ = v___y_2073_;
v___y_2065_ = v___x_1911_;
goto v___jp_2058_;
}
}
}
v___jp_2076_:
{
lean_object* v___x_2084_; 
lean_inc_ref(v___x_1955_);
v___x_2084_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1955_, v___y_2079_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; uint8_t v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = l_Lean_Expr_hasMVar(v_a_2085_);
if (v___x_2086_ == 0)
{
v___y_2067_ = v___y_2077_;
v___y_2068_ = v___y_2078_;
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v_a_2085_;
v___y_2073_ = v___y_2082_;
v___y_2074_ = v___y_2083_;
goto v___jp_2066_;
}
else
{
v___y_2067_ = v___y_2077_;
v___y_2068_ = v___y_2078_;
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2080_;
v___y_2071_ = v___y_2081_;
v___y_2072_ = v_a_2085_;
v___y_2073_ = v___y_2082_;
v___y_2074_ = v___x_1911_;
goto v___jp_2066_;
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2087_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2084_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2084_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
v___jp_2095_:
{
if (v___y_2102_ == 0)
{
v___y_1957_ = v___y_2097_;
v___y_1958_ = v___y_2100_;
v___y_1959_ = v___y_2099_;
v___y_1960_ = v___y_2098_;
v___y_1961_ = v___y_2101_;
v___y_1962_ = v___y_2096_;
goto v___jp_1956_;
}
else
{
v___y_2077_ = v___y_2096_;
v___y_2078_ = v___y_2097_;
v___y_2079_ = v___y_2098_;
v___y_2080_ = v___y_2099_;
v___y_2081_ = v___y_2100_;
v___y_2082_ = v___y_2101_;
v___y_2083_ = v___y_2102_;
goto v___jp_2076_;
}
}
v___jp_2103_:
{
uint8_t v_useDecide_2110_; 
v_useDecide_2110_ = lean_ctor_get_uint8(v_config_1806_, sizeof(void*)*1);
if (v_useDecide_2110_ == 0)
{
v___y_2096_ = v___y_2109_;
v___y_2097_ = v_isHEq_2105_;
v___y_2098_ = v___y_2107_;
v___y_2099_ = v___y_2106_;
v___y_2100_ = v___y_2104_;
v___y_2101_ = v___y_2108_;
v___y_2102_ = v___x_1911_;
goto v___jp_2095_;
}
else
{
uint8_t v___x_2111_; 
v___x_2111_ = l_Lean_Expr_hasFVar(v___x_1955_);
if (v___x_2111_ == 0)
{
v___y_2077_ = v___y_2109_;
v___y_2078_ = v_isHEq_2105_;
v___y_2079_ = v___y_2107_;
v___y_2080_ = v___y_2106_;
v___y_2081_ = v___y_2104_;
v___y_2082_ = v___y_2108_;
v___y_2083_ = v_useDecide_2110_;
goto v___jp_2076_;
}
else
{
v___y_2096_ = v___y_2109_;
v___y_2097_ = v_isHEq_2105_;
v___y_2098_ = v___y_2107_;
v___y_2099_ = v___y_2106_;
v___y_2100_ = v___y_2104_;
v___y_2101_ = v___y_2108_;
v___y_2102_ = v___x_1911_;
goto v___jp_2095_;
}
}
}
v___jp_2112_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Meta_isExprDefEq(v___y_2115_, v___y_2116_, v___y_2118_, v___y_2117_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; uint8_t v___x_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = lean_unbox(v_a_2121_);
lean_dec(v_a_2121_);
if (v___x_2122_ == 0)
{
v___y_2104_ = v___y_2119_;
v_isHEq_2105_ = v___x_1817_;
v___y_2106_ = v___y_2118_;
v___y_2107_ = v___y_2117_;
v___y_2108_ = v___y_2113_;
v___y_2109_ = v___y_2114_;
goto v___jp_2103_;
}
else
{
lean_object* v___x_2123_; 
lean_dec_ref(v___x_1955_);
lean_dec_ref(v_config_1806_);
lean_inc(v_mvarId_1807_);
v___x_2123_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_2118_, v___y_2117_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2126_ = l_Lean_Meta_mkEqOfHEq(v___x_2125_, v___x_1817_, v___y_2118_, v___y_2117_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = l_Lean_Meta_mkNoConfusion(v_a_2124_, v_a_2127_, v___y_2118_, v___y_2117_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2129_, v___y_2117_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec_ref_known(v___x_2130_, 1);
v___x_2131_ = lean_box(v___x_1817_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v___x_1842_);
v_a_1824_ = v___x_2133_;
goto v___jp_1823_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_2134_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2130_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2130_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2142_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2128_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2128_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v_a_2124_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2150_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2126_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2126_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2158_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2123_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2123_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2166_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2120_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2120_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
v___jp_2174_:
{
lean_object* v___x_2180_; 
lean_inc_ref(v___x_1955_);
v___x_2180_ = l_Lean_Meta_matchHEq_x3f(v___x_1955_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
if (lean_obj_tag(v_a_2181_) == 1)
{
lean_object* v_val_2182_; lean_object* v_snd_2183_; lean_object* v_snd_2184_; lean_object* v_fst_2185_; lean_object* v_fst_2186_; lean_object* v_fst_2187_; lean_object* v_snd_2188_; lean_object* v___x_2189_; 
v_val_2182_ = lean_ctor_get(v_a_2181_, 0);
lean_inc(v_val_2182_);
lean_dec_ref_known(v_a_2181_, 1);
v_snd_2183_ = lean_ctor_get(v_val_2182_, 1);
lean_inc(v_snd_2183_);
v_snd_2184_ = lean_ctor_get(v_snd_2183_, 1);
lean_inc(v_snd_2184_);
v_fst_2185_ = lean_ctor_get(v_val_2182_, 0);
lean_inc(v_fst_2185_);
lean_dec(v_val_2182_);
v_fst_2186_ = lean_ctor_get(v_snd_2183_, 0);
lean_inc(v_fst_2186_);
lean_dec(v_snd_2183_);
v_fst_2187_ = lean_ctor_get(v_snd_2184_, 0);
lean_inc(v_fst_2187_);
v_snd_2188_ = lean_ctor_get(v_snd_2184_, 1);
lean_inc(v_snd_2188_);
lean_dec(v_snd_2184_);
v___x_2189_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2186_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
if (lean_obj_tag(v_a_2190_) == 1)
{
lean_object* v_val_2191_; lean_object* v___x_2192_; 
v_val_2191_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_val_2191_);
lean_dec_ref_known(v_a_2190_, 1);
v___x_2192_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2188_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
if (lean_obj_tag(v_a_2193_) == 1)
{
lean_object* v_toConstantVal_2194_; lean_object* v_val_2195_; lean_object* v_toConstantVal_2196_; lean_object* v_name_2197_; lean_object* v_name_2198_; uint8_t v___x_2199_; 
v_toConstantVal_2194_ = lean_ctor_get(v_val_2191_, 0);
lean_inc_ref(v_toConstantVal_2194_);
lean_dec(v_val_2191_);
v_val_2195_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_val_2195_);
lean_dec_ref_known(v_a_2193_, 1);
v_toConstantVal_2196_ = lean_ctor_get(v_val_2195_, 0);
lean_inc_ref(v_toConstantVal_2196_);
lean_dec(v_val_2195_);
v_name_2197_ = lean_ctor_get(v_toConstantVal_2194_, 0);
lean_inc(v_name_2197_);
lean_dec_ref(v_toConstantVal_2194_);
v_name_2198_ = lean_ctor_get(v_toConstantVal_2196_, 0);
lean_inc(v_name_2198_);
lean_dec_ref(v_toConstantVal_2196_);
v___x_2199_ = lean_name_eq(v_name_2197_, v_name_2198_);
lean_dec(v_name_2198_);
lean_dec(v_name_2197_);
if (v___x_2199_ == 0)
{
v___y_2113_ = v___y_2178_;
v___y_2114_ = v___y_2179_;
v___y_2115_ = v_fst_2185_;
v___y_2116_ = v_fst_2187_;
v___y_2117_ = v___y_2177_;
v___y_2118_ = v___y_2176_;
v___y_2119_ = v_isEq_2175_;
goto v___jp_2112_;
}
else
{
if (v___x_1911_ == 0)
{
lean_dec(v_fst_2187_);
lean_dec(v_fst_2185_);
v___y_2104_ = v_isEq_2175_;
v_isHEq_2105_ = v___x_1817_;
v___y_2106_ = v___y_2176_;
v___y_2107_ = v___y_2177_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
goto v___jp_2103_;
}
else
{
v___y_2113_ = v___y_2178_;
v___y_2114_ = v___y_2179_;
v___y_2115_ = v_fst_2185_;
v___y_2116_ = v_fst_2187_;
v___y_2117_ = v___y_2177_;
v___y_2118_ = v___y_2176_;
v___y_2119_ = v_isEq_2175_;
goto v___jp_2112_;
}
}
}
else
{
lean_dec(v_a_2193_);
lean_dec(v_val_2191_);
lean_dec(v_fst_2187_);
lean_dec(v_fst_2185_);
v___y_2104_ = v_isEq_2175_;
v_isHEq_2105_ = v___x_1817_;
v___y_2106_ = v___y_2176_;
v___y_2107_ = v___y_2177_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
goto v___jp_2103_;
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_val_2191_);
lean_dec(v_fst_2187_);
lean_dec(v_fst_2185_);
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2200_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2192_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2192_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_dec(v_a_2190_);
lean_dec(v_snd_2188_);
lean_dec(v_fst_2187_);
lean_dec(v_fst_2185_);
v___y_2104_ = v_isEq_2175_;
v_isHEq_2105_ = v___x_1817_;
v___y_2106_ = v___y_2176_;
v___y_2107_ = v___y_2177_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
goto v___jp_2103_;
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v_snd_2188_);
lean_dec(v_fst_2187_);
lean_dec(v_fst_2185_);
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2208_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2189_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2189_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_dec(v_a_2181_);
v___y_2104_ = v_isEq_2175_;
v_isHEq_2105_ = v___x_1911_;
v___y_2106_ = v___y_2176_;
v___y_2107_ = v___y_2177_;
v___y_2108_ = v___y_2178_;
v___y_2109_ = v___y_2179_;
goto v___jp_2103_;
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2216_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2180_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2180_);
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
v___jp_2224_:
{
lean_object* v___x_2229_; 
lean_inc_ref(v___x_1955_);
v___x_2229_ = l_Lean_Meta_matchEq_x3f(v___x_1955_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
if (lean_obj_tag(v_a_2230_) == 1)
{
lean_object* v_val_2231_; lean_object* v_snd_2232_; lean_object* v_fst_2233_; lean_object* v_snd_2234_; lean_object* v___x_2235_; 
v_val_2231_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v_a_2230_, 1);
v_snd_2232_ = lean_ctor_get(v_val_2231_, 1);
lean_inc(v_snd_2232_);
lean_dec(v_val_2231_);
v_fst_2233_ = lean_ctor_get(v_snd_2232_, 0);
lean_inc(v_fst_2233_);
v_snd_2234_ = lean_ctor_get(v_snd_2232_, 1);
lean_inc(v_snd_2234_);
lean_dec(v_snd_2232_);
v___x_2235_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2233_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
if (lean_obj_tag(v_a_2236_) == 1)
{
lean_object* v_val_2237_; lean_object* v___x_2238_; 
v_val_2237_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v_a_2236_, 1);
v___x_2238_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2234_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
if (lean_obj_tag(v_a_2239_) == 1)
{
lean_object* v_toConstantVal_2240_; lean_object* v_val_2241_; lean_object* v_toConstantVal_2242_; lean_object* v_name_2243_; lean_object* v_name_2244_; uint8_t v___x_2245_; 
v_toConstantVal_2240_ = lean_ctor_get(v_val_2237_, 0);
lean_inc_ref(v_toConstantVal_2240_);
lean_dec(v_val_2237_);
v_val_2241_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_val_2241_);
lean_dec_ref_known(v_a_2239_, 1);
v_toConstantVal_2242_ = lean_ctor_get(v_val_2241_, 0);
lean_inc_ref(v_toConstantVal_2242_);
lean_dec(v_val_2241_);
v_name_2243_ = lean_ctor_get(v_toConstantVal_2240_, 0);
lean_inc(v_name_2243_);
lean_dec_ref(v_toConstantVal_2240_);
v_name_2244_ = lean_ctor_get(v_toConstantVal_2242_, 0);
lean_inc(v_name_2244_);
lean_dec_ref(v_toConstantVal_2242_);
v___x_2245_ = lean_name_eq(v_name_2243_, v_name_2244_);
lean_dec(v_name_2244_);
lean_dec(v_name_2243_);
if (v___x_2245_ == 0)
{
lean_dec_ref(v___x_1955_);
lean_dec_ref(v_config_1806_);
v___y_1844_ = v___y_2228_;
v___y_1845_ = v___y_2227_;
v___y_1846_ = v___y_2226_;
v___y_1847_ = v___y_2225_;
goto v___jp_1843_;
}
else
{
if (v___x_1911_ == 0)
{
lean_del_object(v___x_1840_);
v_isEq_2175_ = v___x_1817_;
v___y_2176_ = v___y_2225_;
v___y_2177_ = v___y_2226_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
goto v___jp_2174_;
}
else
{
lean_dec_ref(v___x_1955_);
lean_dec_ref(v_config_1806_);
v___y_1844_ = v___y_2228_;
v___y_1845_ = v___y_2227_;
v___y_1846_ = v___y_2226_;
v___y_1847_ = v___y_2225_;
goto v___jp_1843_;
}
}
}
else
{
lean_dec(v_a_2239_);
lean_dec(v_val_2237_);
lean_del_object(v___x_1840_);
v_isEq_2175_ = v___x_1817_;
v___y_2176_ = v___y_2225_;
v___y_2177_ = v___y_2226_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
goto v___jp_2174_;
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_val_2237_);
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2246_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2238_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2238_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_dec(v_a_2236_);
lean_dec(v_snd_2234_);
lean_del_object(v___x_1840_);
v_isEq_2175_ = v___x_1817_;
v___y_2176_ = v___y_2225_;
v___y_2177_ = v___y_2226_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
goto v___jp_2174_;
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_snd_2234_);
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2254_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2235_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2235_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_dec(v_a_2230_);
lean_del_object(v___x_1840_);
v_isEq_2175_ = v___x_1911_;
v___y_2176_ = v___y_2225_;
v___y_2177_ = v___y_2226_;
v___y_2178_ = v___y_2227_;
v___y_2179_ = v___y_2228_;
goto v___jp_2174_;
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2262_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2229_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2229_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
v___jp_2270_:
{
lean_object* v___x_2275_; 
lean_inc_ref(v___x_1955_);
v___x_2275_ = l_Lean_refutableHasNotBit_x3f(v___x_1955_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
if (lean_obj_tag(v_a_2276_) == 1)
{
lean_object* v_val_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec_ref(v_config_1806_);
v_val_2277_ = lean_ctor_get(v_a_2276_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_a_2276_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2279_ = v_a_2276_;
v_isShared_2280_ = v_isSharedCheck_2316_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_val_2277_);
lean_dec(v_a_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2316_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; 
lean_inc(v_mvarId_1807_);
v___x_2281_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2284_ = l_Lean_Meta_mkAbsurd(v_a_2282_, v_val_2277_, v___x_2283_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2285_, v___y_2272_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
lean_dec_ref_known(v___x_2286_, 1);
v___x_2287_ = lean_box(v___x_1817_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2287_);
v___x_2289_ = v___x_2279_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v___x_1842_);
v_a_1824_ = v___x_2290_;
goto v___jp_1823_;
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_del_object(v___x_2279_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_2292_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2286_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2286_);
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
lean_del_object(v___x_2279_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2300_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2284_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2284_);
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
lean_del_object(v___x_2279_);
lean_dec(v_val_2277_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2308_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2281_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2281_);
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
}
else
{
lean_object* v___x_2317_; 
lean_dec(v_a_2276_);
lean_inc_ref(v___x_1955_);
v___x_2317_ = l_Lean_Meta_matchNe_x3f(v___x_1955_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
if (lean_obj_tag(v_a_2318_) == 1)
{
lean_object* v_val_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2388_; 
v_val_2319_ = lean_ctor_get(v_a_2318_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_a_2318_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2321_ = v_a_2318_;
v_isShared_2322_ = v_isSharedCheck_2388_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_val_2319_);
lean_dec(v_a_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2388_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_snd_2323_; lean_object* v_fst_2324_; lean_object* v_snd_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2387_; 
v_snd_2323_ = lean_ctor_get(v_val_2319_, 1);
lean_inc(v_snd_2323_);
lean_dec(v_val_2319_);
v_fst_2324_ = lean_ctor_get(v_snd_2323_, 0);
v_snd_2325_ = lean_ctor_get(v_snd_2323_, 1);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_snd_2323_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2327_ = v_snd_2323_;
v_isShared_2328_ = v_isSharedCheck_2387_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_snd_2325_);
lean_inc(v_fst_2324_);
lean_dec(v_snd_2323_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2387_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; 
lean_inc(v_fst_2324_);
v___x_2329_ = l_Lean_Meta_isExprDefEq(v_fst_2324_, v_snd_2325_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = lean_unbox(v_a_2330_);
lean_dec(v_a_2330_);
if (v___x_2331_ == 0)
{
lean_del_object(v___x_2327_);
lean_dec(v_fst_2324_);
lean_del_object(v___x_2321_);
v___y_2225_ = v___y_2271_;
v___y_2226_ = v___y_2272_;
v___y_2227_ = v___y_2273_;
v___y_2228_ = v___y_2274_;
goto v___jp_2224_;
}
else
{
lean_object* v___x_2332_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec_ref(v_config_1806_);
lean_inc(v_mvarId_1807_);
v___x_2332_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = l_Lean_Meta_mkEqRefl(v_fst_2324_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2337_ = l_Lean_Meta_mkAbsurd(v_a_2333_, v_a_2335_, v___x_2336_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2338_, v___y_2272_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
lean_dec_ref_known(v___x_2339_, 1);
v___x_2340_ = lean_box(v___x_1817_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2340_);
v___x_2342_ = v___x_2321_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2344_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 1, v___x_1842_);
lean_ctor_set(v___x_2327_, 0, v___x_2342_);
v___x_2344_ = v___x_2327_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___x_1842_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
v_a_1824_ = v___x_2344_;
goto v___jp_1823_;
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_del_object(v___x_2327_);
lean_del_object(v___x_2321_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_2347_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2339_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2339_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_del_object(v___x_2327_);
lean_del_object(v___x_2321_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2355_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2337_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2337_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v_a_2333_);
lean_del_object(v___x_2327_);
lean_del_object(v___x_2321_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2363_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2334_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2334_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_del_object(v___x_2327_);
lean_dec(v_fst_2324_);
lean_del_object(v___x_2321_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2371_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2332_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2332_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_del_object(v___x_2327_);
lean_dec(v_fst_2324_);
lean_del_object(v___x_2321_);
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2379_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2329_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2329_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2318_);
v___y_2225_ = v___y_2271_;
v___y_2226_ = v___y_2272_;
v___y_2227_ = v___y_2273_;
v___y_2228_ = v___y_2274_;
goto v___jp_2224_;
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2389_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2317_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2317_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2397_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2275_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2275_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
else
{
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_1832_ = v___x_1883_;
goto v___jp_1831_;
}
v___jp_1843_:
{
lean_object* v___x_1848_; 
lean_inc(v_mvarId_1807_);
v___x_1848_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_1847_, v___y_1846_, v___y_1845_, v___y_1844_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_1851_ = l_Lean_Meta_mkNoConfusion(v_a_1849_, v___x_1850_, v___y_1847_, v___y_1846_, v___y_1845_, v___y_1844_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1853_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___x_1851_, 1);
v___x_1853_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_1852_, v___y_1846_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec_ref_known(v___x_1853_, 1);
v___x_1854_ = lean_box(v___x_1817_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1854_);
v___x_1856_ = v___x_1840_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v___x_1842_);
v_a_1824_ = v___x_1857_;
goto v___jp_1823_;
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_del_object(v___x_1840_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_1859_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1853_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1853_);
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
lean_del_object(v___x_1840_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_1867_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1851_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1851_);
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
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_1875_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1848_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1848_);
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
v___jp_1884_:
{
lean_object* v_searchFuel_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_searchFuel_1889_ = lean_ctor_get(v_config_1806_, 0);
v___x_1890_ = l_Lean_LocalDecl_fvarId(v_val_1838_);
lean_dec(v_val_1838_);
lean_inc(v_searchFuel_1889_);
lean_inc(v_mvarId_1807_);
v___x_1891_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1807_, v___x_1890_, v_searchFuel_1889_, v___y_1887_, v___y_1885_, v___y_1888_, v___y_1886_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; uint8_t v___x_1893_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v___x_1893_ = lean_unbox(v_a_1892_);
lean_dec(v_a_1892_);
if (v___x_1893_ == 0)
{
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_1832_ = v___x_1883_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v___x_1894_ = lean_box(v___x_1817_);
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___x_1842_);
v_a_1824_ = v___x_1896_;
goto v___jp_1823_;
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_1897_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1891_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1891_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
v___jp_1905_:
{
if (v___y_1910_ == 0)
{
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_1832_ = v___x_1883_;
goto v___jp_1831_;
}
else
{
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___y_1907_;
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1909_;
goto v___jp_1884_;
}
}
v___jp_1912_:
{
if (v___y_1914_ == 0)
{
v___y_1885_ = v___y_1913_;
v___y_1886_ = v___y_1915_;
v___y_1887_ = v___y_1916_;
v___y_1888_ = v___y_1917_;
goto v___jp_1884_;
}
else
{
v___y_1906_ = v___y_1913_;
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___y_1916_;
v___y_1909_ = v___y_1917_;
v___y_1910_ = v___x_1911_;
goto v___jp_1905_;
}
}
v___jp_1918_:
{
if (v___y_1924_ == 0)
{
v___y_1906_ = v___y_1919_;
v___y_1907_ = v___y_1921_;
v___y_1908_ = v___y_1922_;
v___y_1909_ = v___y_1923_;
v___y_1910_ = v___x_1911_;
goto v___jp_1905_;
}
else
{
v___y_1913_ = v___y_1919_;
v___y_1914_ = v___y_1920_;
v___y_1915_ = v___y_1921_;
v___y_1916_ = v___y_1922_;
v___y_1917_ = v___y_1923_;
goto v___jp_1912_;
}
}
v___jp_1925_:
{
uint8_t v_emptyType_1932_; 
v_emptyType_1932_ = lean_ctor_get_uint8(v_config_1806_, sizeof(void*)*1 + 1);
if (v_emptyType_1932_ == 0)
{
v___y_1919_ = v___y_1929_;
v___y_1920_ = v___y_1926_;
v___y_1921_ = v___y_1931_;
v___y_1922_ = v___y_1928_;
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___x_1911_;
goto v___jp_1918_;
}
else
{
if (v___y_1927_ == 0)
{
v___y_1913_ = v___y_1929_;
v___y_1914_ = v___y_1926_;
v___y_1915_ = v___y_1931_;
v___y_1916_ = v___y_1928_;
v___y_1917_ = v___y_1930_;
goto v___jp_1912_;
}
else
{
v___y_1919_ = v___y_1929_;
v___y_1920_ = v___y_1926_;
v___y_1921_ = v___y_1931_;
v___y_1922_ = v___y_1928_;
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___x_1911_;
goto v___jp_1918_;
}
}
}
v___jp_1933_:
{
if (v___y_1940_ == 0)
{
v___y_1926_ = v___y_1934_;
v___y_1927_ = v___y_1937_;
v___y_1928_ = v___y_1935_;
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___y_1939_;
v___y_1931_ = v___y_1938_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1941_; 
lean_inc(v_val_1838_);
lean_inc(v_mvarId_1807_);
v___x_1941_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1807_, v_val_1838_, v___y_1935_, v___y_1936_, v___y_1939_, v___y_1938_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; uint8_t v___x_1943_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1943_ = lean_unbox(v_a_1942_);
lean_dec(v_a_1942_);
if (v___x_1943_ == 0)
{
v___y_1926_ = v___y_1934_;
v___y_1927_ = v___y_1937_;
v___y_1928_ = v___y_1935_;
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___y_1939_;
v___y_1931_ = v___y_1938_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_dec(v_val_1838_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v___x_1944_ = lean_box(v___x_1817_);
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v___x_1842_);
v_a_1824_ = v___x_1946_;
goto v___jp_1823_;
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_1947_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1941_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1941_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
}
}
v___jp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_a_1824_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1825_);
v___x_1827_ = v___x_1821_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_snd_1819_);
v___x_1827_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
}
v___jp_1831_:
{
lean_object* v___x_1833_; size_t v___x_1834_; size_t v___x_1835_; 
v___x_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1830_);
lean_ctor_set(v___x_1833_, 1, v_a_1832_);
v___x_1834_ = ((size_t)1ULL);
v___x_1835_ = lean_usize_add(v_i_1810_, v___x_1834_);
v_i_1810_ = v___x_1835_;
v_b_1811_ = v___x_1833_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2471_, lean_object* v_mvarId_2472_, lean_object* v_as_2473_, lean_object* v_sz_2474_, lean_object* v_i_2475_, lean_object* v_b_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
size_t v_sz_boxed_2482_; size_t v_i_boxed_2483_; lean_object* v_res_2484_; 
v_sz_boxed_2482_ = lean_unbox_usize(v_sz_2474_);
lean_dec(v_sz_2474_);
v_i_boxed_2483_ = lean_unbox_usize(v_i_2475_);
lean_dec(v_i_2475_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2471_, v_mvarId_2472_, v_as_2473_, v_sz_boxed_2482_, v_i_boxed_2483_, v_b_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec_ref(v_as_2473_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2485_, lean_object* v_mvarId_2486_, lean_object* v_as_2487_, size_t v_sz_2488_, size_t v_i_2489_, lean_object* v_b_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v___x_2496_; 
v___x_2496_ = lean_usize_dec_lt(v_i_2489_, v_sz_2488_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; 
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_b_2490_);
return v___x_2497_;
}
else
{
lean_object* v_snd_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_3148_; 
v_snd_2498_ = lean_ctor_get(v_b_2490_, 1);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_b_2490_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v_b_2490_, 0);
lean_dec(v_unused_3149_);
v___x_2500_ = v_b_2490_;
v_isShared_2501_ = v_isSharedCheck_3148_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_snd_2498_);
lean_dec(v_b_2490_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_3148_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_a_2503_; lean_object* v___x_2509_; lean_object* v_a_2511_; lean_object* v_a_2516_; 
v___x_2509_ = lean_box(0);
v_a_2516_ = lean_array_uget(v_as_2487_, v_i_2489_);
if (lean_obj_tag(v_a_2516_) == 0)
{
lean_del_object(v___x_2500_);
v_a_2511_ = v_snd_2498_;
goto v___jp_2510_;
}
else
{
lean_object* v_val_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_3147_; 
v_val_2517_ = lean_ctor_get(v_a_2516_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_a_2516_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_2519_ = v_a_2516_;
v_isShared_2520_ = v_isSharedCheck_3147_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_val_2517_);
lean_dec(v_a_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_3147_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___x_2562_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; uint8_t v___y_2589_; uint8_t v___x_2590_; lean_object* v___y_2592_; lean_object* v___y_2593_; uint8_t v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2598_; lean_object* v___y_2599_; uint8_t v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; uint8_t v___y_2603_; uint8_t v___y_2605_; uint8_t v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; uint8_t v___y_2613_; uint8_t v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; uint8_t v___y_2619_; 
v___x_2521_ = lean_box(0);
v___x_2562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2590_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2517_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2634_; uint8_t v___y_2636_; uint8_t v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2645_; uint8_t v___y_2646_; uint8_t v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; uint8_t v___y_2652_; uint8_t v___y_2655_; uint8_t v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v_a_2661_; uint8_t v___y_2665_; uint8_t v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; uint8_t v___y_2709_; uint8_t v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; uint8_t v___y_2738_; uint8_t v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; uint8_t v___y_2744_; lean_object* v___y_2746_; uint8_t v___y_2747_; uint8_t v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; uint8_t v___y_2753_; uint8_t v___y_2756_; uint8_t v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint8_t v___y_2762_; uint8_t v___y_2775_; uint8_t v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; uint8_t v___y_2781_; uint8_t v___y_2783_; uint8_t v_isHEq_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; uint8_t v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; uint8_t v_isEq_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___x_3084_; 
v___x_2634_ = l_Lean_LocalDecl_type(v_val_2517_);
lean_inc_ref(v___x_2634_);
v___x_3084_ = l_Lean_Meta_matchNot_x3f(v___x_2634_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
lean_dec_ref_known(v___x_3084_, 1);
if (lean_obj_tag(v_a_3085_) == 1)
{
lean_object* v_val_3086_; lean_object* v___x_3087_; 
v_val_3086_ = lean_ctor_get(v_a_3085_, 0);
lean_inc(v_val_3086_);
lean_dec_ref_known(v_a_3085_, 1);
v___x_3087_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3086_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3087_, 1);
if (lean_obj_tag(v_a_3088_) == 1)
{
lean_object* v_val_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec_ref(v_config_2485_);
v_val_3089_ = lean_ctor_get(v_a_3088_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_a_3088_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3091_ = v_a_3088_;
v_isShared_3092_ = v_isSharedCheck_3130_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_val_3089_);
lean_dec(v_a_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3130_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; 
lean_inc(v_mvarId_2486_);
v___x_3093_ = l_Lean_MVarId_getType(v_mvarId_2486_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
v___x_3095_ = l_Lean_LocalDecl_toExpr(v_val_2517_);
v___x_3096_ = l_Lean_mkFVar(v_val_3089_);
v___x_3097_ = l_Lean_Expr_app___override(v___x_3095_, v___x_3096_);
v___x_3098_ = l_Lean_Meta_mkFalseElim(v_a_3094_, v___x_3097_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v___x_3100_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3099_);
lean_dec_ref_known(v___x_3098_, 1);
v___x_3100_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2486_, v_a_3099_, v___y_2492_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_dec_ref_known(v___x_3100_, 1);
v___x_3101_ = lean_box(v___x_2496_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3101_);
v___x_3103_ = v___x_3091_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3104_; 
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
lean_ctor_set(v___x_3104_, 1, v___x_2521_);
v_a_2503_ = v___x_3104_;
goto v___jp_2502_;
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_del_object(v___x_3091_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
v_a_3106_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3100_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3100_);
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
lean_del_object(v___x_3091_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_3114_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3098_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3098_);
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
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_del_object(v___x_3091_);
lean_dec(v_val_3089_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_3122_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3093_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3093_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
else
{
lean_dec(v_a_3088_);
v___y_2950_ = v___y_2491_;
v___y_2951_ = v___y_2492_;
v___y_2952_ = v___y_2493_;
v___y_2953_ = v___y_2494_;
goto v___jp_2949_;
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_3131_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3087_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3087_);
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
}
else
{
lean_dec(v_a_3085_);
v___y_2950_ = v___y_2491_;
v___y_2951_ = v___y_2492_;
v___y_2952_ = v___y_2493_;
v___y_2953_ = v___y_2494_;
goto v___jp_2949_;
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_3139_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3084_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3084_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
v___jp_2635_:
{
uint8_t v_genDiseq_2642_; 
v_genDiseq_2642_ = lean_ctor_get_uint8(v_config_2485_, sizeof(void*)*1 + 2);
if (v_genDiseq_2642_ == 0)
{
lean_dec_ref(v___x_2634_);
v___y_2613_ = v___y_2636_;
v___y_2614_ = v___y_2637_;
v___y_2615_ = v___y_2641_;
v___y_2616_ = v___y_2638_;
v___y_2617_ = v___y_2639_;
v___y_2618_ = v___y_2640_;
v___y_2619_ = v___x_2590_;
goto v___jp_2612_;
}
else
{
uint8_t v___x_2643_; 
v___x_2643_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2634_);
v___y_2613_ = v___y_2636_;
v___y_2614_ = v___y_2637_;
v___y_2615_ = v___y_2641_;
v___y_2616_ = v___y_2638_;
v___y_2617_ = v___y_2639_;
v___y_2618_ = v___y_2640_;
v___y_2619_ = v___x_2643_;
goto v___jp_2612_;
}
}
v___jp_2644_:
{
if (v___y_2652_ == 0)
{
lean_dec_ref(v___y_2645_);
v___y_2636_ = v___y_2646_;
v___y_2637_ = v___y_2647_;
v___y_2638_ = v___y_2649_;
v___y_2639_ = v___y_2648_;
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2651_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2653_; 
lean_dec_ref(v___x_2634_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___y_2645_);
return v___x_2653_;
}
}
v___jp_2654_:
{
uint8_t v___x_2662_; 
v___x_2662_ = l_Lean_Exception_isInterrupt(v_a_2661_);
if (v___x_2662_ == 0)
{
uint8_t v___x_2663_; 
lean_inc_ref(v_a_2661_);
v___x_2663_ = l_Lean_Exception_isRuntime(v_a_2661_);
v___y_2645_ = v_a_2661_;
v___y_2646_ = v___y_2655_;
v___y_2647_ = v___y_2656_;
v___y_2648_ = v___y_2658_;
v___y_2649_ = v___y_2657_;
v___y_2650_ = v___y_2659_;
v___y_2651_ = v___y_2660_;
v___y_2652_ = v___x_2663_;
goto v___jp_2644_;
}
else
{
v___y_2645_ = v_a_2661_;
v___y_2646_ = v___y_2655_;
v___y_2647_ = v___y_2656_;
v___y_2648_ = v___y_2658_;
v___y_2649_ = v___y_2657_;
v___y_2650_ = v___y_2659_;
v___y_2651_ = v___y_2660_;
v___y_2652_ = v___x_2662_;
goto v___jp_2644_;
}
}
v___jp_2664_:
{
if (lean_obj_tag(v___y_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_a_2673_ = lean_ctor_get(v___y_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___y_2672_, 1);
v___x_2674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2675_ = l_Lean_Expr_isConstOf(v_a_2673_, v___x_2674_);
lean_dec(v_a_2673_);
if (v___x_2675_ == 0)
{
lean_dec_ref(v___y_2669_);
v___y_2636_ = v___y_2665_;
v___y_2637_ = v___y_2666_;
v___y_2638_ = v___y_2668_;
v___y_2639_ = v___y_2667_;
v___y_2640_ = v___y_2670_;
v___y_2641_ = v___y_2671_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2676_; 
lean_inc_ref(v___y_2669_);
v___x_2676_ = l_Lean_Meta_mkEqRefl(v___y_2669_, v___y_2668_, v___y_2667_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
lean_inc(v_mvarId_2486_);
v___x_2678_ = l_Lean_MVarId_getType(v_mvarId_2486_, v___y_2668_, v___y_2667_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v_nargs_2680_; lean_object* v___x_2681_; lean_object* v_dummy_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v_nargs_2680_ = l_Lean_Expr_getAppNumArgs(v___y_2669_);
v___x_2681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2682_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2680_);
v___x_2683_ = lean_mk_array(v_nargs_2680_, v_dummy_2682_);
v___x_2684_ = lean_unsigned_to_nat(1u);
v___x_2685_ = lean_nat_sub(v_nargs_2680_, v___x_2684_);
lean_dec(v_nargs_2680_);
v___x_2686_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2669_, v___x_2683_, v___x_2685_);
v___x_2687_ = lean_array_push(v___x_2686_, v_a_2677_);
v___x_2688_ = l_Lean_mkAppN(v___x_2681_, v___x_2687_);
lean_dec_ref(v___x_2687_);
lean_inc(v_val_2517_);
v___x_2689_ = l_Lean_LocalDecl_toExpr(v_val_2517_);
v___x_2690_ = l_Lean_Meta_mkAbsurd(v_a_2679_, v___x_2689_, v___x_2688_, v___y_2668_, v___y_2667_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
lean_inc(v_mvarId_2486_);
v___x_2692_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2486_, v_a_2691_, v___y_2667_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v___x_2634_);
lean_dec(v_val_2517_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; 
v_unused_2702_ = lean_ctor_get(v___x_2692_, 0);
lean_dec(v_unused_2702_);
v___x_2694_ = v___x_2692_;
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
else
{
lean_dec(v___x_2692_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_box(v___x_2496_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set_tag(v___x_2694_, 1);
lean_ctor_set(v___x_2694_, 0, v___x_2696_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v___x_2521_);
v_a_2503_ = v___x_2699_;
goto v___jp_2502_;
}
}
}
else
{
lean_object* v_a_2703_; 
v_a_2703_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2692_, 1);
v___y_2655_ = v___y_2665_;
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2668_;
v___y_2658_ = v___y_2667_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2671_;
v_a_2661_ = v_a_2703_;
goto v___jp_2654_;
}
}
else
{
lean_object* v_a_2704_; 
v_a_2704_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2690_, 1);
v___y_2655_ = v___y_2665_;
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2668_;
v___y_2658_ = v___y_2667_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2671_;
v_a_2661_ = v_a_2704_;
goto v___jp_2654_;
}
}
else
{
lean_object* v_a_2705_; 
lean_dec(v_a_2677_);
lean_dec_ref(v___y_2669_);
v_a_2705_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2678_, 1);
v___y_2655_ = v___y_2665_;
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2668_;
v___y_2658_ = v___y_2667_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2671_;
v_a_2661_ = v_a_2705_;
goto v___jp_2654_;
}
}
else
{
lean_object* v_a_2706_; 
lean_dec_ref(v___y_2669_);
v_a_2706_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2676_, 1);
v___y_2655_ = v___y_2665_;
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2668_;
v___y_2658_ = v___y_2667_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2671_;
v_a_2661_ = v_a_2706_;
goto v___jp_2654_;
}
}
}
else
{
lean_object* v_a_2707_; 
lean_dec_ref(v___y_2669_);
v_a_2707_ = lean_ctor_get(v___y_2672_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___y_2672_, 1);
v___y_2655_ = v___y_2665_;
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2668_;
v___y_2658_ = v___y_2667_;
v___y_2659_ = v___y_2670_;
v___y_2660_ = v___y_2671_;
v_a_2661_ = v_a_2707_;
goto v___jp_2654_;
}
}
v___jp_2708_:
{
lean_object* v___x_2715_; 
lean_inc_ref(v___x_2634_);
v___x_2715_ = l_Lean_Meta_mkDecide(v___x_2634_, v___y_2712_, v___y_2711_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; uint8_t v_transparency_2718_; uint8_t v___x_2719_; uint8_t v___x_2720_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2717_ = l_Lean_Meta_Context_config(v___y_2712_);
v_transparency_2718_ = lean_ctor_get_uint8(v___x_2717_, 9);
lean_dec_ref(v___x_2717_);
v___x_2719_ = 1;
v___x_2720_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2718_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_object* v_keyedConfig_2721_; uint8_t v_trackZetaDelta_2722_; lean_object* v_zetaDeltaSet_2723_; lean_object* v_lctx_2724_; lean_object* v_localInstances_2725_; lean_object* v_defEqCtx_x3f_2726_; lean_object* v_synthPendingDepth_2727_; lean_object* v_customCanUnfoldPredicate_x3f_2728_; uint8_t v_univApprox_2729_; uint8_t v_inTypeClassResolution_2730_; uint8_t v_cacheInferType_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_keyedConfig_2721_ = lean_ctor_get(v___y_2712_, 0);
v_trackZetaDelta_2722_ = lean_ctor_get_uint8(v___y_2712_, sizeof(void*)*7);
v_zetaDeltaSet_2723_ = lean_ctor_get(v___y_2712_, 1);
v_lctx_2724_ = lean_ctor_get(v___y_2712_, 2);
v_localInstances_2725_ = lean_ctor_get(v___y_2712_, 3);
v_defEqCtx_x3f_2726_ = lean_ctor_get(v___y_2712_, 4);
v_synthPendingDepth_2727_ = lean_ctor_get(v___y_2712_, 5);
v_customCanUnfoldPredicate_x3f_2728_ = lean_ctor_get(v___y_2712_, 6);
v_univApprox_2729_ = lean_ctor_get_uint8(v___y_2712_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2730_ = lean_ctor_get_uint8(v___y_2712_, sizeof(void*)*7 + 2);
v_cacheInferType_2731_ = lean_ctor_get_uint8(v___y_2712_, sizeof(void*)*7 + 3);
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
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2713_);
lean_inc(v___y_2711_);
lean_inc(v_a_2716_);
v___x_2734_ = lean_whnf(v_a_2716_, v___x_2733_, v___y_2711_, v___y_2713_, v___y_2714_);
v___y_2665_ = v___y_2709_;
v___y_2666_ = v___y_2710_;
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v___y_2669_ = v_a_2716_;
v___y_2670_ = v___y_2713_;
v___y_2671_ = v___y_2714_;
v___y_2672_ = v___x_2734_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2735_; 
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2713_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2712_);
lean_inc(v_a_2716_);
v___x_2735_ = lean_whnf(v_a_2716_, v___y_2712_, v___y_2711_, v___y_2713_, v___y_2714_);
v___y_2665_ = v___y_2709_;
v___y_2666_ = v___y_2710_;
v___y_2667_ = v___y_2711_;
v___y_2668_ = v___y_2712_;
v___y_2669_ = v_a_2716_;
v___y_2670_ = v___y_2713_;
v___y_2671_ = v___y_2714_;
v___y_2672_ = v___x_2735_;
goto v___jp_2664_;
}
}
else
{
lean_object* v_a_2736_; 
v_a_2736_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2715_, 1);
v___y_2655_ = v___y_2709_;
v___y_2656_ = v___y_2710_;
v___y_2657_ = v___y_2712_;
v___y_2658_ = v___y_2711_;
v___y_2659_ = v___y_2713_;
v___y_2660_ = v___y_2714_;
v_a_2661_ = v_a_2736_;
goto v___jp_2654_;
}
}
v___jp_2737_:
{
if (v___y_2744_ == 0)
{
v___y_2636_ = v___y_2738_;
v___y_2637_ = v___y_2739_;
v___y_2638_ = v___y_2741_;
v___y_2639_ = v___y_2740_;
v___y_2640_ = v___y_2742_;
v___y_2641_ = v___y_2743_;
goto v___jp_2635_;
}
else
{
v___y_2709_ = v___y_2738_;
v___y_2710_ = v___y_2739_;
v___y_2711_ = v___y_2740_;
v___y_2712_ = v___y_2741_;
v___y_2713_ = v___y_2742_;
v___y_2714_ = v___y_2743_;
goto v___jp_2708_;
}
}
v___jp_2745_:
{
if (v___y_2753_ == 0)
{
lean_dec_ref(v___y_2746_);
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2748_;
v___y_2740_ = v___y_2750_;
v___y_2741_ = v___y_2749_;
v___y_2742_ = v___y_2751_;
v___y_2743_ = v___y_2752_;
v___y_2744_ = v___x_2590_;
goto v___jp_2737_;
}
else
{
uint8_t v___x_2754_; 
v___x_2754_ = l_Lean_Expr_hasFVar(v___y_2746_);
lean_dec_ref(v___y_2746_);
if (v___x_2754_ == 0)
{
v___y_2709_ = v___y_2747_;
v___y_2710_ = v___y_2748_;
v___y_2711_ = v___y_2750_;
v___y_2712_ = v___y_2749_;
v___y_2713_ = v___y_2751_;
v___y_2714_ = v___y_2752_;
goto v___jp_2708_;
}
else
{
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2748_;
v___y_2740_ = v___y_2750_;
v___y_2741_ = v___y_2749_;
v___y_2742_ = v___y_2751_;
v___y_2743_ = v___y_2752_;
v___y_2744_ = v___x_2590_;
goto v___jp_2737_;
}
}
}
v___jp_2755_:
{
lean_object* v___x_2763_; 
lean_inc_ref(v___x_2634_);
v___x_2763_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2634_, v___y_2759_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; uint8_t v___x_2765_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2765_ = l_Lean_Expr_hasMVar(v_a_2764_);
if (v___x_2765_ == 0)
{
v___y_2746_ = v_a_2764_;
v___y_2747_ = v___y_2756_;
v___y_2748_ = v___y_2757_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___y_2759_;
v___y_2751_ = v___y_2760_;
v___y_2752_ = v___y_2761_;
v___y_2753_ = v___y_2762_;
goto v___jp_2745_;
}
else
{
v___y_2746_ = v_a_2764_;
v___y_2747_ = v___y_2756_;
v___y_2748_ = v___y_2757_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___y_2759_;
v___y_2751_ = v___y_2760_;
v___y_2752_ = v___y_2761_;
v___y_2753_ = v___x_2590_;
goto v___jp_2745_;
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec_ref(v___x_2634_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2766_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2763_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2763_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
v___jp_2774_:
{
if (v___y_2781_ == 0)
{
v___y_2636_ = v___y_2775_;
v___y_2637_ = v___y_2776_;
v___y_2638_ = v___y_2778_;
v___y_2639_ = v___y_2777_;
v___y_2640_ = v___y_2779_;
v___y_2641_ = v___y_2780_;
goto v___jp_2635_;
}
else
{
v___y_2756_ = v___y_2775_;
v___y_2757_ = v___y_2776_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v___y_2777_;
v___y_2760_ = v___y_2779_;
v___y_2761_ = v___y_2780_;
v___y_2762_ = v___y_2781_;
goto v___jp_2755_;
}
}
v___jp_2782_:
{
uint8_t v_useDecide_2789_; 
v_useDecide_2789_ = lean_ctor_get_uint8(v_config_2485_, sizeof(void*)*1);
if (v_useDecide_2789_ == 0)
{
v___y_2775_ = v_isHEq_2784_;
v___y_2776_ = v___y_2783_;
v___y_2777_ = v___y_2786_;
v___y_2778_ = v___y_2785_;
v___y_2779_ = v___y_2787_;
v___y_2780_ = v___y_2788_;
v___y_2781_ = v___x_2590_;
goto v___jp_2774_;
}
else
{
uint8_t v___x_2790_; 
v___x_2790_ = l_Lean_Expr_hasFVar(v___x_2634_);
if (v___x_2790_ == 0)
{
v___y_2756_ = v_isHEq_2784_;
v___y_2757_ = v___y_2783_;
v___y_2758_ = v___y_2785_;
v___y_2759_ = v___y_2786_;
v___y_2760_ = v___y_2787_;
v___y_2761_ = v___y_2788_;
v___y_2762_ = v_useDecide_2789_;
goto v___jp_2755_;
}
else
{
v___y_2775_ = v_isHEq_2784_;
v___y_2776_ = v___y_2783_;
v___y_2777_ = v___y_2786_;
v___y_2778_ = v___y_2785_;
v___y_2779_ = v___y_2787_;
v___y_2780_ = v___y_2788_;
v___y_2781_ = v___x_2590_;
goto v___jp_2774_;
}
}
}
v___jp_2791_:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_Meta_isExprDefEq(v___y_2796_, v___y_2798_, v___y_2792_, v___y_2797_, v___y_2794_, v___y_2793_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; uint8_t v___x_2801_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = lean_unbox(v_a_2800_);
lean_dec(v_a_2800_);
if (v___x_2801_ == 0)
{
v___y_2783_ = v___y_2795_;
v_isHEq_2784_ = v___x_2496_;
v___y_2785_ = v___y_2792_;
v___y_2786_ = v___y_2797_;
v___y_2787_ = v___y_2794_;
v___y_2788_ = v___y_2793_;
goto v___jp_2782_;
}
else
{
lean_object* v___x_2802_; 
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_config_2485_);
lean_inc(v_mvarId_2486_);
v___x_2802_ = l_Lean_MVarId_getType(v_mvarId_2486_, v___y_2792_, v___y_2797_, v___y_2794_, v___y_2793_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = l_Lean_LocalDecl_toExpr(v_val_2517_);
v___x_2805_ = l_Lean_Meta_mkEqOfHEq(v___x_2804_, v___x_2496_, v___y_2792_, v___y_2797_, v___y_2794_, v___y_2793_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = l_Lean_Meta_mkNoConfusion(v_a_2803_, v_a_2806_, v___y_2792_, v___y_2797_, v___y_2794_, v___y_2793_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2486_, v_a_2808_, v___y_2797_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_dec_ref_known(v___x_2809_, 1);
v___x_2810_ = lean_box(v___x_2496_);
v___x_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v___x_2521_);
v_a_2503_ = v___x_2812_;
goto v___jp_2502_;
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
v_a_2813_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2809_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2809_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_2821_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2807_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2807_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_a_2803_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_2829_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2805_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2805_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_2837_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2802_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2802_);
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
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec_ref(v___x_2634_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2845_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2799_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2799_);
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
v___jp_2853_:
{
lean_object* v___x_2859_; 
lean_inc_ref(v___x_2634_);
v___x_2859_ = l_Lean_Meta_matchHEq_x3f(v___x_2634_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
if (lean_obj_tag(v_a_2860_) == 1)
{
lean_object* v_val_2861_; lean_object* v_snd_2862_; lean_object* v_snd_2863_; lean_object* v_fst_2864_; lean_object* v_fst_2865_; lean_object* v_fst_2866_; lean_object* v_snd_2867_; lean_object* v___x_2868_; 
v_val_2861_ = lean_ctor_get(v_a_2860_, 0);
lean_inc(v_val_2861_);
lean_dec_ref_known(v_a_2860_, 1);
v_snd_2862_ = lean_ctor_get(v_val_2861_, 1);
lean_inc(v_snd_2862_);
v_snd_2863_ = lean_ctor_get(v_snd_2862_, 1);
lean_inc(v_snd_2863_);
v_fst_2864_ = lean_ctor_get(v_val_2861_, 0);
lean_inc(v_fst_2864_);
lean_dec(v_val_2861_);
v_fst_2865_ = lean_ctor_get(v_snd_2862_, 0);
lean_inc(v_fst_2865_);
lean_dec(v_snd_2862_);
v_fst_2866_ = lean_ctor_get(v_snd_2863_, 0);
lean_inc(v_fst_2866_);
v_snd_2867_ = lean_ctor_get(v_snd_2863_, 1);
lean_inc(v_snd_2867_);
lean_dec(v_snd_2863_);
v___x_2868_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2865_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
if (lean_obj_tag(v_a_2869_) == 1)
{
lean_object* v_val_2870_; lean_object* v___x_2871_; 
v_val_2870_ = lean_ctor_get(v_a_2869_, 0);
lean_inc(v_val_2870_);
lean_dec_ref_known(v_a_2869_, 1);
v___x_2871_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2867_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
if (lean_obj_tag(v_a_2872_) == 1)
{
lean_object* v_toConstantVal_2873_; lean_object* v_val_2874_; lean_object* v_toConstantVal_2875_; lean_object* v_name_2876_; lean_object* v_name_2877_; uint8_t v___x_2878_; 
v_toConstantVal_2873_ = lean_ctor_get(v_val_2870_, 0);
lean_inc_ref(v_toConstantVal_2873_);
lean_dec(v_val_2870_);
v_val_2874_ = lean_ctor_get(v_a_2872_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v_a_2872_, 1);
v_toConstantVal_2875_ = lean_ctor_get(v_val_2874_, 0);
lean_inc_ref(v_toConstantVal_2875_);
lean_dec(v_val_2874_);
v_name_2876_ = lean_ctor_get(v_toConstantVal_2873_, 0);
lean_inc(v_name_2876_);
lean_dec_ref(v_toConstantVal_2873_);
v_name_2877_ = lean_ctor_get(v_toConstantVal_2875_, 0);
lean_inc(v_name_2877_);
lean_dec_ref(v_toConstantVal_2875_);
v___x_2878_ = lean_name_eq(v_name_2876_, v_name_2877_);
lean_dec(v_name_2877_);
lean_dec(v_name_2876_);
if (v___x_2878_ == 0)
{
v___y_2792_ = v___y_2855_;
v___y_2793_ = v___y_2858_;
v___y_2794_ = v___y_2857_;
v___y_2795_ = v_isEq_2854_;
v___y_2796_ = v_fst_2864_;
v___y_2797_ = v___y_2856_;
v___y_2798_ = v_fst_2866_;
goto v___jp_2791_;
}
else
{
if (v___x_2590_ == 0)
{
lean_dec(v_fst_2866_);
lean_dec(v_fst_2864_);
v___y_2783_ = v_isEq_2854_;
v_isHEq_2784_ = v___x_2496_;
v___y_2785_ = v___y_2855_;
v___y_2786_ = v___y_2856_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
goto v___jp_2782_;
}
else
{
v___y_2792_ = v___y_2855_;
v___y_2793_ = v___y_2858_;
v___y_2794_ = v___y_2857_;
v___y_2795_ = v_isEq_2854_;
v___y_2796_ = v_fst_2864_;
v___y_2797_ = v___y_2856_;
v___y_2798_ = v_fst_2866_;
goto v___jp_2791_;
}
}
}
else
{
lean_dec(v_a_2872_);
lean_dec(v_val_2870_);
lean_dec(v_fst_2866_);
lean_dec(v_fst_2864_);
v___y_2783_ = v_isEq_2854_;
v_isHEq_2784_ = v___x_2496_;
v___y_2785_ = v___y_2855_;
v___y_2786_ = v___y_2856_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
goto v___jp_2782_;
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_val_2870_);
lean_dec(v_fst_2866_);
lean_dec(v_fst_2864_);
lean_dec_ref(v___x_2634_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2879_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2871_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2871_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_dec(v_a_2869_);
lean_dec(v_snd_2867_);
lean_dec(v_fst_2866_);
lean_dec(v_fst_2864_);
v___y_2783_ = v_isEq_2854_;
v_isHEq_2784_ = v___x_2496_;
v___y_2785_ = v___y_2855_;
v___y_2786_ = v___y_2856_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
goto v___jp_2782_;
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_snd_2867_);
lean_dec(v_fst_2866_);
lean_dec(v_fst_2864_);
lean_dec_ref(v___x_2634_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2887_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2868_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2868_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_dec(v_a_2860_);
v___y_2783_ = v_isEq_2854_;
v_isHEq_2784_ = v___x_2590_;
v___y_2785_ = v___y_2855_;
v___y_2786_ = v___y_2856_;
v___y_2787_ = v___y_2857_;
v___y_2788_ = v___y_2858_;
goto v___jp_2782_;
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref(v___x_2634_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2895_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2859_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2859_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
v___jp_2903_:
{
lean_object* v___x_2908_; 
lean_inc_ref(v___x_2634_);
v___x_2908_ = l_Lean_Meta_matchEq_x3f(v___x_2634_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2908_, 1);
if (lean_obj_tag(v_a_2909_) == 1)
{
lean_object* v_val_2910_; lean_object* v_snd_2911_; lean_object* v_fst_2912_; lean_object* v_snd_2913_; lean_object* v___x_2914_; 
v_val_2910_ = lean_ctor_get(v_a_2909_, 0);
lean_inc(v_val_2910_);
lean_dec_ref_known(v_a_2909_, 1);
v_snd_2911_ = lean_ctor_get(v_val_2910_, 1);
lean_inc(v_snd_2911_);
lean_dec(v_val_2910_);
v_fst_2912_ = lean_ctor_get(v_snd_2911_, 0);
lean_inc(v_fst_2912_);
v_snd_2913_ = lean_ctor_get(v_snd_2911_, 1);
lean_inc(v_snd_2913_);
lean_dec(v_snd_2911_);
v___x_2914_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2912_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
if (lean_obj_tag(v_a_2915_) == 1)
{
lean_object* v_val_2916_; lean_object* v___x_2917_; 
v_val_2916_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_val_2916_);
lean_dec_ref_known(v_a_2915_, 1);
v___x_2917_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2913_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
if (lean_obj_tag(v_a_2918_) == 1)
{
lean_object* v_toConstantVal_2919_; lean_object* v_val_2920_; lean_object* v_toConstantVal_2921_; lean_object* v_name_2922_; lean_object* v_name_2923_; uint8_t v___x_2924_; 
v_toConstantVal_2919_ = lean_ctor_get(v_val_2916_, 0);
lean_inc_ref(v_toConstantVal_2919_);
lean_dec(v_val_2916_);
v_val_2920_ = lean_ctor_get(v_a_2918_, 0);
lean_inc(v_val_2920_);
lean_dec_ref_known(v_a_2918_, 1);
v_toConstantVal_2921_ = lean_ctor_get(v_val_2920_, 0);
lean_inc_ref(v_toConstantVal_2921_);
lean_dec(v_val_2920_);
v_name_2922_ = lean_ctor_get(v_toConstantVal_2919_, 0);
lean_inc(v_name_2922_);
lean_dec_ref(v_toConstantVal_2919_);
v_name_2923_ = lean_ctor_get(v_toConstantVal_2921_, 0);
lean_inc(v_name_2923_);
lean_dec_ref(v_toConstantVal_2921_);
v___x_2924_ = lean_name_eq(v_name_2922_, v_name_2923_);
lean_dec(v_name_2923_);
lean_dec(v_name_2922_);
if (v___x_2924_ == 0)
{
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_config_2485_);
v___y_2523_ = v___y_2906_;
v___y_2524_ = v___y_2907_;
v___y_2525_ = v___y_2905_;
v___y_2526_ = v___y_2904_;
goto v___jp_2522_;
}
else
{
if (v___x_2590_ == 0)
{
lean_del_object(v___x_2519_);
v_isEq_2854_ = v___x_2496_;
v___y_2855_ = v___y_2904_;
v___y_2856_ = v___y_2905_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
goto v___jp_2853_;
}
else
{
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_config_2485_);
v___y_2523_ = v___y_2906_;
v___y_2524_ = v___y_2907_;
v___y_2525_ = v___y_2905_;
v___y_2526_ = v___y_2904_;
goto v___jp_2522_;
}
}
}
else
{
lean_dec(v_a_2918_);
lean_dec(v_val_2916_);
lean_del_object(v___x_2519_);
v_isEq_2854_ = v___x_2496_;
v___y_2855_ = v___y_2904_;
v___y_2856_ = v___y_2905_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
goto v___jp_2853_;
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_val_2916_);
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2925_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2917_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2917_);
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
else
{
lean_dec(v_a_2915_);
lean_dec(v_snd_2913_);
lean_del_object(v___x_2519_);
v_isEq_2854_ = v___x_2496_;
v___y_2855_ = v___y_2904_;
v___y_2856_ = v___y_2905_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
goto v___jp_2853_;
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v_snd_2913_);
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2933_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2914_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2914_);
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
else
{
lean_dec(v_a_2909_);
lean_del_object(v___x_2519_);
v_isEq_2854_ = v___x_2590_;
v___y_2855_ = v___y_2904_;
v___y_2856_ = v___y_2905_;
v___y_2857_ = v___y_2906_;
v___y_2858_ = v___y_2907_;
goto v___jp_2853_;
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2941_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2908_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2908_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
v___jp_2949_:
{
lean_object* v___x_2954_; 
lean_inc_ref(v___x_2634_);
v___x_2954_ = l_Lean_refutableHasNotBit_x3f(v___x_2634_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
if (lean_obj_tag(v_a_2955_) == 1)
{
lean_object* v_val_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec_ref(v_config_2485_);
v_val_2956_ = lean_ctor_get(v_a_2955_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_a_2955_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2958_ = v_a_2955_;
v_isShared_2959_ = v_isSharedCheck_2995_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_val_2956_);
lean_dec(v_a_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2995_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; 
lean_inc(v_mvarId_2486_);
v___x_2960_ = l_Lean_MVarId_getType(v_mvarId_2486_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = l_Lean_LocalDecl_toExpr(v_val_2517_);
v___x_2963_ = l_Lean_Meta_mkAbsurd(v_a_2961_, v_val_2956_, v___x_2962_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2486_, v_a_2964_, v___y_2951_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v___x_2966_; lean_object* v___x_2968_; 
lean_dec_ref_known(v___x_2965_, 1);
v___x_2966_ = lean_box(v___x_2496_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2966_);
v___x_2968_ = v___x_2958_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
lean_ctor_set(v___x_2969_, 1, v___x_2521_);
v_a_2503_ = v___x_2969_;
goto v___jp_2502_;
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_del_object(v___x_2958_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
v_a_2971_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2965_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2965_);
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
lean_del_object(v___x_2958_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_2979_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2963_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2963_);
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
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_del_object(v___x_2958_);
lean_dec(v_val_2956_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_2987_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2960_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2960_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
}
else
{
lean_object* v___x_2996_; 
lean_dec(v_a_2955_);
lean_inc_ref(v___x_2634_);
v___x_2996_ = l_Lean_Meta_matchNe_x3f(v___x_2634_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
if (lean_obj_tag(v_a_2997_) == 1)
{
lean_object* v_val_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3067_; 
v_val_2998_ = lean_ctor_get(v_a_2997_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_a_2997_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3000_ = v_a_2997_;
v_isShared_3001_ = v_isSharedCheck_3067_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_val_2998_);
lean_dec(v_a_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3067_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v_snd_3002_; lean_object* v_fst_3003_; lean_object* v_snd_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3066_; 
v_snd_3002_ = lean_ctor_get(v_val_2998_, 1);
lean_inc(v_snd_3002_);
lean_dec(v_val_2998_);
v_fst_3003_ = lean_ctor_get(v_snd_3002_, 0);
v_snd_3004_ = lean_ctor_get(v_snd_3002_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_snd_3002_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3006_ = v_snd_3002_;
v_isShared_3007_ = v_isSharedCheck_3066_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_snd_3004_);
lean_inc(v_fst_3003_);
lean_dec(v_snd_3002_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3066_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; 
lean_inc(v_fst_3003_);
v___x_3008_ = l_Lean_Meta_isExprDefEq(v_fst_3003_, v_snd_3004_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; uint8_t v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = lean_unbox(v_a_3009_);
lean_dec(v_a_3009_);
if (v___x_3010_ == 0)
{
lean_del_object(v___x_3006_);
lean_dec(v_fst_3003_);
lean_del_object(v___x_3000_);
v___y_2904_ = v___y_2950_;
v___y_2905_ = v___y_2951_;
v___y_2906_ = v___y_2952_;
v___y_2907_ = v___y_2953_;
goto v___jp_2903_;
}
else
{
lean_object* v___x_3011_; 
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec_ref(v_config_2485_);
lean_inc(v_mvarId_2486_);
v___x_3011_ = l_Lean_MVarId_getType(v_mvarId_2486_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = l_Lean_Meta_mkEqRefl(v_fst_3003_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v___x_3015_ = l_Lean_LocalDecl_toExpr(v_val_2517_);
v___x_3016_ = l_Lean_Meta_mkAbsurd(v_a_3012_, v_a_3014_, v___x_3015_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2486_, v_a_3017_, v___y_2951_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
lean_dec_ref_known(v___x_3018_, 1);
v___x_3019_ = lean_box(v___x_2496_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3019_);
v___x_3021_ = v___x_3000_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3023_; 
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 1, v___x_2521_);
lean_ctor_set(v___x_3006_, 0, v___x_3021_);
v___x_3023_ = v___x_3006_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_2521_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
v_a_2503_ = v___x_3023_;
goto v___jp_2502_;
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_del_object(v___x_3006_);
lean_del_object(v___x_3000_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
v_a_3026_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3018_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3018_);
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
lean_del_object(v___x_3006_);
lean_del_object(v___x_3000_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_3034_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3016_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3016_);
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
lean_dec(v_a_3012_);
lean_del_object(v___x_3006_);
lean_del_object(v___x_3000_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_3042_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3013_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3013_);
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
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_del_object(v___x_3006_);
lean_dec(v_fst_3003_);
lean_del_object(v___x_3000_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_3050_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3011_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3011_);
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
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_del_object(v___x_3006_);
lean_dec(v_fst_3003_);
lean_del_object(v___x_3000_);
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_3058_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3008_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3008_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2997_);
v___y_2904_ = v___y_2950_;
v___y_2905_ = v___y_2951_;
v___y_2906_ = v___y_2952_;
v___y_2907_ = v___y_2953_;
goto v___jp_2903_;
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_3068_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_2996_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_2996_);
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
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec_ref(v___x_2634_);
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_3076_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_2954_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_2954_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
}
else
{
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
v_a_2511_ = v___x_2562_;
goto v___jp_2510_;
}
v___jp_2522_:
{
lean_object* v___x_2527_; 
lean_inc(v_mvarId_2486_);
v___x_2527_ = l_Lean_MVarId_getType(v_mvarId_2486_, v___y_2526_, v___y_2525_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = l_Lean_LocalDecl_toExpr(v_val_2517_);
v___x_2530_ = l_Lean_Meta_mkNoConfusion(v_a_2528_, v___x_2529_, v___y_2526_, v___y_2525_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2486_, v_a_2531_, v___y_2525_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2535_; 
lean_dec_ref_known(v___x_2532_, 1);
v___x_2533_ = lean_box(v___x_2496_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v___x_2533_);
v___x_2535_ = v___x_2519_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v___x_2521_);
v_a_2503_ = v___x_2536_;
goto v___jp_2502_;
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_del_object(v___x_2519_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
v_a_2538_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2532_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2532_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_del_object(v___x_2519_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_2546_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2530_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2530_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_del_object(v___x_2519_);
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
v_a_2554_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2527_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2527_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
v___jp_2563_:
{
lean_object* v_searchFuel_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_searchFuel_2568_ = lean_ctor_get(v_config_2485_, 0);
v___x_2569_ = l_Lean_LocalDecl_fvarId(v_val_2517_);
lean_dec(v_val_2517_);
lean_inc(v_searchFuel_2568_);
lean_inc(v_mvarId_2486_);
v___x_2570_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2486_, v___x_2569_, v_searchFuel_2568_, v___y_2565_, v___y_2564_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; uint8_t v___x_2572_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2572_ = lean_unbox(v_a_2571_);
lean_dec(v_a_2571_);
if (v___x_2572_ == 0)
{
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
v_a_2511_ = v___x_2562_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v___x_2573_ = lean_box(v___x_2496_);
v___x_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___x_2521_);
v_a_2503_ = v___x_2575_;
goto v___jp_2502_;
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2576_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2570_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2570_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
v___jp_2584_:
{
if (v___y_2589_ == 0)
{
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
v_a_2511_ = v___x_2562_;
goto v___jp_2510_;
}
else
{
v___y_2564_ = v___y_2585_;
v___y_2565_ = v___y_2586_;
v___y_2566_ = v___y_2587_;
v___y_2567_ = v___y_2588_;
goto v___jp_2563_;
}
}
v___jp_2591_:
{
if (v___y_2594_ == 0)
{
v___y_2564_ = v___y_2592_;
v___y_2565_ = v___y_2593_;
v___y_2566_ = v___y_2595_;
v___y_2567_ = v___y_2596_;
goto v___jp_2563_;
}
else
{
v___y_2585_ = v___y_2592_;
v___y_2586_ = v___y_2593_;
v___y_2587_ = v___y_2595_;
v___y_2588_ = v___y_2596_;
v___y_2589_ = v___x_2590_;
goto v___jp_2584_;
}
}
v___jp_2597_:
{
if (v___y_2603_ == 0)
{
v___y_2585_ = v___y_2598_;
v___y_2586_ = v___y_2599_;
v___y_2587_ = v___y_2601_;
v___y_2588_ = v___y_2602_;
v___y_2589_ = v___x_2590_;
goto v___jp_2584_;
}
else
{
v___y_2592_ = v___y_2598_;
v___y_2593_ = v___y_2599_;
v___y_2594_ = v___y_2600_;
v___y_2595_ = v___y_2601_;
v___y_2596_ = v___y_2602_;
goto v___jp_2591_;
}
}
v___jp_2604_:
{
uint8_t v_emptyType_2611_; 
v_emptyType_2611_ = lean_ctor_get_uint8(v_config_2485_, sizeof(void*)*1 + 1);
if (v_emptyType_2611_ == 0)
{
v___y_2598_ = v___y_2608_;
v___y_2599_ = v___y_2607_;
v___y_2600_ = v___y_2605_;
v___y_2601_ = v___y_2609_;
v___y_2602_ = v___y_2610_;
v___y_2603_ = v___x_2590_;
goto v___jp_2597_;
}
else
{
if (v___y_2606_ == 0)
{
v___y_2592_ = v___y_2608_;
v___y_2593_ = v___y_2607_;
v___y_2594_ = v___y_2605_;
v___y_2595_ = v___y_2609_;
v___y_2596_ = v___y_2610_;
goto v___jp_2591_;
}
else
{
v___y_2598_ = v___y_2608_;
v___y_2599_ = v___y_2607_;
v___y_2600_ = v___y_2605_;
v___y_2601_ = v___y_2609_;
v___y_2602_ = v___y_2610_;
v___y_2603_ = v___x_2590_;
goto v___jp_2597_;
}
}
}
v___jp_2612_:
{
if (v___y_2619_ == 0)
{
v___y_2605_ = v___y_2613_;
v___y_2606_ = v___y_2614_;
v___y_2607_ = v___y_2616_;
v___y_2608_ = v___y_2617_;
v___y_2609_ = v___y_2618_;
v___y_2610_ = v___y_2615_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2620_; 
lean_inc(v_val_2517_);
lean_inc(v_mvarId_2486_);
v___x_2620_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2486_, v_val_2517_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2615_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; uint8_t v___x_2622_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = lean_unbox(v_a_2621_);
lean_dec(v_a_2621_);
if (v___x_2622_ == 0)
{
v___y_2605_ = v___y_2613_;
v___y_2606_ = v___y_2614_;
v___y_2607_ = v___y_2616_;
v___y_2608_ = v___y_2617_;
v___y_2609_ = v___y_2618_;
v___y_2610_ = v___y_2615_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_dec(v_val_2517_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v___x_2623_ = lean_box(v___x_2496_);
v___x_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
lean_ctor_set(v___x_2625_, 1, v___x_2521_);
v_a_2503_ = v___x_2625_;
goto v___jp_2502_;
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v_val_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_snd_2498_);
lean_dec(v_mvarId_2486_);
lean_dec_ref(v_config_2485_);
v_a_2626_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2620_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2620_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
}
}
v___jp_2502_:
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_a_2503_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2504_);
v___x_2506_ = v___x_2500_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_snd_2498_);
v___x_2506_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
}
v___jp_2510_:
{
lean_object* v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2509_);
lean_ctor_set(v___x_2512_, 1, v_a_2511_);
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_add(v_i_2489_, v___x_2513_);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2485_, v_mvarId_2486_, v_as_2487_, v_sz_2488_, v___x_2514_, v___x_2512_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
return v___x_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3150_, lean_object* v_mvarId_3151_, lean_object* v_as_3152_, lean_object* v_sz_3153_, lean_object* v_i_3154_, lean_object* v_b_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
size_t v_sz_boxed_3161_; size_t v_i_boxed_3162_; lean_object* v_res_3163_; 
v_sz_boxed_3161_ = lean_unbox_usize(v_sz_3153_);
lean_dec(v_sz_3153_);
v_i_boxed_3162_ = lean_unbox_usize(v_i_3154_);
lean_dec(v_i_3154_);
v_res_3163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3150_, v_mvarId_3151_, v_as_3152_, v_sz_boxed_3161_, v_i_boxed_3162_, v_b_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v_as_3152_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3167_, lean_object* v_mvarId_3168_, lean_object* v_as_3169_, size_t v_sz_3170_, size_t v_i_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
uint8_t v___x_3178_; 
v___x_3178_ = lean_usize_dec_lt(v_i_3171_, v_sz_3170_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; 
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v___x_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3179_, 0, v_b_3172_);
return v___x_3179_;
}
else
{
lean_object* v_snd_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3850_; 
v_snd_3180_ = lean_ctor_get(v_b_3172_, 1);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_b_3172_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v_b_3172_, 0);
lean_dec(v_unused_3851_);
v___x_3182_ = v_b_3172_;
v_isShared_3183_ = v_isSharedCheck_3850_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_snd_3180_);
lean_dec(v_b_3172_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3850_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v_a_3185_; lean_object* v___x_3191_; lean_object* v_a_3193_; lean_object* v_a_3198_; 
v___x_3191_ = lean_box(0);
v_a_3198_ = lean_array_uget(v_as_3169_, v_i_3171_);
if (lean_obj_tag(v_a_3198_) == 0)
{
lean_del_object(v___x_3182_);
v_a_3193_ = v_snd_3180_;
goto v___jp_3192_;
}
else
{
lean_object* v_val_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3849_; 
v_val_3199_ = lean_ctor_get(v_a_3198_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v_a_3198_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3201_ = v_a_3198_;
v_isShared_3202_ = v_isSharedCheck_3849_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_val_3199_);
lean_dec(v_a_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3849_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___x_3245_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; uint8_t v___y_3273_; uint8_t v___x_3274_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; uint8_t v___y_3280_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; uint8_t v___y_3286_; uint8_t v___y_3287_; uint8_t v___y_3289_; uint8_t v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3297_; uint8_t v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; uint8_t v___y_3302_; uint8_t v___y_3303_; 
v___x_3203_ = lean_box(0);
v___x_3245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3274_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3199_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3319_; uint8_t v___y_3321_; uint8_t v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3330_; lean_object* v___y_3331_; uint8_t v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; uint8_t v___y_3335_; lean_object* v___y_3336_; uint8_t v___y_3337_; lean_object* v___y_3340_; lean_object* v___y_3341_; uint8_t v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; uint8_t v___y_3345_; lean_object* v_a_3346_; lean_object* v___y_3350_; lean_object* v___y_3351_; uint8_t v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; uint8_t v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3401_; lean_object* v___y_3402_; uint8_t v___y_3403_; lean_object* v___y_3404_; uint8_t v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3430_; lean_object* v___y_3431_; uint8_t v___y_3432_; lean_object* v___y_3433_; uint8_t v___y_3434_; lean_object* v___y_3435_; uint8_t v___y_3436_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; uint8_t v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; uint8_t v___y_3444_; uint8_t v___y_3445_; lean_object* v___y_3448_; lean_object* v___y_3449_; uint8_t v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; uint8_t v___y_3453_; uint8_t v___y_3454_; lean_object* v___y_3467_; lean_object* v___y_3468_; uint8_t v___y_3469_; lean_object* v___y_3470_; uint8_t v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; uint8_t v___y_3475_; uint8_t v_isHEq_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; uint8_t v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; uint8_t v_isEq_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___x_3779_; 
v___x_3319_ = l_Lean_LocalDecl_type(v_val_3199_);
lean_inc_ref(v___x_3319_);
v___x_3779_ = l_Lean_Meta_matchNot_x3f(v___x_3319_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
if (lean_obj_tag(v_a_3780_) == 1)
{
lean_object* v_val_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3840_; 
v_val_3781_ = lean_ctor_get(v_a_3780_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v_a_3780_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3783_ = v_a_3780_;
v_isShared_3784_ = v_isSharedCheck_3840_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_val_3781_);
lean_dec(v_a_3780_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3840_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3781_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
if (lean_obj_tag(v_a_3786_) == 1)
{
lean_object* v_val_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3831_; 
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec_ref(v_config_3167_);
v_val_3787_ = lean_ctor_get(v_a_3786_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_a_3786_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3789_ = v_a_3786_;
v_isShared_3790_ = v_isSharedCheck_3831_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_val_3787_);
lean_dec(v_a_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3831_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3791_; 
lean_inc(v_mvarId_3168_);
v___x_3791_ = l_Lean_MVarId_getType(v_mvarId_3168_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = l_Lean_LocalDecl_toExpr(v_val_3199_);
v___x_3794_ = l_Lean_mkFVar(v_val_3787_);
v___x_3795_ = l_Lean_Expr_app___override(v___x_3793_, v___x_3794_);
v___x_3796_ = l_Lean_Meta_mkFalseElim(v_a_3792_, v___x_3795_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
v___x_3798_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3168_, v_a_3797_, v___y_3174_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v___x_3799_; lean_object* v___x_3801_; 
lean_dec_ref_known(v___x_3798_, 1);
v___x_3799_ = lean_box(v___x_3178_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3799_);
v___x_3801_ = v___x_3789_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3802_; lean_object* v___x_3804_; 
v___x_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set(v___x_3802_, 1, v___x_3203_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set_tag(v___x_3783_, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3802_);
v___x_3804_ = v___x_3783_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
v_a_3185_ = v___x_3804_;
goto v___jp_3184_;
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_del_object(v___x_3789_);
lean_del_object(v___x_3783_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
v_a_3807_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3798_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3798_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_del_object(v___x_3789_);
lean_del_object(v___x_3783_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3815_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3796_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3796_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_del_object(v___x_3789_);
lean_dec(v_val_3787_);
lean_del_object(v___x_3783_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3823_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3791_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3791_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
else
{
lean_dec(v_a_3786_);
lean_del_object(v___x_3783_);
v___y_3643_ = v___y_3173_;
v___y_3644_ = v___y_3174_;
v___y_3645_ = v___y_3175_;
v___y_3646_ = v___y_3176_;
goto v___jp_3642_;
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_del_object(v___x_3783_);
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3832_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3785_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3785_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
else
{
lean_dec(v_a_3780_);
v___y_3643_ = v___y_3173_;
v___y_3644_ = v___y_3174_;
v___y_3645_ = v___y_3175_;
v___y_3646_ = v___y_3176_;
goto v___jp_3642_;
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3841_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3779_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3779_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
v___jp_3320_:
{
uint8_t v_genDiseq_3327_; 
v_genDiseq_3327_ = lean_ctor_get_uint8(v_config_3167_, sizeof(void*)*1 + 2);
if (v_genDiseq_3327_ == 0)
{
lean_dec_ref(v___x_3319_);
v___y_3297_ = v___y_3325_;
v___y_3298_ = v___y_3321_;
v___y_3299_ = v___y_3326_;
v___y_3300_ = v___y_3324_;
v___y_3301_ = v___y_3323_;
v___y_3302_ = v___y_3322_;
v___y_3303_ = v___x_3274_;
goto v___jp_3296_;
}
else
{
uint8_t v___x_3328_; 
v___x_3328_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3319_);
v___y_3297_ = v___y_3325_;
v___y_3298_ = v___y_3321_;
v___y_3299_ = v___y_3326_;
v___y_3300_ = v___y_3324_;
v___y_3301_ = v___y_3323_;
v___y_3302_ = v___y_3322_;
v___y_3303_ = v___x_3328_;
goto v___jp_3296_;
}
}
v___jp_3329_:
{
if (v___y_3337_ == 0)
{
lean_dec_ref(v___y_3334_);
v___y_3321_ = v___y_3332_;
v___y_3322_ = v___y_3335_;
v___y_3323_ = v___y_3333_;
v___y_3324_ = v___y_3331_;
v___y_3325_ = v___y_3336_;
v___y_3326_ = v___y_3330_;
goto v___jp_3320_;
}
else
{
lean_object* v___x_3338_; 
lean_dec_ref(v___x_3319_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___y_3334_);
return v___x_3338_;
}
}
v___jp_3339_:
{
uint8_t v___x_3347_; 
v___x_3347_ = l_Lean_Exception_isInterrupt(v_a_3346_);
if (v___x_3347_ == 0)
{
uint8_t v___x_3348_; 
lean_inc_ref(v_a_3346_);
v___x_3348_ = l_Lean_Exception_isRuntime(v_a_3346_);
v___y_3330_ = v___y_3340_;
v___y_3331_ = v___y_3341_;
v___y_3332_ = v___y_3342_;
v___y_3333_ = v___y_3343_;
v___y_3334_ = v_a_3346_;
v___y_3335_ = v___y_3345_;
v___y_3336_ = v___y_3344_;
v___y_3337_ = v___x_3348_;
goto v___jp_3329_;
}
else
{
v___y_3330_ = v___y_3340_;
v___y_3331_ = v___y_3341_;
v___y_3332_ = v___y_3342_;
v___y_3333_ = v___y_3343_;
v___y_3334_ = v_a_3346_;
v___y_3335_ = v___y_3345_;
v___y_3336_ = v___y_3344_;
v___y_3337_ = v___x_3347_;
goto v___jp_3329_;
}
}
v___jp_3349_:
{
if (lean_obj_tag(v___y_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v_a_3358_ = lean_ctor_get(v___y_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___y_3357_, 1);
v___x_3359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3360_ = l_Lean_Expr_isConstOf(v_a_3358_, v___x_3359_);
lean_dec(v_a_3358_);
if (v___x_3360_ == 0)
{
lean_dec_ref(v___y_3354_);
v___y_3321_ = v___y_3352_;
v___y_3322_ = v___y_3355_;
v___y_3323_ = v___y_3353_;
v___y_3324_ = v___y_3351_;
v___y_3325_ = v___y_3356_;
v___y_3326_ = v___y_3350_;
goto v___jp_3320_;
}
else
{
lean_object* v___x_3361_; 
lean_inc_ref(v___y_3354_);
v___x_3361_ = l_Lean_Meta_mkEqRefl(v___y_3354_, v___y_3353_, v___y_3351_, v___y_3356_, v___y_3350_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
lean_inc(v_mvarId_3168_);
v___x_3363_ = l_Lean_MVarId_getType(v_mvarId_3168_, v___y_3353_, v___y_3351_, v___y_3356_, v___y_3350_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v_nargs_3365_; lean_object* v___x_3366_; lean_object* v_dummy_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v_nargs_3365_ = l_Lean_Expr_getAppNumArgs(v___y_3354_);
v___x_3366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3367_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_3365_);
v___x_3368_ = lean_mk_array(v_nargs_3365_, v_dummy_3367_);
v___x_3369_ = lean_unsigned_to_nat(1u);
v___x_3370_ = lean_nat_sub(v_nargs_3365_, v___x_3369_);
lean_dec(v_nargs_3365_);
v___x_3371_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3354_, v___x_3368_, v___x_3370_);
v___x_3372_ = lean_array_push(v___x_3371_, v_a_3362_);
v___x_3373_ = l_Lean_mkAppN(v___x_3366_, v___x_3372_);
lean_dec_ref(v___x_3372_);
lean_inc(v_val_3199_);
v___x_3374_ = l_Lean_LocalDecl_toExpr(v_val_3199_);
v___x_3375_ = l_Lean_Meta_mkAbsurd(v_a_3364_, v___x_3374_, v___x_3373_, v___y_3353_, v___y_3351_, v___y_3356_, v___y_3350_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3395_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3395_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3395_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; 
lean_inc(v_mvarId_3168_);
v___x_3380_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3168_, v_a_3376_, v___y_3351_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v___x_3319_);
lean_dec(v_val_3199_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v___x_3380_, 0);
lean_dec(v_unused_3393_);
v___x_3382_ = v___x_3380_;
v_isShared_3383_ = v_isSharedCheck_3392_;
goto v_resetjp_3381_;
}
else
{
lean_dec(v___x_3380_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3392_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3386_; 
v___x_3384_ = lean_box(v___x_3178_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set_tag(v___x_3382_, 1);
lean_ctor_set(v___x_3382_, 0, v___x_3384_);
v___x_3386_ = v___x_3382_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v___x_3203_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3387_);
v___x_3389_ = v___x_3378_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
v_a_3185_ = v___x_3389_;
goto v___jp_3184_;
}
}
}
}
else
{
lean_object* v_a_3394_; 
lean_del_object(v___x_3378_);
v_a_3394_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3380_, 1);
v___y_3340_ = v___y_3350_;
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3356_;
v___y_3345_ = v___y_3355_;
v_a_3346_ = v_a_3394_;
goto v___jp_3339_;
}
}
}
else
{
lean_object* v_a_3396_; 
v_a_3396_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3375_, 1);
v___y_3340_ = v___y_3350_;
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3356_;
v___y_3345_ = v___y_3355_;
v_a_3346_ = v_a_3396_;
goto v___jp_3339_;
}
}
else
{
lean_object* v_a_3397_; 
lean_dec(v_a_3362_);
lean_dec_ref(v___y_3354_);
v_a_3397_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3363_, 1);
v___y_3340_ = v___y_3350_;
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3356_;
v___y_3345_ = v___y_3355_;
v_a_3346_ = v_a_3397_;
goto v___jp_3339_;
}
}
else
{
lean_object* v_a_3398_; 
lean_dec_ref(v___y_3354_);
v_a_3398_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3361_, 1);
v___y_3340_ = v___y_3350_;
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3356_;
v___y_3345_ = v___y_3355_;
v_a_3346_ = v_a_3398_;
goto v___jp_3339_;
}
}
}
else
{
lean_object* v_a_3399_; 
lean_dec_ref(v___y_3354_);
v_a_3399_ = lean_ctor_get(v___y_3357_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___y_3357_, 1);
v___y_3340_ = v___y_3350_;
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3356_;
v___y_3345_ = v___y_3355_;
v_a_3346_ = v_a_3399_;
goto v___jp_3339_;
}
}
v___jp_3400_:
{
lean_object* v___x_3407_; 
lean_inc_ref(v___x_3319_);
v___x_3407_ = l_Lean_Meta_mkDecide(v___x_3319_, v___y_3404_, v___y_3402_, v___y_3406_, v___y_3401_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; uint8_t v_transparency_3410_; uint8_t v___x_3411_; uint8_t v___x_3412_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
v___x_3409_ = l_Lean_Meta_Context_config(v___y_3404_);
v_transparency_3410_ = lean_ctor_get_uint8(v___x_3409_, 9);
lean_dec_ref(v___x_3409_);
v___x_3411_ = 1;
v___x_3412_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_object* v_keyedConfig_3413_; uint8_t v_trackZetaDelta_3414_; lean_object* v_zetaDeltaSet_3415_; lean_object* v_lctx_3416_; lean_object* v_localInstances_3417_; lean_object* v_defEqCtx_x3f_3418_; lean_object* v_synthPendingDepth_3419_; lean_object* v_customCanUnfoldPredicate_x3f_3420_; uint8_t v_univApprox_3421_; uint8_t v_inTypeClassResolution_3422_; uint8_t v_cacheInferType_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_keyedConfig_3413_ = lean_ctor_get(v___y_3404_, 0);
v_trackZetaDelta_3414_ = lean_ctor_get_uint8(v___y_3404_, sizeof(void*)*7);
v_zetaDeltaSet_3415_ = lean_ctor_get(v___y_3404_, 1);
v_lctx_3416_ = lean_ctor_get(v___y_3404_, 2);
v_localInstances_3417_ = lean_ctor_get(v___y_3404_, 3);
v_defEqCtx_x3f_3418_ = lean_ctor_get(v___y_3404_, 4);
v_synthPendingDepth_3419_ = lean_ctor_get(v___y_3404_, 5);
v_customCanUnfoldPredicate_x3f_3420_ = lean_ctor_get(v___y_3404_, 6);
v_univApprox_3421_ = lean_ctor_get_uint8(v___y_3404_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3422_ = lean_ctor_get_uint8(v___y_3404_, sizeof(void*)*7 + 2);
v_cacheInferType_3423_ = lean_ctor_get_uint8(v___y_3404_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3413_);
v___x_3424_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3411_, v_keyedConfig_3413_);
lean_inc(v_customCanUnfoldPredicate_x3f_3420_);
lean_inc(v_synthPendingDepth_3419_);
lean_inc(v_defEqCtx_x3f_3418_);
lean_inc_ref(v_localInstances_3417_);
lean_inc_ref(v_lctx_3416_);
lean_inc(v_zetaDeltaSet_3415_);
v___x_3425_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v_zetaDeltaSet_3415_);
lean_ctor_set(v___x_3425_, 2, v_lctx_3416_);
lean_ctor_set(v___x_3425_, 3, v_localInstances_3417_);
lean_ctor_set(v___x_3425_, 4, v_defEqCtx_x3f_3418_);
lean_ctor_set(v___x_3425_, 5, v_synthPendingDepth_3419_);
lean_ctor_set(v___x_3425_, 6, v_customCanUnfoldPredicate_x3f_3420_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7, v_trackZetaDelta_3414_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7 + 1, v_univApprox_3421_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3422_);
lean_ctor_set_uint8(v___x_3425_, sizeof(void*)*7 + 3, v_cacheInferType_3423_);
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3406_);
lean_inc(v___y_3402_);
lean_inc(v_a_3408_);
v___x_3426_ = lean_whnf(v_a_3408_, v___x_3425_, v___y_3402_, v___y_3406_, v___y_3401_);
v___y_3350_ = v___y_3401_;
v___y_3351_ = v___y_3402_;
v___y_3352_ = v___y_3403_;
v___y_3353_ = v___y_3404_;
v___y_3354_ = v_a_3408_;
v___y_3355_ = v___y_3405_;
v___y_3356_ = v___y_3406_;
v___y_3357_ = v___x_3426_;
goto v___jp_3349_;
}
else
{
lean_object* v___x_3427_; 
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3406_);
lean_inc(v___y_3402_);
lean_inc_ref(v___y_3404_);
lean_inc(v_a_3408_);
v___x_3427_ = lean_whnf(v_a_3408_, v___y_3404_, v___y_3402_, v___y_3406_, v___y_3401_);
v___y_3350_ = v___y_3401_;
v___y_3351_ = v___y_3402_;
v___y_3352_ = v___y_3403_;
v___y_3353_ = v___y_3404_;
v___y_3354_ = v_a_3408_;
v___y_3355_ = v___y_3405_;
v___y_3356_ = v___y_3406_;
v___y_3357_ = v___x_3427_;
goto v___jp_3349_;
}
}
else
{
lean_object* v_a_3428_; 
v_a_3428_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3407_, 1);
v___y_3340_ = v___y_3401_;
v___y_3341_ = v___y_3402_;
v___y_3342_ = v___y_3403_;
v___y_3343_ = v___y_3404_;
v___y_3344_ = v___y_3406_;
v___y_3345_ = v___y_3405_;
v_a_3346_ = v_a_3428_;
goto v___jp_3339_;
}
}
v___jp_3429_:
{
if (v___y_3436_ == 0)
{
v___y_3321_ = v___y_3432_;
v___y_3322_ = v___y_3434_;
v___y_3323_ = v___y_3433_;
v___y_3324_ = v___y_3431_;
v___y_3325_ = v___y_3435_;
v___y_3326_ = v___y_3430_;
goto v___jp_3320_;
}
else
{
v___y_3401_ = v___y_3430_;
v___y_3402_ = v___y_3431_;
v___y_3403_ = v___y_3432_;
v___y_3404_ = v___y_3433_;
v___y_3405_ = v___y_3434_;
v___y_3406_ = v___y_3435_;
goto v___jp_3400_;
}
}
v___jp_3437_:
{
if (v___y_3445_ == 0)
{
lean_dec_ref(v___y_3438_);
v___y_3430_ = v___y_3439_;
v___y_3431_ = v___y_3440_;
v___y_3432_ = v___y_3441_;
v___y_3433_ = v___y_3442_;
v___y_3434_ = v___y_3444_;
v___y_3435_ = v___y_3443_;
v___y_3436_ = v___x_3274_;
goto v___jp_3429_;
}
else
{
uint8_t v___x_3446_; 
v___x_3446_ = l_Lean_Expr_hasFVar(v___y_3438_);
lean_dec_ref(v___y_3438_);
if (v___x_3446_ == 0)
{
v___y_3401_ = v___y_3439_;
v___y_3402_ = v___y_3440_;
v___y_3403_ = v___y_3441_;
v___y_3404_ = v___y_3442_;
v___y_3405_ = v___y_3444_;
v___y_3406_ = v___y_3443_;
goto v___jp_3400_;
}
else
{
v___y_3430_ = v___y_3439_;
v___y_3431_ = v___y_3440_;
v___y_3432_ = v___y_3441_;
v___y_3433_ = v___y_3442_;
v___y_3434_ = v___y_3444_;
v___y_3435_ = v___y_3443_;
v___y_3436_ = v___x_3274_;
goto v___jp_3429_;
}
}
}
v___jp_3447_:
{
lean_object* v___x_3455_; 
lean_inc_ref(v___x_3319_);
v___x_3455_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3319_, v___y_3449_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; uint8_t v___x_3457_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v___x_3457_ = l_Lean_Expr_hasMVar(v_a_3456_);
if (v___x_3457_ == 0)
{
v___y_3438_ = v_a_3456_;
v___y_3439_ = v___y_3448_;
v___y_3440_ = v___y_3449_;
v___y_3441_ = v___y_3450_;
v___y_3442_ = v___y_3451_;
v___y_3443_ = v___y_3452_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3454_;
goto v___jp_3437_;
}
else
{
v___y_3438_ = v_a_3456_;
v___y_3439_ = v___y_3448_;
v___y_3440_ = v___y_3449_;
v___y_3441_ = v___y_3450_;
v___y_3442_ = v___y_3451_;
v___y_3443_ = v___y_3452_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___x_3274_;
goto v___jp_3437_;
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec_ref(v___x_3319_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3458_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3455_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3455_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
v___jp_3466_:
{
if (v___y_3473_ == 0)
{
v___y_3321_ = v___y_3469_;
v___y_3322_ = v___y_3471_;
v___y_3323_ = v___y_3470_;
v___y_3324_ = v___y_3468_;
v___y_3325_ = v___y_3472_;
v___y_3326_ = v___y_3467_;
goto v___jp_3320_;
}
else
{
v___y_3448_ = v___y_3467_;
v___y_3449_ = v___y_3468_;
v___y_3450_ = v___y_3469_;
v___y_3451_ = v___y_3470_;
v___y_3452_ = v___y_3472_;
v___y_3453_ = v___y_3471_;
v___y_3454_ = v___y_3473_;
goto v___jp_3447_;
}
}
v___jp_3474_:
{
uint8_t v_useDecide_3481_; 
v_useDecide_3481_ = lean_ctor_get_uint8(v_config_3167_, sizeof(void*)*1);
if (v_useDecide_3481_ == 0)
{
v___y_3467_ = v___y_3480_;
v___y_3468_ = v___y_3478_;
v___y_3469_ = v___y_3475_;
v___y_3470_ = v___y_3477_;
v___y_3471_ = v_isHEq_3476_;
v___y_3472_ = v___y_3479_;
v___y_3473_ = v___x_3274_;
goto v___jp_3466_;
}
else
{
uint8_t v___x_3482_; 
v___x_3482_ = l_Lean_Expr_hasFVar(v___x_3319_);
if (v___x_3482_ == 0)
{
v___y_3448_ = v___y_3480_;
v___y_3449_ = v___y_3478_;
v___y_3450_ = v___y_3475_;
v___y_3451_ = v___y_3477_;
v___y_3452_ = v___y_3479_;
v___y_3453_ = v_isHEq_3476_;
v___y_3454_ = v_useDecide_3481_;
goto v___jp_3447_;
}
else
{
v___y_3467_ = v___y_3480_;
v___y_3468_ = v___y_3478_;
v___y_3469_ = v___y_3475_;
v___y_3470_ = v___y_3477_;
v___y_3471_ = v_isHEq_3476_;
v___y_3472_ = v___y_3479_;
v___y_3473_ = v___x_3274_;
goto v___jp_3466_;
}
}
}
v___jp_3483_:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Lean_Meta_isExprDefEq(v___y_3485_, v___y_3486_, v___y_3488_, v___y_3484_, v___y_3490_, v___y_3489_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; uint8_t v___x_3493_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v___x_3493_ = lean_unbox(v_a_3492_);
lean_dec(v_a_3492_);
if (v___x_3493_ == 0)
{
v___y_3475_ = v___y_3487_;
v_isHEq_3476_ = v___x_3178_;
v___y_3477_ = v___y_3488_;
v___y_3478_ = v___y_3484_;
v___y_3479_ = v___y_3490_;
v___y_3480_ = v___y_3489_;
goto v___jp_3474_;
}
else
{
lean_object* v___x_3494_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref(v_config_3167_);
lean_inc(v_mvarId_3168_);
v___x_3494_ = l_Lean_MVarId_getType(v_mvarId_3168_, v___y_3488_, v___y_3484_, v___y_3490_, v___y_3489_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
v___x_3496_ = l_Lean_LocalDecl_toExpr(v_val_3199_);
v___x_3497_ = l_Lean_Meta_mkEqOfHEq(v___x_3496_, v___x_3178_, v___y_3488_, v___y_3484_, v___y_3490_, v___y_3489_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = l_Lean_Meta_mkNoConfusion(v_a_3495_, v_a_3498_, v___y_3488_, v___y_3484_, v___y_3490_, v___y_3489_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___x_3501_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3168_, v_a_3500_, v___y_3484_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
lean_dec_ref_known(v___x_3501_, 1);
v___x_3502_ = lean_box(v___x_3178_);
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
v___x_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___x_3203_);
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
v_a_3185_ = v___x_3505_;
goto v___jp_3184_;
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
v_a_3506_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3501_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3501_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3514_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3499_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3499_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_a_3495_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3522_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3497_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3497_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3530_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3494_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3494_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec_ref(v___x_3319_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3538_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3491_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3491_);
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
v___jp_3546_:
{
lean_object* v___x_3552_; 
lean_inc_ref(v___x_3319_);
v___x_3552_ = l_Lean_Meta_matchHEq_x3f(v___x_3319_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
if (lean_obj_tag(v_a_3553_) == 1)
{
lean_object* v_val_3554_; lean_object* v_snd_3555_; lean_object* v_snd_3556_; lean_object* v_fst_3557_; lean_object* v_fst_3558_; lean_object* v_fst_3559_; lean_object* v_snd_3560_; lean_object* v___x_3561_; 
v_val_3554_ = lean_ctor_get(v_a_3553_, 0);
lean_inc(v_val_3554_);
lean_dec_ref_known(v_a_3553_, 1);
v_snd_3555_ = lean_ctor_get(v_val_3554_, 1);
lean_inc(v_snd_3555_);
v_snd_3556_ = lean_ctor_get(v_snd_3555_, 1);
lean_inc(v_snd_3556_);
v_fst_3557_ = lean_ctor_get(v_val_3554_, 0);
lean_inc(v_fst_3557_);
lean_dec(v_val_3554_);
v_fst_3558_ = lean_ctor_get(v_snd_3555_, 0);
lean_inc(v_fst_3558_);
lean_dec(v_snd_3555_);
v_fst_3559_ = lean_ctor_get(v_snd_3556_, 0);
lean_inc(v_fst_3559_);
v_snd_3560_ = lean_ctor_get(v_snd_3556_, 1);
lean_inc(v_snd_3560_);
lean_dec(v_snd_3556_);
v___x_3561_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3558_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
if (lean_obj_tag(v_a_3562_) == 1)
{
lean_object* v_val_3563_; lean_object* v___x_3564_; 
v_val_3563_ = lean_ctor_get(v_a_3562_, 0);
lean_inc(v_val_3563_);
lean_dec_ref_known(v_a_3562_, 1);
v___x_3564_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3560_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
if (lean_obj_tag(v_a_3565_) == 1)
{
lean_object* v_toConstantVal_3566_; lean_object* v_val_3567_; lean_object* v_toConstantVal_3568_; lean_object* v_name_3569_; lean_object* v_name_3570_; uint8_t v___x_3571_; 
v_toConstantVal_3566_ = lean_ctor_get(v_val_3563_, 0);
lean_inc_ref(v_toConstantVal_3566_);
lean_dec(v_val_3563_);
v_val_3567_ = lean_ctor_get(v_a_3565_, 0);
lean_inc(v_val_3567_);
lean_dec_ref_known(v_a_3565_, 1);
v_toConstantVal_3568_ = lean_ctor_get(v_val_3567_, 0);
lean_inc_ref(v_toConstantVal_3568_);
lean_dec(v_val_3567_);
v_name_3569_ = lean_ctor_get(v_toConstantVal_3566_, 0);
lean_inc(v_name_3569_);
lean_dec_ref(v_toConstantVal_3566_);
v_name_3570_ = lean_ctor_get(v_toConstantVal_3568_, 0);
lean_inc(v_name_3570_);
lean_dec_ref(v_toConstantVal_3568_);
v___x_3571_ = lean_name_eq(v_name_3569_, v_name_3570_);
lean_dec(v_name_3570_);
lean_dec(v_name_3569_);
if (v___x_3571_ == 0)
{
v___y_3484_ = v___y_3549_;
v___y_3485_ = v_fst_3557_;
v___y_3486_ = v_fst_3559_;
v___y_3487_ = v_isEq_3547_;
v___y_3488_ = v___y_3548_;
v___y_3489_ = v___y_3551_;
v___y_3490_ = v___y_3550_;
goto v___jp_3483_;
}
else
{
if (v___x_3274_ == 0)
{
lean_dec(v_fst_3559_);
lean_dec(v_fst_3557_);
v___y_3475_ = v_isEq_3547_;
v_isHEq_3476_ = v___x_3178_;
v___y_3477_ = v___y_3548_;
v___y_3478_ = v___y_3549_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
goto v___jp_3474_;
}
else
{
v___y_3484_ = v___y_3549_;
v___y_3485_ = v_fst_3557_;
v___y_3486_ = v_fst_3559_;
v___y_3487_ = v_isEq_3547_;
v___y_3488_ = v___y_3548_;
v___y_3489_ = v___y_3551_;
v___y_3490_ = v___y_3550_;
goto v___jp_3483_;
}
}
}
else
{
lean_dec(v_a_3565_);
lean_dec(v_val_3563_);
lean_dec(v_fst_3559_);
lean_dec(v_fst_3557_);
v___y_3475_ = v_isEq_3547_;
v_isHEq_3476_ = v___x_3178_;
v___y_3477_ = v___y_3548_;
v___y_3478_ = v___y_3549_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
goto v___jp_3474_;
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v_val_3563_);
lean_dec(v_fst_3559_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___x_3319_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3572_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3564_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3564_);
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
else
{
lean_dec(v_a_3562_);
lean_dec(v_snd_3560_);
lean_dec(v_fst_3559_);
lean_dec(v_fst_3557_);
v___y_3475_ = v_isEq_3547_;
v_isHEq_3476_ = v___x_3178_;
v___y_3477_ = v___y_3548_;
v___y_3478_ = v___y_3549_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
goto v___jp_3474_;
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec(v_snd_3560_);
lean_dec(v_fst_3559_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___x_3319_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3580_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3561_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3561_);
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
else
{
lean_dec(v_a_3553_);
v___y_3475_ = v_isEq_3547_;
v_isHEq_3476_ = v___x_3274_;
v___y_3477_ = v___y_3548_;
v___y_3478_ = v___y_3549_;
v___y_3479_ = v___y_3550_;
v___y_3480_ = v___y_3551_;
goto v___jp_3474_;
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v___x_3319_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3588_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3552_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3552_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
v___jp_3596_:
{
lean_object* v___x_3601_; 
lean_inc_ref(v___x_3319_);
v___x_3601_ = l_Lean_Meta_matchEq_x3f(v___x_3319_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
if (lean_obj_tag(v_a_3602_) == 1)
{
lean_object* v_val_3603_; lean_object* v_snd_3604_; lean_object* v_fst_3605_; lean_object* v_snd_3606_; lean_object* v___x_3607_; 
v_val_3603_ = lean_ctor_get(v_a_3602_, 0);
lean_inc(v_val_3603_);
lean_dec_ref_known(v_a_3602_, 1);
v_snd_3604_ = lean_ctor_get(v_val_3603_, 1);
lean_inc(v_snd_3604_);
lean_dec(v_val_3603_);
v_fst_3605_ = lean_ctor_get(v_snd_3604_, 0);
lean_inc(v_fst_3605_);
v_snd_3606_ = lean_ctor_get(v_snd_3604_, 1);
lean_inc(v_snd_3606_);
lean_dec(v_snd_3604_);
v___x_3607_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3605_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
if (lean_obj_tag(v_a_3608_) == 1)
{
lean_object* v_val_3609_; lean_object* v___x_3610_; 
v_val_3609_ = lean_ctor_get(v_a_3608_, 0);
lean_inc(v_val_3609_);
lean_dec_ref_known(v_a_3608_, 1);
v___x_3610_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3606_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
if (lean_obj_tag(v_a_3611_) == 1)
{
lean_object* v_toConstantVal_3612_; lean_object* v_val_3613_; lean_object* v_toConstantVal_3614_; lean_object* v_name_3615_; lean_object* v_name_3616_; uint8_t v___x_3617_; 
v_toConstantVal_3612_ = lean_ctor_get(v_val_3609_, 0);
lean_inc_ref(v_toConstantVal_3612_);
lean_dec(v_val_3609_);
v_val_3613_ = lean_ctor_get(v_a_3611_, 0);
lean_inc(v_val_3613_);
lean_dec_ref_known(v_a_3611_, 1);
v_toConstantVal_3614_ = lean_ctor_get(v_val_3613_, 0);
lean_inc_ref(v_toConstantVal_3614_);
lean_dec(v_val_3613_);
v_name_3615_ = lean_ctor_get(v_toConstantVal_3612_, 0);
lean_inc(v_name_3615_);
lean_dec_ref(v_toConstantVal_3612_);
v_name_3616_ = lean_ctor_get(v_toConstantVal_3614_, 0);
lean_inc(v_name_3616_);
lean_dec_ref(v_toConstantVal_3614_);
v___x_3617_ = lean_name_eq(v_name_3615_, v_name_3616_);
lean_dec(v_name_3616_);
lean_dec(v_name_3615_);
if (v___x_3617_ == 0)
{
lean_dec_ref(v___x_3319_);
lean_dec_ref(v_config_3167_);
v___y_3205_ = v___y_3599_;
v___y_3206_ = v___y_3600_;
v___y_3207_ = v___y_3597_;
v___y_3208_ = v___y_3598_;
goto v___jp_3204_;
}
else
{
if (v___x_3274_ == 0)
{
lean_del_object(v___x_3201_);
v_isEq_3547_ = v___x_3178_;
v___y_3548_ = v___y_3597_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
goto v___jp_3546_;
}
else
{
lean_dec_ref(v___x_3319_);
lean_dec_ref(v_config_3167_);
v___y_3205_ = v___y_3599_;
v___y_3206_ = v___y_3600_;
v___y_3207_ = v___y_3597_;
v___y_3208_ = v___y_3598_;
goto v___jp_3204_;
}
}
}
else
{
lean_dec(v_a_3611_);
lean_dec(v_val_3609_);
lean_del_object(v___x_3201_);
v_isEq_3547_ = v___x_3178_;
v___y_3548_ = v___y_3597_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
goto v___jp_3546_;
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec(v_val_3609_);
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3618_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3610_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3610_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
lean_dec(v_a_3608_);
lean_dec(v_snd_3606_);
lean_del_object(v___x_3201_);
v_isEq_3547_ = v___x_3178_;
v___y_3548_ = v___y_3597_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
goto v___jp_3546_;
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v_snd_3606_);
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3626_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3607_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3607_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
else
{
lean_dec(v_a_3602_);
lean_del_object(v___x_3201_);
v_isEq_3547_ = v___x_3274_;
v___y_3548_ = v___y_3597_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3599_;
v___y_3551_ = v___y_3600_;
goto v___jp_3546_;
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3634_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3601_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3601_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
v___jp_3642_:
{
lean_object* v___x_3647_; 
lean_inc_ref(v___x_3319_);
v___x_3647_ = l_Lean_refutableHasNotBit_x3f(v___x_3319_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
lean_inc(v_a_3648_);
lean_dec_ref_known(v___x_3647_, 1);
if (lean_obj_tag(v_a_3648_) == 1)
{
lean_object* v_val_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3689_; 
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec_ref(v_config_3167_);
v_val_3649_ = lean_ctor_get(v_a_3648_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_a_3648_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3651_ = v_a_3648_;
v_isShared_3652_ = v_isSharedCheck_3689_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_val_3649_);
lean_dec(v_a_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3689_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3653_; 
lean_inc(v_mvarId_3168_);
v___x_3653_ = l_Lean_MVarId_getType(v_mvarId_3168_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v___x_3655_ = l_Lean_LocalDecl_toExpr(v_val_3199_);
v___x_3656_ = l_Lean_Meta_mkAbsurd(v_a_3654_, v_val_3649_, v___x_3655_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3658_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___x_3656_, 1);
v___x_3658_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3168_, v_a_3657_, v___y_3644_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
lean_dec_ref_known(v___x_3658_, 1);
v___x_3659_ = lean_box(v___x_3178_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3659_);
v___x_3661_ = v___x_3651_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
lean_ctor_set(v___x_3662_, 1, v___x_3203_);
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
v_a_3185_ = v___x_3663_;
goto v___jp_3184_;
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_del_object(v___x_3651_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
v_a_3665_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3658_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3658_);
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
lean_del_object(v___x_3651_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3673_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3656_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3656_);
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
lean_del_object(v___x_3651_);
lean_dec(v_val_3649_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3681_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3653_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3653_);
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
lean_object* v___x_3690_; 
lean_dec(v_a_3648_);
lean_inc_ref(v___x_3319_);
v___x_3690_ = l_Lean_Meta_matchNe_x3f(v___x_3319_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3690_, 1);
if (lean_obj_tag(v_a_3691_) == 1)
{
lean_object* v_val_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3762_; 
v_val_3692_ = lean_ctor_get(v_a_3691_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_a_3691_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3694_ = v_a_3691_;
v_isShared_3695_ = v_isSharedCheck_3762_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_val_3692_);
lean_dec(v_a_3691_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3762_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_snd_3696_; lean_object* v_fst_3697_; lean_object* v_snd_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3761_; 
v_snd_3696_ = lean_ctor_get(v_val_3692_, 1);
lean_inc(v_snd_3696_);
lean_dec(v_val_3692_);
v_fst_3697_ = lean_ctor_get(v_snd_3696_, 0);
v_snd_3698_ = lean_ctor_get(v_snd_3696_, 1);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_snd_3696_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3700_ = v_snd_3696_;
v_isShared_3701_ = v_isSharedCheck_3761_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_snd_3698_);
lean_inc(v_fst_3697_);
lean_dec(v_snd_3696_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3761_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3702_; 
lean_inc(v_fst_3697_);
v___x_3702_ = l_Lean_Meta_isExprDefEq(v_fst_3697_, v_snd_3698_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; uint8_t v___x_3704_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3703_);
lean_dec_ref_known(v___x_3702_, 1);
v___x_3704_ = lean_unbox(v_a_3703_);
lean_dec(v_a_3703_);
if (v___x_3704_ == 0)
{
lean_del_object(v___x_3700_);
lean_dec(v_fst_3697_);
lean_del_object(v___x_3694_);
v___y_3597_ = v___y_3643_;
v___y_3598_ = v___y_3644_;
v___y_3599_ = v___y_3645_;
v___y_3600_ = v___y_3646_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3705_; 
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec_ref(v_config_3167_);
lean_inc(v_mvarId_3168_);
v___x_3705_ = l_Lean_MVarId_getType(v_mvarId_3168_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3707_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref_known(v___x_3705_, 1);
v___x_3707_ = l_Lean_Meta_mkEqRefl(v_fst_3697_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v___x_3709_ = l_Lean_LocalDecl_toExpr(v_val_3199_);
v___x_3710_ = l_Lean_Meta_mkAbsurd(v_a_3706_, v_a_3708_, v___x_3709_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3712_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v___x_3712_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3168_, v_a_3711_, v___y_3644_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
lean_dec_ref_known(v___x_3712_, 1);
v___x_3713_ = lean_box(v___x_3178_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3713_);
v___x_3715_ = v___x_3694_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3717_; 
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 1, v___x_3203_);
lean_ctor_set(v___x_3700_, 0, v___x_3715_);
v___x_3717_ = v___x_3700_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v___x_3203_);
v___x_3717_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
v_a_3185_ = v___x_3718_;
goto v___jp_3184_;
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_del_object(v___x_3700_);
lean_del_object(v___x_3694_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
v_a_3721_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3712_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3712_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_del_object(v___x_3700_);
lean_del_object(v___x_3694_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3729_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3710_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3710_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v_a_3706_);
lean_del_object(v___x_3700_);
lean_del_object(v___x_3694_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3737_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3707_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3707_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_del_object(v___x_3700_);
lean_dec(v_fst_3697_);
lean_del_object(v___x_3694_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3745_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3705_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3705_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_del_object(v___x_3700_);
lean_dec(v_fst_3697_);
lean_del_object(v___x_3694_);
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3753_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3702_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3702_);
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
}
}
else
{
lean_dec(v_a_3691_);
v___y_3597_ = v___y_3643_;
v___y_3598_ = v___y_3644_;
v___y_3599_ = v___y_3645_;
v___y_3600_ = v___y_3646_;
goto v___jp_3596_;
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3763_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3690_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3690_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec_ref(v___x_3319_);
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3771_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3647_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3647_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
}
else
{
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
v_a_3193_ = v___x_3245_;
goto v___jp_3192_;
}
v___jp_3204_:
{
lean_object* v___x_3209_; 
lean_inc(v_mvarId_3168_);
v___x_3209_ = l_Lean_MVarId_getType(v_mvarId_3168_, v___y_3207_, v___y_3208_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = l_Lean_LocalDecl_toExpr(v_val_3199_);
v___x_3212_ = l_Lean_Meta_mkNoConfusion(v_a_3210_, v___x_3211_, v___y_3207_, v___y_3208_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3214_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref_known(v___x_3212_, 1);
v___x_3214_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3168_, v_a_3213_, v___y_3208_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
lean_dec_ref_known(v___x_3214_, 1);
v___x_3215_ = lean_box(v___x_3178_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3215_);
v___x_3217_ = v___x_3201_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v___x_3203_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
v_a_3185_ = v___x_3219_;
goto v___jp_3184_;
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_del_object(v___x_3201_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
v_a_3221_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3214_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3214_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_del_object(v___x_3201_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3229_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3212_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3212_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_del_object(v___x_3201_);
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
v_a_3237_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3209_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3209_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
v___jp_3246_:
{
lean_object* v_searchFuel_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_searchFuel_3251_ = lean_ctor_get(v_config_3167_, 0);
v___x_3252_ = l_Lean_LocalDecl_fvarId(v_val_3199_);
lean_dec(v_val_3199_);
lean_inc(v_searchFuel_3251_);
lean_inc(v_mvarId_3168_);
v___x_3253_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3168_, v___x_3252_, v_searchFuel_3251_, v___y_3249_, v___y_3247_, v___y_3250_, v___y_3248_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; uint8_t v___x_3255_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref_known(v___x_3253_, 1);
v___x_3255_ = lean_unbox(v_a_3254_);
lean_dec(v_a_3254_);
if (v___x_3255_ == 0)
{
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
v_a_3193_ = v___x_3245_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v___x_3256_ = lean_box(v___x_3178_);
v___x_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v___x_3203_);
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
v_a_3185_ = v___x_3259_;
goto v___jp_3184_;
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3260_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3253_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3253_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
v___jp_3268_:
{
if (v___y_3273_ == 0)
{
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
v_a_3193_ = v___x_3245_;
goto v___jp_3192_;
}
else
{
v___y_3247_ = v___y_3269_;
v___y_3248_ = v___y_3270_;
v___y_3249_ = v___y_3271_;
v___y_3250_ = v___y_3272_;
goto v___jp_3246_;
}
}
v___jp_3275_:
{
if (v___y_3280_ == 0)
{
v___y_3247_ = v___y_3276_;
v___y_3248_ = v___y_3277_;
v___y_3249_ = v___y_3278_;
v___y_3250_ = v___y_3279_;
goto v___jp_3246_;
}
else
{
v___y_3269_ = v___y_3276_;
v___y_3270_ = v___y_3277_;
v___y_3271_ = v___y_3278_;
v___y_3272_ = v___y_3279_;
v___y_3273_ = v___x_3274_;
goto v___jp_3268_;
}
}
v___jp_3281_:
{
if (v___y_3287_ == 0)
{
v___y_3269_ = v___y_3282_;
v___y_3270_ = v___y_3283_;
v___y_3271_ = v___y_3284_;
v___y_3272_ = v___y_3285_;
v___y_3273_ = v___x_3274_;
goto v___jp_3268_;
}
else
{
v___y_3276_ = v___y_3282_;
v___y_3277_ = v___y_3283_;
v___y_3278_ = v___y_3284_;
v___y_3279_ = v___y_3285_;
v___y_3280_ = v___y_3286_;
goto v___jp_3275_;
}
}
v___jp_3288_:
{
uint8_t v_emptyType_3295_; 
v_emptyType_3295_ = lean_ctor_get_uint8(v_config_3167_, sizeof(void*)*1 + 1);
if (v_emptyType_3295_ == 0)
{
v___y_3282_ = v___y_3292_;
v___y_3283_ = v___y_3294_;
v___y_3284_ = v___y_3291_;
v___y_3285_ = v___y_3293_;
v___y_3286_ = v___y_3290_;
v___y_3287_ = v___x_3274_;
goto v___jp_3281_;
}
else
{
if (v___y_3289_ == 0)
{
v___y_3276_ = v___y_3292_;
v___y_3277_ = v___y_3294_;
v___y_3278_ = v___y_3291_;
v___y_3279_ = v___y_3293_;
v___y_3280_ = v___y_3290_;
goto v___jp_3275_;
}
else
{
v___y_3282_ = v___y_3292_;
v___y_3283_ = v___y_3294_;
v___y_3284_ = v___y_3291_;
v___y_3285_ = v___y_3293_;
v___y_3286_ = v___y_3290_;
v___y_3287_ = v___x_3274_;
goto v___jp_3281_;
}
}
}
v___jp_3296_:
{
if (v___y_3303_ == 0)
{
v___y_3289_ = v___y_3298_;
v___y_3290_ = v___y_3302_;
v___y_3291_ = v___y_3301_;
v___y_3292_ = v___y_3300_;
v___y_3293_ = v___y_3297_;
v___y_3294_ = v___y_3299_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3304_; 
lean_inc(v_val_3199_);
lean_inc(v_mvarId_3168_);
v___x_3304_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3168_, v_val_3199_, v___y_3301_, v___y_3300_, v___y_3297_, v___y_3299_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; uint8_t v___x_3306_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = lean_unbox(v_a_3305_);
lean_dec(v_a_3305_);
if (v___x_3306_ == 0)
{
v___y_3289_ = v___y_3298_;
v___y_3290_ = v___y_3302_;
v___y_3291_ = v___y_3301_;
v___y_3292_ = v___y_3300_;
v___y_3293_ = v___y_3297_;
v___y_3294_ = v___y_3299_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_dec(v_val_3199_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v___x_3307_ = lean_box(v___x_3178_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
v___x_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
lean_ctor_set(v___x_3309_, 1, v___x_3203_);
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
v_a_3185_ = v___x_3310_;
goto v___jp_3184_;
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec(v_val_3199_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_dec(v_mvarId_3168_);
lean_dec_ref(v_config_3167_);
v_a_3311_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3304_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3304_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
}
}
}
v___jp_3184_:
{
lean_object* v___x_3186_; lean_object* v___x_3188_; 
v___x_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3186_, 0, v_a_3185_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3186_);
v___x_3188_ = v___x_3182_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_snd_3180_);
v___x_3188_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
return v___x_3189_;
}
}
v___jp_3192_:
{
lean_object* v___x_3194_; size_t v___x_3195_; size_t v___x_3196_; 
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3191_);
lean_ctor_set(v___x_3194_, 1, v_a_3193_);
v___x_3195_ = ((size_t)1ULL);
v___x_3196_ = lean_usize_add(v_i_3171_, v___x_3195_);
v_i_3171_ = v___x_3196_;
v_b_3172_ = v___x_3194_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3852_, lean_object* v_mvarId_3853_, lean_object* v_as_3854_, lean_object* v_sz_3855_, lean_object* v_i_3856_, lean_object* v_b_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
size_t v_sz_boxed_3863_; size_t v_i_boxed_3864_; lean_object* v_res_3865_; 
v_sz_boxed_3863_ = lean_unbox_usize(v_sz_3855_);
lean_dec(v_sz_3855_);
v_i_boxed_3864_ = lean_unbox_usize(v_i_3856_);
lean_dec(v_i_3856_);
v_res_3865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3852_, v_mvarId_3853_, v_as_3854_, v_sz_boxed_3863_, v_i_boxed_3864_, v_b_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec_ref(v_as_3854_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3866_, lean_object* v_mvarId_3867_, lean_object* v_as_3868_, size_t v_sz_3869_, size_t v_i_3870_, lean_object* v_b_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
uint8_t v___x_3877_; 
v___x_3877_ = lean_usize_dec_lt(v_i_3870_, v_sz_3869_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v___x_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3878_, 0, v_b_3871_);
return v___x_3878_;
}
else
{
lean_object* v_snd_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_4549_; 
v_snd_3879_ = lean_ctor_get(v_b_3871_, 1);
v_isSharedCheck_4549_ = !lean_is_exclusive(v_b_3871_);
if (v_isSharedCheck_4549_ == 0)
{
lean_object* v_unused_4550_; 
v_unused_4550_ = lean_ctor_get(v_b_3871_, 0);
lean_dec(v_unused_4550_);
v___x_3881_ = v_b_3871_;
v_isShared_3882_ = v_isSharedCheck_4549_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_snd_3879_);
lean_dec(v_b_3871_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_4549_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v_a_3884_; lean_object* v___x_3890_; lean_object* v_a_3892_; lean_object* v_a_3897_; 
v___x_3890_ = lean_box(0);
v_a_3897_ = lean_array_uget(v_as_3868_, v_i_3870_);
if (lean_obj_tag(v_a_3897_) == 0)
{
lean_del_object(v___x_3881_);
v_a_3892_ = v_snd_3879_;
goto v___jp_3891_;
}
else
{
lean_object* v_val_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_4548_; 
v_val_3898_ = lean_ctor_get(v_a_3897_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v_a_3897_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_3900_ = v_a_3897_;
v_isShared_3901_ = v_isSharedCheck_4548_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_val_3898_);
lean_dec(v_a_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_4548_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___x_3944_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; uint8_t v___y_3972_; uint8_t v___x_3973_; lean_object* v___y_3975_; lean_object* v___y_3976_; uint8_t v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; uint8_t v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; uint8_t v___y_3986_; uint8_t v___y_3988_; uint8_t v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; uint8_t v___y_4000_; uint8_t v___y_4001_; uint8_t v___y_4002_; 
v___x_3902_ = lean_box(0);
v___x_3944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3973_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3898_);
if (v___x_3973_ == 0)
{
lean_object* v___x_4018_; uint8_t v___y_4020_; uint8_t v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4029_; lean_object* v___y_4030_; uint8_t v___y_4031_; lean_object* v___y_4032_; uint8_t v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; uint8_t v___y_4036_; lean_object* v___y_4039_; lean_object* v___y_4040_; uint8_t v___y_4041_; lean_object* v___y_4042_; uint8_t v___y_4043_; lean_object* v___y_4044_; lean_object* v_a_4045_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; uint8_t v___y_4052_; uint8_t v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4100_; lean_object* v___y_4101_; uint8_t v___y_4102_; uint8_t v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4129_; lean_object* v___y_4130_; uint8_t v___y_4131_; uint8_t v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; uint8_t v___y_4135_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; uint8_t v___y_4140_; lean_object* v___y_4141_; uint8_t v___y_4142_; lean_object* v___y_4143_; uint8_t v___y_4144_; lean_object* v___y_4147_; lean_object* v___y_4148_; uint8_t v___y_4149_; uint8_t v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; uint8_t v___y_4153_; lean_object* v___y_4166_; lean_object* v___y_4167_; uint8_t v___y_4168_; uint8_t v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; uint8_t v___y_4172_; uint8_t v___y_4174_; uint8_t v_isHEq_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; uint8_t v___y_4189_; uint8_t v_isEq_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___x_4478_; 
v___x_4018_ = l_Lean_LocalDecl_type(v_val_3898_);
lean_inc_ref(v___x_4018_);
v___x_4478_ = l_Lean_Meta_matchNot_x3f(v___x_4018_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4479_; 
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref_known(v___x_4478_, 1);
if (lean_obj_tag(v_a_4479_) == 1)
{
lean_object* v_val_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4539_; 
v_val_4480_ = lean_ctor_get(v_a_4479_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_a_4479_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4482_ = v_a_4479_;
v_isShared_4483_ = v_isSharedCheck_4539_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_val_4480_);
lean_dec(v_a_4479_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4539_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; 
v___x_4484_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4480_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref_known(v___x_4484_, 1);
if (lean_obj_tag(v_a_4485_) == 1)
{
lean_object* v_val_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4530_; 
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec_ref(v_config_3866_);
v_val_4486_ = lean_ctor_get(v_a_4485_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v_a_4485_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4488_ = v_a_4485_;
v_isShared_4489_ = v_isSharedCheck_4530_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_val_4486_);
lean_dec(v_a_4485_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4530_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4490_; 
lean_inc(v_mvarId_3867_);
v___x_4490_ = l_Lean_MVarId_getType(v_mvarId_3867_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_a_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4490_, 1);
v___x_4492_ = l_Lean_LocalDecl_toExpr(v_val_3898_);
v___x_4493_ = l_Lean_mkFVar(v_val_4486_);
v___x_4494_ = l_Lean_Expr_app___override(v___x_4492_, v___x_4493_);
v___x_4495_ = l_Lean_Meta_mkFalseElim(v_a_4491_, v___x_4494_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; lean_object* v___x_4497_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
v___x_4497_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3867_, v_a_4496_, v___y_3873_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v___x_4498_; lean_object* v___x_4500_; 
lean_dec_ref_known(v___x_4497_, 1);
v___x_4498_ = lean_box(v___x_3877_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 0, v___x_4498_);
v___x_4500_ = v___x_4488_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4501_; lean_object* v___x_4503_; 
v___x_4501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
lean_ctor_set(v___x_4501_, 1, v___x_3902_);
if (v_isShared_4483_ == 0)
{
lean_ctor_set_tag(v___x_4482_, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4501_);
v___x_4503_ = v___x_4482_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
v_a_3884_ = v___x_4503_;
goto v___jp_3883_;
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_del_object(v___x_4488_);
lean_del_object(v___x_4482_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
v_a_4506_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4497_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4497_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
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
lean_del_object(v___x_4488_);
lean_del_object(v___x_4482_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4514_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4495_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4495_);
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
else
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
lean_del_object(v___x_4488_);
lean_dec(v_val_4486_);
lean_del_object(v___x_4482_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4522_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4490_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4490_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
}
else
{
lean_dec(v_a_4485_);
lean_del_object(v___x_4482_);
v___y_4342_ = v___y_3872_;
v___y_4343_ = v___y_3873_;
v___y_4344_ = v___y_3874_;
v___y_4345_ = v___y_3875_;
goto v___jp_4341_;
}
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_del_object(v___x_4482_);
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4531_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4484_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4484_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
}
else
{
lean_dec(v_a_4479_);
v___y_4342_ = v___y_3872_;
v___y_4343_ = v___y_3873_;
v___y_4344_ = v___y_3874_;
v___y_4345_ = v___y_3875_;
goto v___jp_4341_;
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4540_ = lean_ctor_get(v___x_4478_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4478_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4478_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
v___jp_4019_:
{
uint8_t v_genDiseq_4026_; 
v_genDiseq_4026_ = lean_ctor_get_uint8(v_config_3866_, sizeof(void*)*1 + 2);
if (v_genDiseq_4026_ == 0)
{
lean_dec_ref(v___x_4018_);
v___y_3996_ = v___y_4025_;
v___y_3997_ = v___y_4024_;
v___y_3998_ = v___y_4023_;
v___y_3999_ = v___y_4022_;
v___y_4000_ = v___y_4020_;
v___y_4001_ = v___y_4021_;
v___y_4002_ = v___x_3973_;
goto v___jp_3995_;
}
else
{
uint8_t v___x_4027_; 
v___x_4027_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4018_);
v___y_3996_ = v___y_4025_;
v___y_3997_ = v___y_4024_;
v___y_3998_ = v___y_4023_;
v___y_3999_ = v___y_4022_;
v___y_4000_ = v___y_4020_;
v___y_4001_ = v___y_4021_;
v___y_4002_ = v___x_4027_;
goto v___jp_3995_;
}
}
v___jp_4028_:
{
if (v___y_4036_ == 0)
{
lean_dec_ref(v___y_4032_);
v___y_4020_ = v___y_4031_;
v___y_4021_ = v___y_4033_;
v___y_4022_ = v___y_4030_;
v___y_4023_ = v___y_4034_;
v___y_4024_ = v___y_4035_;
v___y_4025_ = v___y_4029_;
goto v___jp_4019_;
}
else
{
lean_object* v___x_4037_; 
lean_dec_ref(v___x_4018_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v___x_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4037_, 0, v___y_4032_);
return v___x_4037_;
}
}
v___jp_4038_:
{
uint8_t v___x_4046_; 
v___x_4046_ = l_Lean_Exception_isInterrupt(v_a_4045_);
if (v___x_4046_ == 0)
{
uint8_t v___x_4047_; 
lean_inc_ref(v_a_4045_);
v___x_4047_ = l_Lean_Exception_isRuntime(v_a_4045_);
v___y_4029_ = v___y_4039_;
v___y_4030_ = v___y_4040_;
v___y_4031_ = v___y_4041_;
v___y_4032_ = v_a_4045_;
v___y_4033_ = v___y_4043_;
v___y_4034_ = v___y_4042_;
v___y_4035_ = v___y_4044_;
v___y_4036_ = v___x_4047_;
goto v___jp_4028_;
}
else
{
v___y_4029_ = v___y_4039_;
v___y_4030_ = v___y_4040_;
v___y_4031_ = v___y_4041_;
v___y_4032_ = v_a_4045_;
v___y_4033_ = v___y_4043_;
v___y_4034_ = v___y_4042_;
v___y_4035_ = v___y_4044_;
v___y_4036_ = v___x_4046_;
goto v___jp_4028_;
}
}
v___jp_4048_:
{
if (lean_obj_tag(v___y_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v_a_4057_ = lean_ctor_get(v___y_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref_known(v___y_4056_, 1);
v___x_4058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4059_ = l_Lean_Expr_isConstOf(v_a_4057_, v___x_4058_);
lean_dec(v_a_4057_);
if (v___x_4059_ == 0)
{
lean_dec_ref(v___y_4050_);
v___y_4020_ = v___y_4052_;
v___y_4021_ = v___y_4053_;
v___y_4022_ = v___y_4051_;
v___y_4023_ = v___y_4054_;
v___y_4024_ = v___y_4055_;
v___y_4025_ = v___y_4049_;
goto v___jp_4019_;
}
else
{
lean_object* v___x_4060_; 
lean_inc_ref(v___y_4050_);
v___x_4060_ = l_Lean_Meta_mkEqRefl(v___y_4050_, v___y_4051_, v___y_4054_, v___y_4055_, v___y_4049_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4062_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
lean_inc(v_mvarId_3867_);
v___x_4062_ = l_Lean_MVarId_getType(v_mvarId_3867_, v___y_4051_, v___y_4054_, v___y_4055_, v___y_4049_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v_nargs_4064_; lean_object* v___x_4065_; lean_object* v_dummy_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
v_nargs_4064_ = l_Lean_Expr_getAppNumArgs(v___y_4050_);
v___x_4065_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4066_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_4064_);
v___x_4067_ = lean_mk_array(v_nargs_4064_, v_dummy_4066_);
v___x_4068_ = lean_unsigned_to_nat(1u);
v___x_4069_ = lean_nat_sub(v_nargs_4064_, v___x_4068_);
lean_dec(v_nargs_4064_);
v___x_4070_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_4050_, v___x_4067_, v___x_4069_);
v___x_4071_ = lean_array_push(v___x_4070_, v_a_4061_);
v___x_4072_ = l_Lean_mkAppN(v___x_4065_, v___x_4071_);
lean_dec_ref(v___x_4071_);
lean_inc(v_val_3898_);
v___x_4073_ = l_Lean_LocalDecl_toExpr(v_val_3898_);
v___x_4074_ = l_Lean_Meta_mkAbsurd(v_a_4063_, v___x_4073_, v___x_4072_, v___y_4051_, v___y_4054_, v___y_4055_, v___y_4049_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4094_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4077_ = v___x_4074_;
v_isShared_4078_ = v_isSharedCheck_4094_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4074_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4094_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4079_; 
lean_inc(v_mvarId_3867_);
v___x_4079_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3867_, v_a_4075_, v___y_4054_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4091_; 
lean_dec_ref(v___x_4018_);
lean_dec(v_val_3898_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4091_ == 0)
{
lean_object* v_unused_4092_; 
v_unused_4092_ = lean_ctor_get(v___x_4079_, 0);
lean_dec(v_unused_4092_);
v___x_4081_ = v___x_4079_;
v_isShared_4082_ = v_isSharedCheck_4091_;
goto v_resetjp_4080_;
}
else
{
lean_dec(v___x_4079_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4091_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v___x_4085_; 
v___x_4083_ = lean_box(v___x_3877_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set_tag(v___x_4081_, 1);
lean_ctor_set(v___x_4081_, 0, v___x_4083_);
v___x_4085_ = v___x_4081_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4083_);
v___x_4085_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
lean_ctor_set(v___x_4086_, 1, v___x_3902_);
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 0, v___x_4086_);
v___x_4088_ = v___x_4077_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
v_a_3884_ = v___x_4088_;
goto v___jp_3883_;
}
}
}
}
else
{
lean_object* v_a_4093_; 
lean_del_object(v___x_4077_);
v_a_4093_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4093_);
lean_dec_ref_known(v___x_4079_, 1);
v___y_4039_ = v___y_4049_;
v___y_4040_ = v___y_4051_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4054_;
v___y_4043_ = v___y_4053_;
v___y_4044_ = v___y_4055_;
v_a_4045_ = v_a_4093_;
goto v___jp_4038_;
}
}
}
else
{
lean_object* v_a_4095_; 
v_a_4095_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4074_, 1);
v___y_4039_ = v___y_4049_;
v___y_4040_ = v___y_4051_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4054_;
v___y_4043_ = v___y_4053_;
v___y_4044_ = v___y_4055_;
v_a_4045_ = v_a_4095_;
goto v___jp_4038_;
}
}
else
{
lean_object* v_a_4096_; 
lean_dec(v_a_4061_);
lean_dec_ref(v___y_4050_);
v_a_4096_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4062_, 1);
v___y_4039_ = v___y_4049_;
v___y_4040_ = v___y_4051_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4054_;
v___y_4043_ = v___y_4053_;
v___y_4044_ = v___y_4055_;
v_a_4045_ = v_a_4096_;
goto v___jp_4038_;
}
}
else
{
lean_object* v_a_4097_; 
lean_dec_ref(v___y_4050_);
v_a_4097_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4060_, 1);
v___y_4039_ = v___y_4049_;
v___y_4040_ = v___y_4051_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4054_;
v___y_4043_ = v___y_4053_;
v___y_4044_ = v___y_4055_;
v_a_4045_ = v_a_4097_;
goto v___jp_4038_;
}
}
}
else
{
lean_object* v_a_4098_; 
lean_dec_ref(v___y_4050_);
v_a_4098_ = lean_ctor_get(v___y_4056_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___y_4056_, 1);
v___y_4039_ = v___y_4049_;
v___y_4040_ = v___y_4051_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4054_;
v___y_4043_ = v___y_4053_;
v___y_4044_ = v___y_4055_;
v_a_4045_ = v_a_4098_;
goto v___jp_4038_;
}
}
v___jp_4099_:
{
lean_object* v___x_4106_; 
lean_inc_ref(v___x_4018_);
v___x_4106_ = l_Lean_Meta_mkDecide(v___x_4018_, v___y_4101_, v___y_4104_, v___y_4105_, v___y_4100_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4108_; uint8_t v_transparency_4109_; uint8_t v___x_4110_; uint8_t v___x_4111_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___x_4106_, 1);
v___x_4108_ = l_Lean_Meta_Context_config(v___y_4101_);
v_transparency_4109_ = lean_ctor_get_uint8(v___x_4108_, 9);
lean_dec_ref(v___x_4108_);
v___x_4110_ = 1;
v___x_4111_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4109_, v___x_4110_);
if (v___x_4111_ == 0)
{
lean_object* v_keyedConfig_4112_; uint8_t v_trackZetaDelta_4113_; lean_object* v_zetaDeltaSet_4114_; lean_object* v_lctx_4115_; lean_object* v_localInstances_4116_; lean_object* v_defEqCtx_x3f_4117_; lean_object* v_synthPendingDepth_4118_; lean_object* v_customCanUnfoldPredicate_x3f_4119_; uint8_t v_univApprox_4120_; uint8_t v_inTypeClassResolution_4121_; uint8_t v_cacheInferType_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v_keyedConfig_4112_ = lean_ctor_get(v___y_4101_, 0);
v_trackZetaDelta_4113_ = lean_ctor_get_uint8(v___y_4101_, sizeof(void*)*7);
v_zetaDeltaSet_4114_ = lean_ctor_get(v___y_4101_, 1);
v_lctx_4115_ = lean_ctor_get(v___y_4101_, 2);
v_localInstances_4116_ = lean_ctor_get(v___y_4101_, 3);
v_defEqCtx_x3f_4117_ = lean_ctor_get(v___y_4101_, 4);
v_synthPendingDepth_4118_ = lean_ctor_get(v___y_4101_, 5);
v_customCanUnfoldPredicate_x3f_4119_ = lean_ctor_get(v___y_4101_, 6);
v_univApprox_4120_ = lean_ctor_get_uint8(v___y_4101_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4121_ = lean_ctor_get_uint8(v___y_4101_, sizeof(void*)*7 + 2);
v_cacheInferType_4122_ = lean_ctor_get_uint8(v___y_4101_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4112_);
v___x_4123_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4110_, v_keyedConfig_4112_);
lean_inc(v_customCanUnfoldPredicate_x3f_4119_);
lean_inc(v_synthPendingDepth_4118_);
lean_inc(v_defEqCtx_x3f_4117_);
lean_inc_ref(v_localInstances_4116_);
lean_inc_ref(v_lctx_4115_);
lean_inc(v_zetaDeltaSet_4114_);
v___x_4124_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
lean_ctor_set(v___x_4124_, 1, v_zetaDeltaSet_4114_);
lean_ctor_set(v___x_4124_, 2, v_lctx_4115_);
lean_ctor_set(v___x_4124_, 3, v_localInstances_4116_);
lean_ctor_set(v___x_4124_, 4, v_defEqCtx_x3f_4117_);
lean_ctor_set(v___x_4124_, 5, v_synthPendingDepth_4118_);
lean_ctor_set(v___x_4124_, 6, v_customCanUnfoldPredicate_x3f_4119_);
lean_ctor_set_uint8(v___x_4124_, sizeof(void*)*7, v_trackZetaDelta_4113_);
lean_ctor_set_uint8(v___x_4124_, sizeof(void*)*7 + 1, v_univApprox_4120_);
lean_ctor_set_uint8(v___x_4124_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4121_);
lean_ctor_set_uint8(v___x_4124_, sizeof(void*)*7 + 3, v_cacheInferType_4122_);
lean_inc(v___y_4100_);
lean_inc_ref(v___y_4105_);
lean_inc(v___y_4104_);
lean_inc(v_a_4107_);
v___x_4125_ = lean_whnf(v_a_4107_, v___x_4124_, v___y_4104_, v___y_4105_, v___y_4100_);
v___y_4049_ = v___y_4100_;
v___y_4050_ = v_a_4107_;
v___y_4051_ = v___y_4101_;
v___y_4052_ = v___y_4102_;
v___y_4053_ = v___y_4103_;
v___y_4054_ = v___y_4104_;
v___y_4055_ = v___y_4105_;
v___y_4056_ = v___x_4125_;
goto v___jp_4048_;
}
else
{
lean_object* v___x_4126_; 
lean_inc(v___y_4100_);
lean_inc_ref(v___y_4105_);
lean_inc(v___y_4104_);
lean_inc_ref(v___y_4101_);
lean_inc(v_a_4107_);
v___x_4126_ = lean_whnf(v_a_4107_, v___y_4101_, v___y_4104_, v___y_4105_, v___y_4100_);
v___y_4049_ = v___y_4100_;
v___y_4050_ = v_a_4107_;
v___y_4051_ = v___y_4101_;
v___y_4052_ = v___y_4102_;
v___y_4053_ = v___y_4103_;
v___y_4054_ = v___y_4104_;
v___y_4055_ = v___y_4105_;
v___y_4056_ = v___x_4126_;
goto v___jp_4048_;
}
}
else
{
lean_object* v_a_4127_; 
v_a_4127_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4106_, 1);
v___y_4039_ = v___y_4100_;
v___y_4040_ = v___y_4101_;
v___y_4041_ = v___y_4102_;
v___y_4042_ = v___y_4104_;
v___y_4043_ = v___y_4103_;
v___y_4044_ = v___y_4105_;
v_a_4045_ = v_a_4127_;
goto v___jp_4038_;
}
}
v___jp_4128_:
{
if (v___y_4135_ == 0)
{
v___y_4020_ = v___y_4131_;
v___y_4021_ = v___y_4132_;
v___y_4022_ = v___y_4130_;
v___y_4023_ = v___y_4133_;
v___y_4024_ = v___y_4134_;
v___y_4025_ = v___y_4129_;
goto v___jp_4019_;
}
else
{
v___y_4100_ = v___y_4129_;
v___y_4101_ = v___y_4130_;
v___y_4102_ = v___y_4131_;
v___y_4103_ = v___y_4132_;
v___y_4104_ = v___y_4133_;
v___y_4105_ = v___y_4134_;
goto v___jp_4099_;
}
}
v___jp_4136_:
{
if (v___y_4144_ == 0)
{
lean_dec_ref(v___y_4138_);
v___y_4129_ = v___y_4137_;
v___y_4130_ = v___y_4139_;
v___y_4131_ = v___y_4140_;
v___y_4132_ = v___y_4142_;
v___y_4133_ = v___y_4141_;
v___y_4134_ = v___y_4143_;
v___y_4135_ = v___x_3973_;
goto v___jp_4128_;
}
else
{
uint8_t v___x_4145_; 
v___x_4145_ = l_Lean_Expr_hasFVar(v___y_4138_);
lean_dec_ref(v___y_4138_);
if (v___x_4145_ == 0)
{
v___y_4100_ = v___y_4137_;
v___y_4101_ = v___y_4139_;
v___y_4102_ = v___y_4140_;
v___y_4103_ = v___y_4142_;
v___y_4104_ = v___y_4141_;
v___y_4105_ = v___y_4143_;
goto v___jp_4099_;
}
else
{
v___y_4129_ = v___y_4137_;
v___y_4130_ = v___y_4139_;
v___y_4131_ = v___y_4140_;
v___y_4132_ = v___y_4142_;
v___y_4133_ = v___y_4141_;
v___y_4134_ = v___y_4143_;
v___y_4135_ = v___x_3973_;
goto v___jp_4128_;
}
}
}
v___jp_4146_:
{
lean_object* v___x_4154_; 
lean_inc_ref(v___x_4018_);
v___x_4154_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4018_, v___y_4151_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; uint8_t v___x_4156_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v___x_4156_ = l_Lean_Expr_hasMVar(v_a_4155_);
if (v___x_4156_ == 0)
{
v___y_4137_ = v___y_4147_;
v___y_4138_ = v_a_4155_;
v___y_4139_ = v___y_4148_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___y_4151_;
v___y_4142_ = v___y_4150_;
v___y_4143_ = v___y_4152_;
v___y_4144_ = v___y_4153_;
goto v___jp_4136_;
}
else
{
v___y_4137_ = v___y_4147_;
v___y_4138_ = v_a_4155_;
v___y_4139_ = v___y_4148_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___y_4151_;
v___y_4142_ = v___y_4150_;
v___y_4143_ = v___y_4152_;
v___y_4144_ = v___x_3973_;
goto v___jp_4136_;
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec_ref(v___x_4018_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4157_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4154_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4154_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
v___jp_4165_:
{
if (v___y_4172_ == 0)
{
v___y_4020_ = v___y_4168_;
v___y_4021_ = v___y_4169_;
v___y_4022_ = v___y_4167_;
v___y_4023_ = v___y_4170_;
v___y_4024_ = v___y_4171_;
v___y_4025_ = v___y_4166_;
goto v___jp_4019_;
}
else
{
v___y_4147_ = v___y_4166_;
v___y_4148_ = v___y_4167_;
v___y_4149_ = v___y_4168_;
v___y_4150_ = v___y_4169_;
v___y_4151_ = v___y_4170_;
v___y_4152_ = v___y_4171_;
v___y_4153_ = v___y_4172_;
goto v___jp_4146_;
}
}
v___jp_4173_:
{
uint8_t v_useDecide_4180_; 
v_useDecide_4180_ = lean_ctor_get_uint8(v_config_3866_, sizeof(void*)*1);
if (v_useDecide_4180_ == 0)
{
v___y_4166_ = v___y_4179_;
v___y_4167_ = v___y_4176_;
v___y_4168_ = v_isHEq_4175_;
v___y_4169_ = v___y_4174_;
v___y_4170_ = v___y_4177_;
v___y_4171_ = v___y_4178_;
v___y_4172_ = v___x_3973_;
goto v___jp_4165_;
}
else
{
uint8_t v___x_4181_; 
v___x_4181_ = l_Lean_Expr_hasFVar(v___x_4018_);
if (v___x_4181_ == 0)
{
v___y_4147_ = v___y_4179_;
v___y_4148_ = v___y_4176_;
v___y_4149_ = v_isHEq_4175_;
v___y_4150_ = v___y_4174_;
v___y_4151_ = v___y_4177_;
v___y_4152_ = v___y_4178_;
v___y_4153_ = v_useDecide_4180_;
goto v___jp_4146_;
}
else
{
v___y_4166_ = v___y_4179_;
v___y_4167_ = v___y_4176_;
v___y_4168_ = v_isHEq_4175_;
v___y_4169_ = v___y_4174_;
v___y_4170_ = v___y_4177_;
v___y_4171_ = v___y_4178_;
v___y_4172_ = v___x_3973_;
goto v___jp_4165_;
}
}
}
v___jp_4182_:
{
lean_object* v___x_4190_; 
v___x_4190_ = l_Lean_Meta_isExprDefEq(v___y_4188_, v___y_4187_, v___y_4186_, v___y_4185_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; uint8_t v___x_4192_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
lean_dec_ref_known(v___x_4190_, 1);
v___x_4192_ = lean_unbox(v_a_4191_);
lean_dec(v_a_4191_);
if (v___x_4192_ == 0)
{
v___y_4174_ = v___y_4189_;
v_isHEq_4175_ = v___x_3877_;
v___y_4176_ = v___y_4186_;
v___y_4177_ = v___y_4185_;
v___y_4178_ = v___y_4183_;
v___y_4179_ = v___y_4184_;
goto v___jp_4173_;
}
else
{
lean_object* v___x_4193_; 
lean_dec_ref(v___x_4018_);
lean_dec_ref(v_config_3866_);
lean_inc(v_mvarId_3867_);
v___x_4193_ = l_Lean_MVarId_getType(v_mvarId_3867_, v___y_4186_, v___y_4185_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
lean_dec_ref_known(v___x_4193_, 1);
v___x_4195_ = l_Lean_LocalDecl_toExpr(v_val_3898_);
v___x_4196_ = l_Lean_Meta_mkEqOfHEq(v___x_4195_, v___x_3877_, v___y_4186_, v___y_4185_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4198_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___x_4198_ = l_Lean_Meta_mkNoConfusion(v_a_4194_, v_a_4197_, v___y_4186_, v___y_4185_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4200_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v___x_4200_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3867_, v_a_4199_, v___y_4185_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_dec_ref_known(v___x_4200_, 1);
v___x_4201_ = lean_box(v___x_3877_);
v___x_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
lean_ctor_set(v___x_4203_, 1, v___x_3902_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
v_a_3884_ = v___x_4204_;
goto v___jp_3883_;
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
v_a_4205_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4200_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4200_);
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
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4213_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4198_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4198_);
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
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec(v_a_4194_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4221_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4196_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4196_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4229_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4193_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4193_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v___x_4018_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4237_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4190_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4190_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
v___jp_4245_:
{
lean_object* v___x_4251_; 
lean_inc_ref(v___x_4018_);
v___x_4251_ = l_Lean_Meta_matchHEq_x3f(v___x_4018_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___x_4251_, 1);
if (lean_obj_tag(v_a_4252_) == 1)
{
lean_object* v_val_4253_; lean_object* v_snd_4254_; lean_object* v_snd_4255_; lean_object* v_fst_4256_; lean_object* v_fst_4257_; lean_object* v_fst_4258_; lean_object* v_snd_4259_; lean_object* v___x_4260_; 
v_val_4253_ = lean_ctor_get(v_a_4252_, 0);
lean_inc(v_val_4253_);
lean_dec_ref_known(v_a_4252_, 1);
v_snd_4254_ = lean_ctor_get(v_val_4253_, 1);
lean_inc(v_snd_4254_);
v_snd_4255_ = lean_ctor_get(v_snd_4254_, 1);
lean_inc(v_snd_4255_);
v_fst_4256_ = lean_ctor_get(v_val_4253_, 0);
lean_inc(v_fst_4256_);
lean_dec(v_val_4253_);
v_fst_4257_ = lean_ctor_get(v_snd_4254_, 0);
lean_inc(v_fst_4257_);
lean_dec(v_snd_4254_);
v_fst_4258_ = lean_ctor_get(v_snd_4255_, 0);
lean_inc(v_fst_4258_);
v_snd_4259_ = lean_ctor_get(v_snd_4255_, 1);
lean_inc(v_snd_4259_);
lean_dec(v_snd_4255_);
v___x_4260_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4257_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___x_4260_, 1);
if (lean_obj_tag(v_a_4261_) == 1)
{
lean_object* v_val_4262_; lean_object* v___x_4263_; 
v_val_4262_ = lean_ctor_get(v_a_4261_, 0);
lean_inc(v_val_4262_);
lean_dec_ref_known(v_a_4261_, 1);
v___x_4263_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4259_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
lean_dec_ref_known(v___x_4263_, 1);
if (lean_obj_tag(v_a_4264_) == 1)
{
lean_object* v_toConstantVal_4265_; lean_object* v_val_4266_; lean_object* v_toConstantVal_4267_; lean_object* v_name_4268_; lean_object* v_name_4269_; uint8_t v___x_4270_; 
v_toConstantVal_4265_ = lean_ctor_get(v_val_4262_, 0);
lean_inc_ref(v_toConstantVal_4265_);
lean_dec(v_val_4262_);
v_val_4266_ = lean_ctor_get(v_a_4264_, 0);
lean_inc(v_val_4266_);
lean_dec_ref_known(v_a_4264_, 1);
v_toConstantVal_4267_ = lean_ctor_get(v_val_4266_, 0);
lean_inc_ref(v_toConstantVal_4267_);
lean_dec(v_val_4266_);
v_name_4268_ = lean_ctor_get(v_toConstantVal_4265_, 0);
lean_inc(v_name_4268_);
lean_dec_ref(v_toConstantVal_4265_);
v_name_4269_ = lean_ctor_get(v_toConstantVal_4267_, 0);
lean_inc(v_name_4269_);
lean_dec_ref(v_toConstantVal_4267_);
v___x_4270_ = lean_name_eq(v_name_4268_, v_name_4269_);
lean_dec(v_name_4269_);
lean_dec(v_name_4268_);
if (v___x_4270_ == 0)
{
v___y_4183_ = v___y_4249_;
v___y_4184_ = v___y_4250_;
v___y_4185_ = v___y_4248_;
v___y_4186_ = v___y_4247_;
v___y_4187_ = v_fst_4258_;
v___y_4188_ = v_fst_4256_;
v___y_4189_ = v_isEq_4246_;
goto v___jp_4182_;
}
else
{
if (v___x_3973_ == 0)
{
lean_dec(v_fst_4258_);
lean_dec(v_fst_4256_);
v___y_4174_ = v_isEq_4246_;
v_isHEq_4175_ = v___x_3877_;
v___y_4176_ = v___y_4247_;
v___y_4177_ = v___y_4248_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
goto v___jp_4173_;
}
else
{
v___y_4183_ = v___y_4249_;
v___y_4184_ = v___y_4250_;
v___y_4185_ = v___y_4248_;
v___y_4186_ = v___y_4247_;
v___y_4187_ = v_fst_4258_;
v___y_4188_ = v_fst_4256_;
v___y_4189_ = v_isEq_4246_;
goto v___jp_4182_;
}
}
}
else
{
lean_dec(v_a_4264_);
lean_dec(v_val_4262_);
lean_dec(v_fst_4258_);
lean_dec(v_fst_4256_);
v___y_4174_ = v_isEq_4246_;
v_isHEq_4175_ = v___x_3877_;
v___y_4176_ = v___y_4247_;
v___y_4177_ = v___y_4248_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
goto v___jp_4173_;
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec(v_val_4262_);
lean_dec(v_fst_4258_);
lean_dec(v_fst_4256_);
lean_dec_ref(v___x_4018_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4271_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4263_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4263_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
else
{
lean_dec(v_a_4261_);
lean_dec(v_snd_4259_);
lean_dec(v_fst_4258_);
lean_dec(v_fst_4256_);
v___y_4174_ = v_isEq_4246_;
v_isHEq_4175_ = v___x_3877_;
v___y_4176_ = v___y_4247_;
v___y_4177_ = v___y_4248_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
goto v___jp_4173_;
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
lean_dec(v_snd_4259_);
lean_dec(v_fst_4258_);
lean_dec(v_fst_4256_);
lean_dec_ref(v___x_4018_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4279_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4260_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4260_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
else
{
lean_dec(v_a_4252_);
v___y_4174_ = v_isEq_4246_;
v_isHEq_4175_ = v___x_3973_;
v___y_4176_ = v___y_4247_;
v___y_4177_ = v___y_4248_;
v___y_4178_ = v___y_4249_;
v___y_4179_ = v___y_4250_;
goto v___jp_4173_;
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec_ref(v___x_4018_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4287_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4251_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4251_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
v___jp_4295_:
{
lean_object* v___x_4300_; 
lean_inc_ref(v___x_4018_);
v___x_4300_ = l_Lean_Meta_matchEq_x3f(v___x_4018_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v___x_4300_, 1);
if (lean_obj_tag(v_a_4301_) == 1)
{
lean_object* v_val_4302_; lean_object* v_snd_4303_; lean_object* v_fst_4304_; lean_object* v_snd_4305_; lean_object* v___x_4306_; 
v_val_4302_ = lean_ctor_get(v_a_4301_, 0);
lean_inc(v_val_4302_);
lean_dec_ref_known(v_a_4301_, 1);
v_snd_4303_ = lean_ctor_get(v_val_4302_, 1);
lean_inc(v_snd_4303_);
lean_dec(v_val_4302_);
v_fst_4304_ = lean_ctor_get(v_snd_4303_, 0);
lean_inc(v_fst_4304_);
v_snd_4305_ = lean_ctor_get(v_snd_4303_, 1);
lean_inc(v_snd_4305_);
lean_dec(v_snd_4303_);
v___x_4306_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4304_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
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
v___x_4309_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4305_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
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
lean_dec_ref(v___x_4018_);
lean_dec_ref(v_config_3866_);
v___y_3904_ = v___y_4298_;
v___y_3905_ = v___y_4296_;
v___y_3906_ = v___y_4297_;
v___y_3907_ = v___y_4299_;
goto v___jp_3903_;
}
else
{
if (v___x_3973_ == 0)
{
lean_del_object(v___x_3900_);
v_isEq_4246_ = v___x_3877_;
v___y_4247_ = v___y_4296_;
v___y_4248_ = v___y_4297_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
goto v___jp_4245_;
}
else
{
lean_dec_ref(v___x_4018_);
lean_dec_ref(v_config_3866_);
v___y_3904_ = v___y_4298_;
v___y_3905_ = v___y_4296_;
v___y_3906_ = v___y_4297_;
v___y_3907_ = v___y_4299_;
goto v___jp_3903_;
}
}
}
else
{
lean_dec(v_a_4310_);
lean_dec(v_val_4308_);
lean_del_object(v___x_3900_);
v_isEq_4246_ = v___x_3877_;
v___y_4247_ = v___y_4296_;
v___y_4248_ = v___y_4297_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
goto v___jp_4245_;
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4324_; 
lean_dec(v_val_4308_);
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
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
lean_del_object(v___x_3900_);
v_isEq_4246_ = v___x_3877_;
v___y_4247_ = v___y_4296_;
v___y_4248_ = v___y_4297_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
goto v___jp_4245_;
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec(v_snd_4305_);
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
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
lean_dec(v_a_4301_);
lean_del_object(v___x_3900_);
v_isEq_4246_ = v___x_3973_;
v___y_4247_ = v___y_4296_;
v___y_4248_ = v___y_4297_;
v___y_4249_ = v___y_4298_;
v___y_4250_ = v___y_4299_;
goto v___jp_4245_;
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4333_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4300_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4300_);
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
lean_inc_ref(v___x_4018_);
v___x_4346_ = l_Lean_refutableHasNotBit_x3f(v___x_4018_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4346_, 1);
if (lean_obj_tag(v_a_4347_) == 1)
{
lean_object* v_val_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4388_; 
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec_ref(v_config_3866_);
v_val_4348_ = lean_ctor_get(v_a_4347_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_a_4347_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4350_ = v_a_4347_;
v_isShared_4351_ = v_isSharedCheck_4388_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_val_4348_);
lean_dec(v_a_4347_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4388_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; 
lean_inc(v_mvarId_3867_);
v___x_4352_ = l_Lean_MVarId_getType(v_mvarId_3867_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v___x_4354_ = l_Lean_LocalDecl_toExpr(v_val_3898_);
v___x_4355_ = l_Lean_Meta_mkAbsurd(v_a_4353_, v_val_4348_, v___x_4354_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v___x_4357_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3867_, v_a_4356_, v___y_4343_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4360_; 
lean_dec_ref_known(v___x_4357_, 1);
v___x_4358_ = lean_box(v___x_3877_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v___x_4358_);
v___x_4360_ = v___x_4350_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
lean_ctor_set(v___x_4361_, 1, v___x_3902_);
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
v_a_3884_ = v___x_4362_;
goto v___jp_3883_;
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
lean_del_object(v___x_4350_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
v_a_4364_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4357_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4357_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_del_object(v___x_4350_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4372_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4355_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4355_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_del_object(v___x_4350_);
lean_dec(v_val_4348_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4380_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4352_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4352_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
else
{
lean_object* v___x_4389_; 
lean_dec(v_a_4347_);
lean_inc_ref(v___x_4018_);
v___x_4389_ = l_Lean_Meta_matchNe_x3f(v___x_4018_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc(v_a_4390_);
lean_dec_ref_known(v___x_4389_, 1);
if (lean_obj_tag(v_a_4390_) == 1)
{
lean_object* v_val_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4461_; 
v_val_4391_ = lean_ctor_get(v_a_4390_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_a_4390_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4393_ = v_a_4390_;
v_isShared_4394_ = v_isSharedCheck_4461_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_val_4391_);
lean_dec(v_a_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4461_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v_snd_4395_; lean_object* v_fst_4396_; lean_object* v_snd_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4460_; 
v_snd_4395_ = lean_ctor_get(v_val_4391_, 1);
lean_inc(v_snd_4395_);
lean_dec(v_val_4391_);
v_fst_4396_ = lean_ctor_get(v_snd_4395_, 0);
v_snd_4397_ = lean_ctor_get(v_snd_4395_, 1);
v_isSharedCheck_4460_ = !lean_is_exclusive(v_snd_4395_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4399_ = v_snd_4395_;
v_isShared_4400_ = v_isSharedCheck_4460_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_snd_4397_);
lean_inc(v_fst_4396_);
lean_dec(v_snd_4395_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4460_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; 
lean_inc(v_fst_4396_);
v___x_4401_ = l_Lean_Meta_isExprDefEq(v_fst_4396_, v_snd_4397_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; uint8_t v___x_4403_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v___x_4403_ = lean_unbox(v_a_4402_);
lean_dec(v_a_4402_);
if (v___x_4403_ == 0)
{
lean_del_object(v___x_4399_);
lean_dec(v_fst_4396_);
lean_del_object(v___x_4393_);
v___y_4296_ = v___y_4342_;
v___y_4297_ = v___y_4343_;
v___y_4298_ = v___y_4344_;
v___y_4299_ = v___y_4345_;
goto v___jp_4295_;
}
else
{
lean_object* v___x_4404_; 
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec_ref(v_config_3866_);
lean_inc(v_mvarId_3867_);
v___x_4404_ = l_Lean_MVarId_getType(v_mvarId_3867_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v___x_4406_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4404_, 1);
v___x_4406_ = l_Lean_Meta_mkEqRefl(v_fst_4396_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
v___x_4408_ = l_Lean_LocalDecl_toExpr(v_val_3898_);
v___x_4409_ = l_Lean_Meta_mkAbsurd(v_a_4405_, v_a_4407_, v___x_4408_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3867_, v_a_4410_, v___y_4343_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v___x_4412_; lean_object* v___x_4414_; 
lean_dec_ref_known(v___x_4411_, 1);
v___x_4412_ = lean_box(v___x_3877_);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___x_4412_);
v___x_4414_ = v___x_4393_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4412_);
v___x_4414_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4416_; 
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 1, v___x_3902_);
lean_ctor_set(v___x_4399_, 0, v___x_4414_);
v___x_4416_ = v___x_4399_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4414_);
lean_ctor_set(v_reuseFailAlloc_4418_, 1, v___x_3902_);
v___x_4416_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4417_; 
v___x_4417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
v_a_3884_ = v___x_4417_;
goto v___jp_3883_;
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_del_object(v___x_4399_);
lean_del_object(v___x_4393_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
v_a_4420_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4411_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4411_);
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
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_del_object(v___x_4399_);
lean_del_object(v___x_4393_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4428_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4409_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4409_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec(v_a_4405_);
lean_del_object(v___x_4399_);
lean_del_object(v___x_4393_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4436_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4406_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4406_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_del_object(v___x_4399_);
lean_dec(v_fst_4396_);
lean_del_object(v___x_4393_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_4444_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4404_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4404_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_del_object(v___x_4399_);
lean_dec(v_fst_4396_);
lean_del_object(v___x_4393_);
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4452_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4401_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4401_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4390_);
v___y_4296_ = v___y_4342_;
v___y_4297_ = v___y_4343_;
v___y_4298_ = v___y_4344_;
v___y_4299_ = v___y_4345_;
goto v___jp_4295_;
}
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4462_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4464_ = v___x_4389_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4389_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec_ref(v___x_4018_);
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4470_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4346_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4346_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
else
{
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
v_a_3892_ = v___x_3944_;
goto v___jp_3891_;
}
v___jp_3903_:
{
lean_object* v___x_3908_; 
lean_inc(v_mvarId_3867_);
v___x_3908_ = l_Lean_MVarId_getType(v_mvarId_3867_, v___y_3905_, v___y_3906_, v___y_3904_, v___y_3907_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = l_Lean_LocalDecl_toExpr(v_val_3898_);
v___x_3911_ = l_Lean_Meta_mkNoConfusion(v_a_3909_, v___x_3910_, v___y_3905_, v___y_3906_, v___y_3904_, v___y_3907_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3867_, v_a_3912_, v___y_3906_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v___x_3914_; lean_object* v___x_3916_; 
lean_dec_ref_known(v___x_3913_, 1);
v___x_3914_ = lean_box(v___x_3877_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3914_);
v___x_3916_ = v___x_3900_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
lean_ctor_set(v___x_3917_, 1, v___x_3902_);
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
v_a_3884_ = v___x_3918_;
goto v___jp_3883_;
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_del_object(v___x_3900_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
v_a_3920_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3913_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3913_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_del_object(v___x_3900_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_3928_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3911_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3911_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_del_object(v___x_3900_);
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_3936_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3908_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3908_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
v___jp_3945_:
{
lean_object* v_searchFuel_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v_searchFuel_3950_ = lean_ctor_get(v_config_3866_, 0);
v___x_3951_ = l_Lean_LocalDecl_fvarId(v_val_3898_);
lean_dec(v_val_3898_);
lean_inc(v_searchFuel_3950_);
lean_inc(v_mvarId_3867_);
v___x_3952_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3867_, v___x_3951_, v_searchFuel_3950_, v___y_3949_, v___y_3948_, v___y_3947_, v___y_3946_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; uint8_t v___x_3954_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v___x_3954_ = lean_unbox(v_a_3953_);
lean_dec(v_a_3953_);
if (v___x_3954_ == 0)
{
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
v_a_3892_ = v___x_3944_;
goto v___jp_3891_;
}
else
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v___x_3955_ = lean_box(v___x_3877_);
v___x_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
v___x_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
lean_ctor_set(v___x_3957_, 1, v___x_3902_);
v___x_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
v_a_3884_ = v___x_3958_;
goto v___jp_3883_;
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_3959_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3952_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3952_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
v___jp_3967_:
{
if (v___y_3972_ == 0)
{
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
v_a_3892_ = v___x_3944_;
goto v___jp_3891_;
}
else
{
v___y_3946_ = v___y_3969_;
v___y_3947_ = v___y_3968_;
v___y_3948_ = v___y_3970_;
v___y_3949_ = v___y_3971_;
goto v___jp_3945_;
}
}
v___jp_3974_:
{
if (v___y_3977_ == 0)
{
v___y_3946_ = v___y_3976_;
v___y_3947_ = v___y_3975_;
v___y_3948_ = v___y_3978_;
v___y_3949_ = v___y_3979_;
goto v___jp_3945_;
}
else
{
v___y_3968_ = v___y_3975_;
v___y_3969_ = v___y_3976_;
v___y_3970_ = v___y_3978_;
v___y_3971_ = v___y_3979_;
v___y_3972_ = v___x_3973_;
goto v___jp_3967_;
}
}
v___jp_3980_:
{
if (v___y_3986_ == 0)
{
v___y_3968_ = v___y_3983_;
v___y_3969_ = v___y_3982_;
v___y_3970_ = v___y_3984_;
v___y_3971_ = v___y_3985_;
v___y_3972_ = v___x_3973_;
goto v___jp_3967_;
}
else
{
v___y_3975_ = v___y_3983_;
v___y_3976_ = v___y_3982_;
v___y_3977_ = v___y_3981_;
v___y_3978_ = v___y_3984_;
v___y_3979_ = v___y_3985_;
goto v___jp_3974_;
}
}
v___jp_3987_:
{
uint8_t v_emptyType_3994_; 
v_emptyType_3994_ = lean_ctor_get_uint8(v_config_3866_, sizeof(void*)*1 + 1);
if (v_emptyType_3994_ == 0)
{
v___y_3981_ = v___y_3988_;
v___y_3982_ = v___y_3993_;
v___y_3983_ = v___y_3992_;
v___y_3984_ = v___y_3991_;
v___y_3985_ = v___y_3990_;
v___y_3986_ = v___x_3973_;
goto v___jp_3980_;
}
else
{
if (v___y_3989_ == 0)
{
v___y_3975_ = v___y_3992_;
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___y_3988_;
v___y_3978_ = v___y_3991_;
v___y_3979_ = v___y_3990_;
goto v___jp_3974_;
}
else
{
v___y_3981_ = v___y_3988_;
v___y_3982_ = v___y_3993_;
v___y_3983_ = v___y_3992_;
v___y_3984_ = v___y_3991_;
v___y_3985_ = v___y_3990_;
v___y_3986_ = v___x_3973_;
goto v___jp_3980_;
}
}
}
v___jp_3995_:
{
if (v___y_4002_ == 0)
{
v___y_3988_ = v___y_4000_;
v___y_3989_ = v___y_4001_;
v___y_3990_ = v___y_3999_;
v___y_3991_ = v___y_3998_;
v___y_3992_ = v___y_3997_;
v___y_3993_ = v___y_3996_;
goto v___jp_3987_;
}
else
{
lean_object* v___x_4003_; 
lean_inc(v_val_3898_);
lean_inc(v_mvarId_3867_);
v___x_4003_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3867_, v_val_3898_, v___y_3999_, v___y_3998_, v___y_3997_, v___y_3996_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; uint8_t v___x_4005_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
v___x_4005_ = lean_unbox(v_a_4004_);
lean_dec(v_a_4004_);
if (v___x_4005_ == 0)
{
v___y_3988_ = v___y_4000_;
v___y_3989_ = v___y_4001_;
v___y_3990_ = v___y_3999_;
v___y_3991_ = v___y_3998_;
v___y_3992_ = v___y_3997_;
v___y_3993_ = v___y_3996_;
goto v___jp_3987_;
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec(v_val_3898_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v___x_4006_ = lean_box(v___x_3877_);
v___x_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
v___x_4008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
lean_ctor_set(v___x_4008_, 1, v___x_3902_);
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
v_a_3884_ = v___x_4009_;
goto v___jp_3883_;
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v_val_3898_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
lean_dec_ref(v_config_3866_);
v_a_4010_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4003_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4003_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
}
}
}
v___jp_3883_:
{
lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3885_, 0, v_a_3884_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v___x_3885_);
v___x_3887_ = v___x_3881_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_snd_3879_);
v___x_3887_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
return v___x_3888_;
}
}
v___jp_3891_:
{
lean_object* v___x_3893_; size_t v___x_3894_; size_t v___x_3895_; lean_object* v___x_3896_; 
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3890_);
lean_ctor_set(v___x_3893_, 1, v_a_3892_);
v___x_3894_ = ((size_t)1ULL);
v___x_3895_ = lean_usize_add(v_i_3870_, v___x_3894_);
v___x_3896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3866_, v_mvarId_3867_, v_as_3868_, v_sz_3869_, v___x_3895_, v___x_3893_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
return v___x_3896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4551_, lean_object* v_mvarId_4552_, lean_object* v_as_4553_, lean_object* v_sz_4554_, lean_object* v_i_4555_, lean_object* v_b_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
size_t v_sz_boxed_4562_; size_t v_i_boxed_4563_; lean_object* v_res_4564_; 
v_sz_boxed_4562_ = lean_unbox_usize(v_sz_4554_);
lean_dec(v_sz_4554_);
v_i_boxed_4563_ = lean_unbox_usize(v_i_4555_);
lean_dec(v_i_4555_);
v_res_4564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4551_, v_mvarId_4552_, v_as_4553_, v_sz_boxed_4562_, v_i_boxed_4563_, v_b_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec_ref(v_as_4553_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4565_, lean_object* v_config_4566_, lean_object* v_mvarId_4567_, lean_object* v_n_4568_, lean_object* v_b_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
if (lean_obj_tag(v_n_4568_) == 0)
{
lean_object* v_cs_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; size_t v_sz_4578_; size_t v___x_4579_; lean_object* v___x_4580_; 
v_cs_4575_ = lean_ctor_get(v_n_4568_, 0);
v___x_4576_ = lean_box(0);
v___x_4577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
lean_ctor_set(v___x_4577_, 1, v_b_4569_);
v_sz_4578_ = lean_array_size(v_cs_4575_);
v___x_4579_ = ((size_t)0ULL);
v___x_4580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4565_, v_config_4566_, v_mvarId_4567_, v_cs_4575_, v_sz_4578_, v___x_4579_, v___x_4577_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4595_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4583_ = v___x_4580_;
v_isShared_4584_ = v_isSharedCheck_4595_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4580_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4595_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v_fst_4585_; 
v_fst_4585_ = lean_ctor_get(v_a_4581_, 0);
if (lean_obj_tag(v_fst_4585_) == 0)
{
lean_object* v_snd_4586_; lean_object* v___x_4587_; lean_object* v___x_4589_; 
v_snd_4586_ = lean_ctor_get(v_a_4581_, 1);
lean_inc(v_snd_4586_);
lean_dec(v_a_4581_);
v___x_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4587_, 0, v_snd_4586_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4587_);
v___x_4589_ = v___x_4583_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4587_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
else
{
lean_object* v_val_4591_; lean_object* v___x_4593_; 
lean_inc_ref(v_fst_4585_);
lean_dec(v_a_4581_);
v_val_4591_ = lean_ctor_get(v_fst_4585_, 0);
lean_inc(v_val_4591_);
lean_dec_ref_known(v_fst_4585_, 1);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v_val_4591_);
v___x_4593_ = v___x_4583_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_val_4591_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
v_a_4596_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4580_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4580_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
else
{
lean_object* v_vs_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; size_t v_sz_4607_; size_t v___x_4608_; lean_object* v___x_4609_; 
v_vs_4604_ = lean_ctor_get(v_n_4568_, 0);
v___x_4605_ = lean_box(0);
v___x_4606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
lean_ctor_set(v___x_4606_, 1, v_b_4569_);
v_sz_4607_ = lean_array_size(v_vs_4604_);
v___x_4608_ = ((size_t)0ULL);
v___x_4609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4566_, v_mvarId_4567_, v_vs_4604_, v_sz_4607_, v___x_4608_, v___x_4606_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4624_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4624_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4624_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v_fst_4614_; 
v_fst_4614_ = lean_ctor_get(v_a_4610_, 0);
if (lean_obj_tag(v_fst_4614_) == 0)
{
lean_object* v_snd_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
v_snd_4615_ = lean_ctor_get(v_a_4610_, 1);
lean_inc(v_snd_4615_);
lean_dec(v_a_4610_);
v___x_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4616_, 0, v_snd_4615_);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v___x_4616_);
v___x_4618_ = v___x_4612_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4616_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
else
{
lean_object* v_val_4620_; lean_object* v___x_4622_; 
lean_inc_ref(v_fst_4614_);
lean_dec(v_a_4610_);
v_val_4620_ = lean_ctor_get(v_fst_4614_, 0);
lean_inc(v_val_4620_);
lean_dec_ref_known(v_fst_4614_, 1);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v_val_4620_);
v___x_4622_ = v___x_4612_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_val_4620_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
v_a_4625_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4609_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4609_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4633_, lean_object* v_config_4634_, lean_object* v_mvarId_4635_, lean_object* v_as_4636_, size_t v_sz_4637_, size_t v_i_4638_, lean_object* v_b_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
uint8_t v___x_4645_; 
v___x_4645_ = lean_usize_dec_lt(v_i_4638_, v_sz_4637_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; 
lean_dec(v_mvarId_4635_);
lean_dec_ref(v_config_4634_);
v___x_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4646_, 0, v_b_4639_);
return v___x_4646_;
}
else
{
lean_object* v_snd_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4681_; 
v_snd_4647_ = lean_ctor_get(v_b_4639_, 1);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_b_4639_);
if (v_isSharedCheck_4681_ == 0)
{
lean_object* v_unused_4682_; 
v_unused_4682_ = lean_ctor_get(v_b_4639_, 0);
lean_dec(v_unused_4682_);
v___x_4649_ = v_b_4639_;
v_isShared_4650_ = v_isSharedCheck_4681_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_snd_4647_);
lean_dec(v_b_4639_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4681_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v_a_4651_; lean_object* v___x_4652_; 
v_a_4651_ = lean_array_uget_borrowed(v_as_4636_, v_i_4638_);
lean_inc(v_snd_4647_);
lean_inc(v_mvarId_4635_);
lean_inc_ref(v_config_4634_);
v___x_4652_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4633_, v_config_4634_, v_mvarId_4635_, v_a_4651_, v_snd_4647_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4672_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4655_ = v___x_4652_;
v_isShared_4656_ = v_isSharedCheck_4672_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4652_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4672_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
if (lean_obj_tag(v_a_4653_) == 0)
{
lean_object* v___x_4657_; lean_object* v___x_4659_; 
lean_dec(v_mvarId_4635_);
lean_dec_ref(v_config_4634_);
v___x_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4657_, 0, v_a_4653_);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 0, v___x_4657_);
v___x_4659_ = v___x_4649_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_snd_4647_);
v___x_4659_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4661_; 
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v___x_4659_);
v___x_4661_ = v___x_4655_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4659_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4665_; lean_object* v___x_4667_; 
lean_del_object(v___x_4655_);
lean_dec(v_snd_4647_);
v_a_4664_ = lean_ctor_get(v_a_4653_, 0);
lean_inc(v_a_4664_);
lean_dec_ref_known(v_a_4653_, 1);
v___x_4665_ = lean_box(0);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 1, v_a_4664_);
lean_ctor_set(v___x_4649_, 0, v___x_4665_);
v___x_4667_ = v___x_4649_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4665_);
lean_ctor_set(v_reuseFailAlloc_4671_, 1, v_a_4664_);
v___x_4667_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
size_t v___x_4668_; size_t v___x_4669_; 
v___x_4668_ = ((size_t)1ULL);
v___x_4669_ = lean_usize_add(v_i_4638_, v___x_4668_);
v_i_4638_ = v___x_4669_;
v_b_4639_ = v___x_4667_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
lean_del_object(v___x_4649_);
lean_dec(v_snd_4647_);
lean_dec(v_mvarId_4635_);
lean_dec_ref(v_config_4634_);
v_a_4673_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4652_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4652_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4683_, lean_object* v_config_4684_, lean_object* v_mvarId_4685_, lean_object* v_as_4686_, lean_object* v_sz_4687_, lean_object* v_i_4688_, lean_object* v_b_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
size_t v_sz_boxed_4695_; size_t v_i_boxed_4696_; lean_object* v_res_4697_; 
v_sz_boxed_4695_ = lean_unbox_usize(v_sz_4687_);
lean_dec(v_sz_4687_);
v_i_boxed_4696_ = lean_unbox_usize(v_i_4688_);
lean_dec(v_i_4688_);
v_res_4697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4683_, v_config_4684_, v_mvarId_4685_, v_as_4686_, v_sz_boxed_4695_, v_i_boxed_4696_, v_b_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec_ref(v_as_4686_);
lean_dec_ref(v_init_4683_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4698_, lean_object* v_config_4699_, lean_object* v_mvarId_4700_, lean_object* v_n_4701_, lean_object* v_b_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4698_, v_config_4699_, v_mvarId_4700_, v_n_4701_, v_b_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec_ref(v_n_4701_);
lean_dec_ref(v_init_4698_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4709_, lean_object* v_mvarId_4710_, lean_object* v_t_4711_, lean_object* v_init_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v_root_4718_; lean_object* v_tail_4719_; lean_object* v___x_4720_; 
v_root_4718_ = lean_ctor_get(v_t_4711_, 0);
v_tail_4719_ = lean_ctor_get(v_t_4711_, 1);
lean_inc(v_mvarId_4710_);
lean_inc_ref(v_config_4709_);
lean_inc_ref(v_init_4712_);
v___x_4720_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4712_, v_config_4709_, v_mvarId_4710_, v_root_4718_, v_init_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
lean_dec_ref(v_init_4712_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4757_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4723_ = v___x_4720_;
v_isShared_4724_ = v_isSharedCheck_4757_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4720_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4757_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
if (lean_obj_tag(v_a_4721_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4727_; 
lean_dec(v_mvarId_4710_);
lean_dec_ref(v_config_4709_);
v_a_4725_ = lean_ctor_get(v_a_4721_, 0);
lean_inc(v_a_4725_);
lean_dec_ref_known(v_a_4721_, 1);
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v_a_4725_);
v___x_4727_ = v___x_4723_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4725_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; size_t v_sz_4732_; size_t v___x_4733_; lean_object* v___x_4734_; 
lean_del_object(v___x_4723_);
v_a_4729_ = lean_ctor_get(v_a_4721_, 0);
lean_inc(v_a_4729_);
lean_dec_ref_known(v_a_4721_, 1);
v___x_4730_ = lean_box(0);
v___x_4731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
lean_ctor_set(v___x_4731_, 1, v_a_4729_);
v_sz_4732_ = lean_array_size(v_tail_4719_);
v___x_4733_ = ((size_t)0ULL);
v___x_4734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4709_, v_mvarId_4710_, v_tail_4719_, v_sz_4732_, v___x_4733_, v___x_4731_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
if (lean_obj_tag(v___x_4734_) == 0)
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4748_; 
v_a_4735_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4737_ = v___x_4734_;
v_isShared_4738_ = v_isSharedCheck_4748_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4734_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4748_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v_fst_4739_; 
v_fst_4739_ = lean_ctor_get(v_a_4735_, 0);
if (lean_obj_tag(v_fst_4739_) == 0)
{
lean_object* v_snd_4740_; lean_object* v___x_4742_; 
v_snd_4740_ = lean_ctor_get(v_a_4735_, 1);
lean_inc(v_snd_4740_);
lean_dec(v_a_4735_);
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 0, v_snd_4740_);
v___x_4742_ = v___x_4737_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_snd_4740_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
else
{
lean_object* v_val_4744_; lean_object* v___x_4746_; 
lean_inc_ref(v_fst_4739_);
lean_dec(v_a_4735_);
v_val_4744_ = lean_ctor_get(v_fst_4739_, 0);
lean_inc(v_val_4744_);
lean_dec_ref_known(v_fst_4739_, 1);
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 0, v_val_4744_);
v___x_4746_ = v___x_4737_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_val_4744_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
v_a_4749_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___x_4734_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4734_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
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
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
lean_dec(v_mvarId_4710_);
lean_dec_ref(v_config_4709_);
v_a_4758_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4720_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4720_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4766_, lean_object* v_mvarId_4767_, lean_object* v_t_4768_, lean_object* v_init_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4766_, v_mvarId_4767_, v_t_4768_, v_init_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
lean_dec_ref(v_t_4768_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4776_, lean_object* v___x_4777_, lean_object* v_config_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v___x_4784_; 
lean_inc(v_mvarId_4776_);
v___x_4784_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4776_, v___x_4777_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v___x_4785_; 
lean_dec_ref_known(v___x_4784_, 1);
lean_inc(v_mvarId_4776_);
v___x_4785_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4776_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4819_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4788_ = v___x_4785_;
v_isShared_4789_ = v_isSharedCheck_4819_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4785_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4819_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
uint8_t v___x_4790_; 
v___x_4790_ = lean_unbox(v_a_4786_);
if (v___x_4790_ == 0)
{
lean_object* v_lctx_4791_; lean_object* v_decls_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_del_object(v___x_4788_);
v_lctx_4791_ = lean_ctor_get(v___y_4779_, 2);
v_decls_4792_ = lean_ctor_get(v_lctx_4791_, 1);
v___x_4793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4794_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4778_, v_mvarId_4776_, v_decls_4792_, v___x_4793_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4807_; 
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4797_ = v___x_4794_;
v_isShared_4798_ = v_isSharedCheck_4807_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4794_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4807_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v_fst_4799_; 
v_fst_4799_ = lean_ctor_get(v_a_4795_, 0);
lean_inc(v_fst_4799_);
lean_dec(v_a_4795_);
if (lean_obj_tag(v_fst_4799_) == 0)
{
lean_object* v___x_4801_; 
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 0, v_a_4786_);
v___x_4801_ = v___x_4797_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_a_4786_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
else
{
lean_object* v_val_4803_; lean_object* v___x_4805_; 
lean_dec(v_a_4786_);
v_val_4803_ = lean_ctor_get(v_fst_4799_, 0);
lean_inc(v_val_4803_);
lean_dec_ref_known(v_fst_4799_, 1);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 0, v_val_4803_);
v___x_4805_ = v___x_4797_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_val_4803_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
lean_dec(v_a_4786_);
v_a_4808_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4794_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4794_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
else
{
lean_object* v___x_4817_; 
lean_dec_ref(v_config_4778_);
lean_dec(v_mvarId_4776_);
if (v_isShared_4789_ == 0)
{
v___x_4817_ = v___x_4788_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4786_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
else
{
lean_dec_ref(v_config_4778_);
lean_dec(v_mvarId_4776_);
return v___x_4785_;
}
}
else
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4827_; 
lean_dec_ref(v_config_4778_);
lean_dec(v_mvarId_4776_);
v_a_4820_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4822_ = v___x_4784_;
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4784_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4825_; 
if (v_isShared_4823_ == 0)
{
v___x_4825_ = v___x_4822_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4828_, lean_object* v___x_4829_, lean_object* v_config_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4828_, v___x_4829_, v_config_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4839_, lean_object* v_config_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_){
_start:
{
lean_object* v___x_4846_; lean_object* v___f_4847_; lean_object* v___x_4848_; 
v___x_4846_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4839_);
v___f_4847_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4847_, 0, v_mvarId_4839_);
lean_closure_set(v___f_4847_, 1, v___x_4846_);
lean_closure_set(v___f_4847_, 2, v_config_4840_);
v___x_4848_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4839_, v___f_4847_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4849_, lean_object* v_config_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l_Lean_MVarId_contradictionCore(v_mvarId_4849_, v_config_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4857_, lean_object* v_config_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_){
_start:
{
lean_object* v___x_4864_; 
lean_inc(v_mvarId_4857_);
v___x_4864_ = l_Lean_MVarId_contradictionCore(v_mvarId_4857_, v_config_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4877_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4867_ = v___x_4864_;
v_isShared_4868_ = v_isSharedCheck_4877_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4864_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4877_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
uint8_t v___x_4869_; 
v___x_4869_ = lean_unbox(v_a_4865_);
lean_dec(v_a_4865_);
if (v___x_4869_ == 0)
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
lean_del_object(v___x_4867_);
v___x_4870_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4871_ = lean_box(0);
v___x_4872_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4870_, v_mvarId_4857_, v___x_4871_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
return v___x_4872_;
}
else
{
lean_object* v___x_4873_; lean_object* v___x_4875_; 
lean_dec(v_mvarId_4857_);
v___x_4873_ = lean_box(0);
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 0, v___x_4873_);
v___x_4875_ = v___x_4867_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4873_);
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
else
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4885_; 
lean_dec(v_mvarId_4857_);
v_a_4878_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4880_ = v___x_4864_;
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4864_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4883_; 
if (v_isShared_4881_ == 0)
{
v___x_4883_ = v___x_4880_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4878_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4886_, lean_object* v_config_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_Lean_MVarId_contradiction(v_mvarId_4886_, v_config_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
lean_dec(v_a_4889_);
lean_dec_ref(v_a_4888_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4956_; uint8_t v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4956_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4957_ = 0;
v___x_4958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4959_ = l_Lean_registerTraceClass(v___x_4956_, v___x_4957_, v___x_4958_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4961_;
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
