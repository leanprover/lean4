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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_refutableHasNotBit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "of_decide_eq_false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(101, 242, 48, 138, 187, 4, 117, 248)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8;
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
lean_object* v_ks_103_; lean_object* v_vs_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_124_; 
v_ks_103_ = lean_ctor_get(v_x_52_, 0);
v_vs_104_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_124_ == 0)
{
v___x_106_ = v_x_52_;
v_isShared_107_ = v_isSharedCheck_124_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_vs_104_);
lean_inc(v_ks_103_);
lean_dec(v_x_52_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_124_;
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
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_ks_103_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_vs_104_);
v___x_109_ = v_reuseFailAlloc_123_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v_newNode_110_; uint8_t v___y_112_; size_t v___x_118_; uint8_t v___x_119_; 
v_newNode_110_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v___x_109_, v_x_55_, v_x_56_);
v___x_118_ = ((size_t)7ULL);
v___x_119_ = lean_usize_dec_le(v___x_118_, v_x_54_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_110_);
v___x_121_ = lean_unsigned_to_nat(4u);
v___x_122_ = lean_nat_dec_lt(v___x_120_, v___x_121_);
lean_dec(v___x_120_);
v___y_112_ = v___x_122_;
goto v___jp_111_;
}
else
{
v___y_112_ = v___x_119_;
goto v___jp_111_;
}
v___jp_111_:
{
if (v___y_112_ == 0)
{
lean_object* v_ks_113_; lean_object* v_vs_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_ks_113_ = lean_ctor_get(v_newNode_110_, 0);
lean_inc_ref(v_ks_113_);
v_vs_114_ = lean_ctor_get(v_newNode_110_, 1);
lean_inc_ref(v_vs_114_);
lean_dec_ref(v_newNode_110_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_x_54_, v_ks_113_, v_vs_114_, v___x_115_, v___x_116_);
lean_dec_ref(v_vs_114_);
lean_dec_ref(v_ks_113_);
return v___x_117_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_125_, lean_object* v_keys_126_, lean_object* v_vals_127_, lean_object* v_i_128_, lean_object* v_entries_129_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_145_, lean_object* v_keys_146_, lean_object* v_vals_147_, lean_object* v_i_148_, lean_object* v_entries_149_){
_start:
{
size_t v_depth_boxed_150_; lean_object* v_res_151_; 
v_depth_boxed_150_ = lean_unbox_usize(v_depth_145_);
lean_dec(v_depth_145_);
v_res_151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_150_, v_keys_146_, v_vals_147_, v_i_148_, v_entries_149_);
lean_dec_ref(v_vals_147_);
lean_dec_ref(v_keys_146_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
size_t v_x_1108__boxed_157_; size_t v_x_1109__boxed_158_; lean_object* v_res_159_; 
v_x_1108__boxed_157_ = lean_unbox_usize(v_x_153_);
lean_dec(v_x_153_);
v_x_1109__boxed_158_ = lean_unbox_usize(v_x_154_);
lean_dec(v_x_154_);
v_res_159_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_152_, v_x_1108__boxed_157_, v_x_1109__boxed_158_, v_x_155_, v_x_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
uint64_t v___x_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; 
v___x_163_ = l_Lean_instHashableMVarId_hash(v_x_161_);
v___x_164_ = lean_uint64_to_usize(v___x_163_);
v___x_165_ = ((size_t)1ULL);
v___x_166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_160_, v___x_164_, v___x_165_, v_x_161_, v_x_162_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object* v_mvarId_167_, lean_object* v_val_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; lean_object* v_mctx_172_; lean_object* v_cache_173_; lean_object* v_zetaDeltaFVarIds_174_; lean_object* v_postponed_175_; lean_object* v_diag_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_204_; 
v___x_171_ = lean_st_ref_take(v___y_169_);
v_mctx_172_ = lean_ctor_get(v___x_171_, 0);
v_cache_173_ = lean_ctor_get(v___x_171_, 1);
v_zetaDeltaFVarIds_174_ = lean_ctor_get(v___x_171_, 2);
v_postponed_175_ = lean_ctor_get(v___x_171_, 3);
v_diag_176_ = lean_ctor_get(v___x_171_, 4);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_204_ == 0)
{
v___x_178_ = v___x_171_;
v_isShared_179_ = v_isSharedCheck_204_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_diag_176_);
lean_inc(v_postponed_175_);
lean_inc(v_zetaDeltaFVarIds_174_);
lean_inc(v_cache_173_);
lean_inc(v_mctx_172_);
lean_dec(v___x_171_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_204_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_depth_180_; lean_object* v_levelAssignDepth_181_; lean_object* v_lmvarCounter_182_; lean_object* v_mvarCounter_183_; lean_object* v_lDecls_184_; lean_object* v_decls_185_; lean_object* v_userNames_186_; lean_object* v_lAssignment_187_; lean_object* v_eAssignment_188_; lean_object* v_dAssignment_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_203_; 
v_depth_180_ = lean_ctor_get(v_mctx_172_, 0);
v_levelAssignDepth_181_ = lean_ctor_get(v_mctx_172_, 1);
v_lmvarCounter_182_ = lean_ctor_get(v_mctx_172_, 2);
v_mvarCounter_183_ = lean_ctor_get(v_mctx_172_, 3);
v_lDecls_184_ = lean_ctor_get(v_mctx_172_, 4);
v_decls_185_ = lean_ctor_get(v_mctx_172_, 5);
v_userNames_186_ = lean_ctor_get(v_mctx_172_, 6);
v_lAssignment_187_ = lean_ctor_get(v_mctx_172_, 7);
v_eAssignment_188_ = lean_ctor_get(v_mctx_172_, 8);
v_dAssignment_189_ = lean_ctor_get(v_mctx_172_, 9);
v_isSharedCheck_203_ = !lean_is_exclusive(v_mctx_172_);
if (v_isSharedCheck_203_ == 0)
{
v___x_191_ = v_mctx_172_;
v_isShared_192_ = v_isSharedCheck_203_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_dAssignment_189_);
lean_inc(v_eAssignment_188_);
lean_inc(v_lAssignment_187_);
lean_inc(v_userNames_186_);
lean_inc(v_decls_185_);
lean_inc(v_lDecls_184_);
lean_inc(v_mvarCounter_183_);
lean_inc(v_lmvarCounter_182_);
lean_inc(v_levelAssignDepth_181_);
lean_inc(v_depth_180_);
lean_dec(v_mctx_172_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_203_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_188_, v_mvarId_167_, v_val_168_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 8, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_depth_180_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_levelAssignDepth_181_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_lmvarCounter_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_mvarCounter_183_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_lDecls_184_);
lean_ctor_set(v_reuseFailAlloc_202_, 5, v_decls_185_);
lean_ctor_set(v_reuseFailAlloc_202_, 6, v_userNames_186_);
lean_ctor_set(v_reuseFailAlloc_202_, 7, v_lAssignment_187_);
lean_ctor_set(v_reuseFailAlloc_202_, 8, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_202_, 9, v_dAssignment_189_);
v___x_195_ = v_reuseFailAlloc_202_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_195_);
v___x_197_ = v___x_178_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_cache_173_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_zetaDeltaFVarIds_174_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_postponed_175_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_diag_176_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_st_ref_set(v___y_169_, v___x_197_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
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
lean_object* v___x_217_; 
lean_inc(v_mvarId_211_);
v___x_217_ = l_Lean_MVarId_getType(v_mvarId_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_262_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_262_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_262_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_262_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___f_222_; lean_object* v___x_223_; 
v___f_222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
v___x_223_ = lean_find_expr(v___f_222_, v_a_218_);
lean_dec(v_a_218_);
if (lean_obj_tag(v___x_223_) == 1)
{
lean_object* v_val_224_; lean_object* v___x_225_; 
lean_del_object(v___x_220_);
v_val_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_223_, 1);
lean_inc(v_mvarId_211_);
v___x_225_ = l_Lean_MVarId_getType(v_mvarId_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = l_Lean_Expr_appArg_x21(v_val_224_);
lean_dec(v_val_224_);
v___x_228_ = l_Lean_Meta_mkFalseElim(v_a_226_, v___x_227_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
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
lean_dec(v_val_224_);
lean_dec(v_mvarId_211_);
v_a_249_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_225_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_225_);
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
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_258_);
v___x_260_ = v___x_220_;
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
v_a_263_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_217_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_217_);
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
size_t v_x_1463__boxed_312_; size_t v_x_1464__boxed_313_; lean_object* v_res_314_; 
v_x_1463__boxed_312_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_x_1464__boxed_313_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_res_314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_306_, v_x_307_, v_x_1463__boxed_312_, v_x_1464__boxed_313_, v_x_310_, v_x_311_);
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
lean_dec_ref(v_s_414_);
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
lean_dec(v_a_501_);
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
lean_object* v___x_571_; lean_object* v_env_572_; lean_object* v___x_573_; lean_object* v_mctx_574_; lean_object* v_lctx_575_; lean_object* v_options_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_571_ = lean_st_ref_get(v___y_569_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_571_);
v___x_573_ = lean_st_ref_get(v___y_567_);
v_mctx_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_mctx_574_);
lean_dec(v___x_573_);
v_lctx_575_ = lean_ctor_get(v___y_566_, 2);
v_options_576_ = lean_ctor_get(v___y_568_, 2);
lean_inc_ref(v_options_576_);
lean_inc_ref(v_lctx_575_);
v___x_577_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_577_, 0, v_env_572_);
lean_ctor_set(v___x_577_, 1, v_mctx_574_);
lean_ctor_set(v___x_577_, 2, v_lctx_575_);
lean_ctor_set(v___x_577_, 3, v_options_576_);
v___x_578_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_msgData_565_);
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
v_ref_599_ = lean_ctor_get(v___y_596_, 5);
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
v___x_636_ = lean_st_ref_set(v___y_597_, v___x_635_);
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
size_t v_sz_boxed_674_; size_t v___x_18104__boxed_675_; uint8_t v___x_18106__boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v___x_18104__boxed_675_ = lean_unbox_usize(v___x_665_);
lean_dec(v___x_665_);
v___x_18106__boxed_676_ = lean_unbox(v___x_667_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_661_, v_mvarId_662_, v_fields_663_, v_sz_boxed_674_, v___x_18104__boxed_675_, v___x_666_, v___x_18106__boxed_676_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
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
lean_object* v_a_765_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v_options_798_; uint8_t v_hasTrace_799_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v_options_798_ = lean_ctor_get(v___y_761_, 2);
v_hasTrace_799_ = lean_ctor_get_uint8(v_options_798_, sizeof(void*)*1);
if (v_hasTrace_799_ == 0)
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
lean_object* v_inheritedTraceOptions_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_inheritedTraceOptions_800_ = lean_ctor_get(v___y_761_, 13);
v___x_801_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_802_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_803_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_800_, v_options_798_, v___x_802_);
if (v___x_803_ == 0)
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
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_804_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_805_ = lean_array_get_size(v_a_765_);
v___x_806_ = l_Nat_reprFast(v___x_805_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = l_Lean_MessageData_ofFormat(v___x_807_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_804_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_801_, v___x_809_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_dec_ref_known(v___x_810_, 1);
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
goto v___jp_766_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_a_765_);
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
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_863_; 
v_a_819_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_863_ == 0)
{
v___x_821_ = v___x_764_;
v_isShared_822_ = v_isSharedCheck_863_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_764_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_863_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___y_824_; uint8_t v___x_861_; 
v___x_861_ = l_Lean_Exception_isInterrupt(v_a_819_);
if (v___x_861_ == 0)
{
uint8_t v___x_862_; 
lean_inc(v_a_819_);
v___x_862_ = l_Lean_Exception_isRuntime(v_a_819_);
v___y_824_ = v___x_862_;
goto v___jp_823_;
}
else
{
v___y_824_ = v___x_861_;
goto v___jp_823_;
}
v___jp_823_:
{
if (v___y_824_ == 0)
{
lean_object* v_options_825_; uint8_t v_hasTrace_826_; 
v_options_825_ = lean_ctor_get(v___y_761_, 2);
v_hasTrace_826_ = lean_ctor_get_uint8(v_options_825_, sizeof(void*)*1);
if (v_hasTrace_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec(v_a_819_);
v___x_827_ = lean_box(v___x_754_);
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
lean_object* v_inheritedTraceOptions_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_inheritedTraceOptions_831_ = lean_ctor_get(v___y_761_, 13);
v___x_832_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_833_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_831_, v_options_825_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_dec(v_a_819_);
v___x_835_ = lean_box(v___x_754_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v___x_835_);
v___x_837_ = v___x_821_;
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
lean_del_object(v___x_821_);
v___x_839_ = l_Lean_Exception_toMessageData(v_a_819_);
v___x_840_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_832_, v___x_839_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
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
v___x_844_ = lean_box(v___x_754_);
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
if (v_isShared_822_ == 0)
{
v___x_859_ = v___x_821_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_819_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_864_, lean_object* v_fvarId_865_, lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v___x_868_, lean_object* v_val_869_, lean_object* v___x_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v___x_18226__boxed_877_; uint8_t v___x_18229__boxed_878_; lean_object* v_res_879_; 
v___x_18226__boxed_877_ = lean_unbox(v___x_867_);
v___x_18229__boxed_878_ = lean_unbox(v___x_870_);
v_res_879_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_864_, v_fvarId_865_, v___x_866_, v___x_18226__boxed_877_, v___x_868_, v_val_869_, v___x_18229__boxed_878_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec(v_val_869_);
return v_res_879_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_883_, lean_object* v_fvarId_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_895_ = lean_st_ref_get(v_a_885_);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_nat_dec_eq(v___x_895_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___f_907_; lean_object* v___x_908_; 
v___x_898_ = lean_st_ref_take(v_a_885_);
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_sub(v___x_898_, v___x_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_st_ref_set(v_a_885_, v___x_900_);
v___x_902_ = 1;
v___x_903_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_904_ = lean_box(0);
v___x_905_ = lean_box(v___x_897_);
v___x_906_ = lean_box(v___x_902_);
v___f_907_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_907_, 0, v_mvarId_883_);
lean_closure_set(v___f_907_, 1, v_fvarId_884_);
lean_closure_set(v___f_907_, 2, v___x_903_);
lean_closure_set(v___f_907_, 3, v___x_905_);
lean_closure_set(v___f_907_, 4, v___x_904_);
lean_closure_set(v___f_907_, 5, v___x_895_);
lean_closure_set(v___f_907_, 6, v___x_906_);
v___x_908_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_907_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
return v___x_908_;
}
else
{
lean_object* v_options_909_; uint8_t v_hasTrace_910_; 
lean_dec(v___x_895_);
lean_dec(v_fvarId_884_);
lean_dec(v_mvarId_883_);
v_options_909_ = lean_ctor_get(v_a_888_, 2);
v_hasTrace_910_ = lean_ctor_get_uint8(v_options_909_, sizeof(void*)*1);
if (v_hasTrace_910_ == 0)
{
goto v___jp_891_;
}
else
{
lean_object* v_inheritedTraceOptions_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_inheritedTraceOptions_911_ = lean_ctor_get(v_a_888_, 13);
v___x_912_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_913_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_914_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_911_, v_options_909_, v___x_913_);
if (v___x_914_ == 0)
{
goto v___jp_891_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_916_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_912_, v___x_915_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_dec_ref_known(v___x_916_, 1);
goto v___jp_891_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
v___jp_891_:
{
uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = 0;
v___x_893_ = lean_box(v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_925_, lean_object* v___x_926_, lean_object* v_as_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_a_938_; uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v___x_926_);
lean_dec_ref(v___x_925_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_b_930_);
return v___x_943_;
}
else
{
lean_object* v_subst_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_a_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
lean_dec_ref(v_b_930_);
v_subst_944_ = lean_ctor_get(v___x_925_, 2);
v___x_945_ = lean_box(0);
v___x_946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_947_ = lean_array_uget_borrowed(v_as_927_, v_i_929_);
lean_inc(v_subst_944_);
v___x_948_ = l_Lean_Meta_FVarSubst_apply(v_subst_944_, v_a_947_);
v___x_949_ = l_Lean_Expr_isFVar(v___x_948_);
if (v___x_949_ == 0)
{
lean_dec_ref(v___x_948_);
v_a_938_ = v___x_946_;
goto v___jp_937_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = l_Lean_Expr_fvarId_x21(v___x_948_);
lean_dec_ref(v___x_948_);
lean_inc(v___x_950_);
v___x_951_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_950_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; uint8_t v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_unbox(v_a_952_);
lean_dec(v_a_952_);
if (v___x_953_ == 0)
{
lean_dec(v___x_950_);
v_a_938_ = v___x_946_;
goto v___jp_937_;
}
else
{
lean_object* v___x_954_; 
lean_inc(v___x_926_);
v___x_954_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_926_, v___x_950_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_965_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_965_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint8_t v___x_959_; 
v___x_959_ = lean_unbox(v_a_955_);
if (v___x_959_ == 0)
{
lean_del_object(v___x_957_);
lean_dec(v_a_955_);
v_a_938_ = v___x_946_;
goto v___jp_937_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
lean_dec(v___x_926_);
lean_dec_ref(v___x_925_);
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v_a_955_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_945_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_961_);
v___x_963_ = v___x_957_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v___x_926_);
lean_dec_ref(v___x_925_);
v_a_966_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_954_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_954_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
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
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v___x_950_);
lean_dec(v___x_926_);
lean_dec_ref(v___x_925_);
v_a_974_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_951_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_951_);
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
v___jp_937_:
{
size_t v___x_939_; size_t v___x_940_; 
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_929_, v___x_939_);
lean_inc_ref(v_a_938_);
v_i_929_ = v___x_940_;
v_b_930_ = v_a_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_982_, lean_object* v_mvarId_983_, lean_object* v_fields_984_, size_t v_sz_985_, size_t v___x_986_, lean_object* v___x_987_, uint8_t v___x_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_982_, v_mvarId_983_, v_fields_984_, v_sz_985_, v___x_986_, v___x_987_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1009_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1009_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1009_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_fst_1000_; 
v_fst_1000_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_fst_1000_);
lean_dec(v_a_996_);
if (lean_obj_tag(v_fst_1000_) == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_box(v___x_988_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1001_);
v___x_1003_ = v___x_998_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
else
{
lean_object* v_val_1005_; lean_object* v___x_1007_; 
v_val_1005_ = lean_ctor_get(v_fst_1000_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v_fst_1000_, 1);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v_val_1005_);
v___x_1007_ = v___x_998_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_val_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_995_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_995_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1018_, lean_object* v_as_1019_, lean_object* v_sz_1020_, lean_object* v_i_1021_, lean_object* v_b_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
size_t v_sz_boxed_1029_; size_t v_i_boxed_1030_; lean_object* v_res_1031_; 
v_sz_boxed_1029_ = lean_unbox_usize(v_sz_1020_);
lean_dec(v_sz_1020_);
v_i_boxed_1030_ = lean_unbox_usize(v_i_1021_);
lean_dec(v_i_1021_);
v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1018_, v_as_1019_, v_sz_boxed_1029_, v_i_boxed_1030_, v_b_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v_as_1019_);
lean_dec(v_val_1018_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v_as_1034_, lean_object* v_sz_1035_, lean_object* v_i_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
size_t v_sz_boxed_1044_; size_t v_i_boxed_1045_; lean_object* v_res_1046_; 
v_sz_boxed_1044_ = lean_unbox_usize(v_sz_1035_);
lean_dec(v_sz_1035_);
v_i_boxed_1045_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1032_, v___x_1033_, v_as_1034_, v_sz_boxed_1044_, v_i_boxed_1045_, v_b_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v_as_1034_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1047_, lean_object* v_fvarId_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1047_, v_fvarId_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1056_, lean_object* v_msg_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1056_, v_msg_1057_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1065_, lean_object* v_msg_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1065_, v_msg_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Meta_saveState___redArg(v___y_1076_, v___y_1078_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___y_1083_; lean_object* v___y_1084_; uint8_t v___y_1085_; lean_object* v___y_1104_; lean_object* v_a_1105_; lean_object* v___x_1108_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
lean_inc(v___y_1076_);
lean_inc_ref(v___y_1075_);
v___x_1108_ = lean_apply_5(v_x_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, lean_box(0));
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
v___x_1111_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1081_, v___y_1076_, v___y_1078_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_a_1081_);
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
v___y_1104_ = v___x_1125_;
v_a_1105_ = v_a_1120_;
goto v___jp_1103_;
}
}
}
}
else
{
lean_dec(v_a_1109_);
lean_dec(v_a_1081_);
return v___x_1108_;
}
}
else
{
lean_object* v_a_1128_; 
v_a_1128_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1128_);
v___y_1104_ = v___x_1108_;
v_a_1105_ = v_a_1128_;
goto v___jp_1103_;
}
v___jp_1082_:
{
if (v___y_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_dec_ref(v___y_1083_);
v___x_1086_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1081_, v___y_1076_, v___y_1078_);
lean_dec(v_a_1081_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v___x_1086_, 0);
lean_dec(v_unused_1094_);
v___x_1088_ = v___x_1086_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v___x_1086_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 1);
lean_ctor_set(v___x_1088_, 0, v___y_1084_);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___y_1084_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v___y_1084_);
v_a_1095_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1086_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1086_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_dec_ref(v___y_1084_);
lean_dec(v_a_1081_);
return v___y_1083_;
}
}
v___jp_1103_:
{
uint8_t v___x_1106_; 
v___x_1106_ = l_Lean_Exception_isInterrupt(v_a_1105_);
if (v___x_1106_ == 0)
{
uint8_t v___x_1107_; 
lean_inc_ref(v_a_1105_);
v___x_1107_ = l_Lean_Exception_isRuntime(v_a_1105_);
v___y_1083_ = v___y_1104_;
v___y_1084_ = v_a_1105_;
v___y_1085_ = v___x_1107_;
goto v___jp_1082_;
}
else
{
v___y_1083_ = v___y_1104_;
v___y_1084_ = v_a_1105_;
v___y_1085_ = v___x_1106_;
goto v___jp_1082_;
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v_x_1074_);
v_a_1129_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1080_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1080_);
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
lean_inc(v_a_1240_);
v___x_1241_ = lean_unbox(v_a_1240_);
lean_dec(v_a_1240_);
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
lean_object* v___f_1307_; lean_object* v___x_5509__overap_1308_; lean_object* v___x_1309_; 
v___f_1307_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_5509__overap_1308_ = lean_panic_fn_borrowed(v___f_1307_, v_msg_1301_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
v___x_1309_ = lean_apply_5(v___x_5509__overap_1308_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, lean_box(0));
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
v___x_1337_ = lean_st_ref_set(v___y_1318_, v___x_1336_);
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
uint8_t v___x_7190__boxed_1725_; lean_object* v_res_1726_; 
v___x_7190__boxed_1725_ = lean_unbox(v___x_1717_);
v_res_1726_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1716_, v___x_7190__boxed_1725_, v_localDecl_1718_, v_mvarId_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
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
v___x_1732_ = lean_unsigned_to_nat(120u);
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
lean_inc_ref(v___x_1743_);
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
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1(void){
_start:
{
uint8_t v___x_1791_; uint64_t v___x_1792_; 
v___x_1791_ = 1;
v___x_1792_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6));
v___x_1803_ = l_Lean_mkConst(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8(void){
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
lean_object* v_snd_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_2487_; 
v_snd_1819_ = lean_ctor_get(v_b_1811_, 1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_b_1811_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; 
v_unused_2488_ = lean_ctor_get(v_b_1811_, 0);
lean_dec(v_unused_2488_);
v___x_1821_ = v_b_1811_;
v_isShared_1822_ = v_isSharedCheck_2487_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_snd_1819_);
lean_dec(v_b_1811_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_2487_;
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
lean_object* v_val_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_2486_; 
v_val_1838_ = lean_ctor_get(v_a_1837_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_a_1837_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_1840_ = v_a_1837_;
v_isShared_1841_ = v_isSharedCheck_2486_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_val_1838_);
lean_dec(v_a_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_2486_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___x_1883_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; uint8_t v___x_1911_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; uint8_t v___y_1917_; lean_object* v___y_1919_; lean_object* v___y_1920_; uint8_t v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; uint8_t v___y_1924_; uint8_t v___y_1926_; uint8_t v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; uint8_t v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; uint8_t v___y_1938_; lean_object* v___y_1939_; uint8_t v___y_1940_; 
v___x_1842_ = lean_box(0);
v___x_1883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1911_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1838_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1955_; uint8_t v___y_1957_; uint8_t v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1966_; uint8_t v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; uint8_t v___y_1972_; uint8_t v___y_1973_; uint8_t v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1981_; lean_object* v_a_1982_; uint8_t v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; uint8_t v___y_1991_; uint8_t v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; uint8_t v___y_2082_; uint8_t v___y_2083_; uint8_t v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; uint8_t v___y_2091_; uint8_t v___y_2092_; uint8_t v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; uint8_t v___y_2100_; uint8_t v___y_2101_; uint8_t v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; uint8_t v___y_2119_; uint8_t v___y_2120_; uint8_t v___y_2122_; uint8_t v_isHEq_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2131_; lean_object* v___y_2132_; uint8_t v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; uint8_t v_isEq_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___x_2423_; 
v___x_1955_ = l_Lean_LocalDecl_type(v_val_1838_);
lean_inc_ref(v___x_1955_);
v___x_2423_ = l_Lean_Meta_matchNot_x3f(v___x_1955_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
if (lean_obj_tag(v_a_2424_) == 1)
{
lean_object* v_val_2425_; lean_object* v___x_2426_; 
v_val_2425_ = lean_ctor_get(v_a_2424_, 0);
lean_inc(v_val_2425_);
lean_dec_ref_known(v_a_2424_, 1);
v___x_2426_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2425_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
if (lean_obj_tag(v_a_2427_) == 1)
{
lean_object* v_val_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec_ref(v_config_1806_);
v_val_2428_ = lean_ctor_get(v_a_2427_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_a_2427_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2430_ = v_a_2427_;
v_isShared_2431_ = v_isSharedCheck_2469_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_val_2428_);
lean_dec(v_a_2427_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2469_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; 
lean_inc(v_mvarId_1807_);
v___x_2432_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v___x_2434_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2435_ = l_Lean_mkFVar(v_val_2428_);
v___x_2436_ = l_Lean_Expr_app___override(v___x_2434_, v___x_2435_);
v___x_2437_ = l_Lean_Meta_mkFalseElim(v_a_2433_, v___x_2436_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2438_, v___y_1813_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
lean_dec_ref_known(v___x_2439_, 1);
v___x_2440_ = lean_box(v___x_1817_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2440_);
v___x_2442_ = v___x_2430_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v___x_1842_);
v_a_1824_ = v___x_2443_;
goto v___jp_1823_;
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_del_object(v___x_2430_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_2445_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2439_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2439_);
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
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_del_object(v___x_2430_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2453_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2437_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2437_);
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
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_del_object(v___x_2430_);
lean_dec(v_val_2428_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2461_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2432_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2432_);
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
lean_dec(v_a_2427_);
v___y_2289_ = v___y_1812_;
v___y_2290_ = v___y_1813_;
v___y_2291_ = v___y_1814_;
v___y_2292_ = v___y_1815_;
goto v___jp_2288_;
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2470_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2426_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2426_);
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
lean_dec(v_a_2424_);
v___y_2289_ = v___y_1812_;
v___y_2290_ = v___y_1813_;
v___y_2291_ = v___y_1814_;
v___y_2292_ = v___y_1815_;
goto v___jp_2288_;
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2478_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2423_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2423_);
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
v___jp_1956_:
{
uint8_t v_genDiseq_1963_; 
v_genDiseq_1963_ = lean_ctor_get_uint8(v_config_1806_, sizeof(void*)*1 + 2);
if (v_genDiseq_1963_ == 0)
{
lean_dec_ref(v___x_1955_);
v___y_1934_ = v___y_1957_;
v___y_1935_ = v___y_1962_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1959_;
v___y_1938_ = v___y_1958_;
v___y_1939_ = v___y_1961_;
v___y_1940_ = v___x_1911_;
goto v___jp_1933_;
}
else
{
uint8_t v___x_1964_; 
v___x_1964_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1955_);
v___y_1934_ = v___y_1957_;
v___y_1935_ = v___y_1962_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1959_;
v___y_1938_ = v___y_1958_;
v___y_1939_ = v___y_1961_;
v___y_1940_ = v___x_1964_;
goto v___jp_1933_;
}
}
v___jp_1965_:
{
if (v___y_1973_ == 0)
{
lean_dec_ref(v___y_1966_);
v___y_1957_ = v___y_1967_;
v___y_1958_ = v___y_1972_;
v___y_1959_ = v___y_1970_;
v___y_1960_ = v___y_1969_;
v___y_1961_ = v___y_1971_;
v___y_1962_ = v___y_1968_;
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
lean_ctor_set(v___x_1974_, 0, v___y_1966_);
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
v___y_1966_ = v_a_1982_;
v___y_1967_ = v___y_1976_;
v___y_1968_ = v___y_1979_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1977_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___x_1984_;
goto v___jp_1965_;
}
else
{
v___y_1966_ = v_a_1982_;
v___y_1967_ = v___y_1976_;
v___y_1968_ = v___y_1979_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___y_1977_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___x_1983_;
goto v___jp_1965_;
}
}
v___jp_1985_:
{
lean_object* v___x_1992_; 
lean_inc_ref(v___x_1955_);
v___x_1992_ = l_Lean_Meta_mkDecide(v___x_1955_, v___y_1989_, v___y_1988_, v___y_1990_, v___y_1987_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1994_; uint8_t v_foApprox_1995_; uint8_t v_ctxApprox_1996_; uint8_t v_quasiPatternApprox_1997_; uint8_t v_constApprox_1998_; uint8_t v_isDefEqStuckEx_1999_; uint8_t v_unificationHints_2000_; uint8_t v_proofIrrelevance_2001_; uint8_t v_assignSyntheticOpaque_2002_; uint8_t v_offsetCnstrs_2003_; uint8_t v_etaStruct_2004_; uint8_t v_univApprox_2005_; uint8_t v_iota_2006_; uint8_t v_beta_2007_; uint8_t v_proj_2008_; uint8_t v_zeta_2009_; uint8_t v_zetaDelta_2010_; uint8_t v_zetaUnused_2011_; uint8_t v_zetaHave_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2074_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = l_Lean_Meta_Context_config(v___y_1989_);
v_foApprox_1995_ = lean_ctor_get_uint8(v___x_1994_, 0);
v_ctxApprox_1996_ = lean_ctor_get_uint8(v___x_1994_, 1);
v_quasiPatternApprox_1997_ = lean_ctor_get_uint8(v___x_1994_, 2);
v_constApprox_1998_ = lean_ctor_get_uint8(v___x_1994_, 3);
v_isDefEqStuckEx_1999_ = lean_ctor_get_uint8(v___x_1994_, 4);
v_unificationHints_2000_ = lean_ctor_get_uint8(v___x_1994_, 5);
v_proofIrrelevance_2001_ = lean_ctor_get_uint8(v___x_1994_, 6);
v_assignSyntheticOpaque_2002_ = lean_ctor_get_uint8(v___x_1994_, 7);
v_offsetCnstrs_2003_ = lean_ctor_get_uint8(v___x_1994_, 8);
v_etaStruct_2004_ = lean_ctor_get_uint8(v___x_1994_, 10);
v_univApprox_2005_ = lean_ctor_get_uint8(v___x_1994_, 11);
v_iota_2006_ = lean_ctor_get_uint8(v___x_1994_, 12);
v_beta_2007_ = lean_ctor_get_uint8(v___x_1994_, 13);
v_proj_2008_ = lean_ctor_get_uint8(v___x_1994_, 14);
v_zeta_2009_ = lean_ctor_get_uint8(v___x_1994_, 15);
v_zetaDelta_2010_ = lean_ctor_get_uint8(v___x_1994_, 16);
v_zetaUnused_2011_ = lean_ctor_get_uint8(v___x_1994_, 17);
v_zetaHave_2012_ = lean_ctor_get_uint8(v___x_1994_, 18);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2014_ = v___x_1994_;
v_isShared_2015_ = v_isSharedCheck_2074_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v___x_1994_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2074_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
uint8_t v_trackZetaDelta_2016_; lean_object* v_zetaDeltaSet_2017_; lean_object* v_lctx_2018_; lean_object* v_localInstances_2019_; lean_object* v_defEqCtx_x3f_2020_; lean_object* v_synthPendingDepth_2021_; lean_object* v_canUnfold_x3f_2022_; uint8_t v_univApprox_2023_; uint8_t v_inTypeClassResolution_2024_; uint8_t v_cacheInferType_2025_; uint8_t v___x_2026_; lean_object* v_config_2028_; 
v_trackZetaDelta_2016_ = lean_ctor_get_uint8(v___y_1989_, sizeof(void*)*7);
v_zetaDeltaSet_2017_ = lean_ctor_get(v___y_1989_, 1);
v_lctx_2018_ = lean_ctor_get(v___y_1989_, 2);
v_localInstances_2019_ = lean_ctor_get(v___y_1989_, 3);
v_defEqCtx_x3f_2020_ = lean_ctor_get(v___y_1989_, 4);
v_synthPendingDepth_2021_ = lean_ctor_get(v___y_1989_, 5);
v_canUnfold_x3f_2022_ = lean_ctor_get(v___y_1989_, 6);
v_univApprox_2023_ = lean_ctor_get_uint8(v___y_1989_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2024_ = lean_ctor_get_uint8(v___y_1989_, sizeof(void*)*7 + 2);
v_cacheInferType_2025_ = lean_ctor_get_uint8(v___y_1989_, sizeof(void*)*7 + 3);
v___x_2026_ = 1;
if (v_isShared_2015_ == 0)
{
v_config_2028_ = v___x_2014_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 0, v_foApprox_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 1, v_ctxApprox_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 2, v_quasiPatternApprox_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 3, v_constApprox_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 4, v_isDefEqStuckEx_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 5, v_unificationHints_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 6, v_proofIrrelevance_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 7, v_assignSyntheticOpaque_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 8, v_offsetCnstrs_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 10, v_etaStruct_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 11, v_univApprox_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 12, v_iota_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 13, v_beta_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 14, v_proj_2008_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 15, v_zeta_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 16, v_zetaDelta_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 17, v_zetaUnused_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, 18, v_zetaHave_2012_);
v_config_2028_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
uint64_t v___x_2029_; uint64_t v___x_2030_; uint64_t v___x_2031_; uint64_t v___x_2032_; uint64_t v___x_2033_; uint64_t v_key_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_ctor_set_uint8(v_config_2028_, 9, v___x_2026_);
v___x_2029_ = l_Lean_Meta_Context_configKey(v___y_1989_);
v___x_2030_ = 3ULL;
v___x_2031_ = lean_uint64_shift_right(v___x_2029_, v___x_2030_);
v___x_2032_ = lean_uint64_shift_left(v___x_2031_, v___x_2030_);
v___x_2033_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_2034_ = lean_uint64_lor(v___x_2032_, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2035_, 0, v_config_2028_);
lean_ctor_set_uint64(v___x_2035_, sizeof(void*)*1, v_key_2034_);
lean_inc(v_canUnfold_x3f_2022_);
lean_inc(v_synthPendingDepth_2021_);
lean_inc(v_defEqCtx_x3f_2020_);
lean_inc_ref(v_localInstances_2019_);
lean_inc_ref(v_lctx_2018_);
lean_inc(v_zetaDeltaSet_2017_);
v___x_2036_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v_zetaDeltaSet_2017_);
lean_ctor_set(v___x_2036_, 2, v_lctx_2018_);
lean_ctor_set(v___x_2036_, 3, v_localInstances_2019_);
lean_ctor_set(v___x_2036_, 4, v_defEqCtx_x3f_2020_);
lean_ctor_set(v___x_2036_, 5, v_synthPendingDepth_2021_);
lean_ctor_set(v___x_2036_, 6, v_canUnfold_x3f_2022_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*7, v_trackZetaDelta_2016_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*7 + 1, v_univApprox_2023_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2024_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*7 + 3, v_cacheInferType_2025_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1990_);
lean_inc(v___y_1988_);
lean_inc(v_a_1993_);
v___x_2037_ = lean_whnf(v_a_1993_, v___x_2036_, v___y_1988_, v___y_1990_, v___y_1987_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_2040_ = l_Lean_Expr_isConstOf(v_a_2038_, v___x_2039_);
lean_dec(v_a_2038_);
if (v___x_2040_ == 0)
{
lean_dec(v_a_1993_);
v___y_1957_ = v___y_1986_;
v___y_1958_ = v___y_1991_;
v___y_1959_ = v___y_1989_;
v___y_1960_ = v___y_1988_;
v___y_1961_ = v___y_1990_;
v___y_1962_ = v___y_1987_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_2041_; 
lean_inc(v_a_1993_);
v___x_2041_ = l_Lean_Meta_mkEqRefl(v_a_1993_, v___y_1989_, v___y_1988_, v___y_1990_, v___y_1987_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
lean_inc(v_mvarId_1807_);
v___x_2043_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_1989_, v___y_1988_, v___y_1990_, v___y_1987_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v_nargs_2045_; lean_object* v___x_2046_; lean_object* v_dummy_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v_nargs_2045_ = l_Lean_Expr_getAppNumArgs(v_a_1993_);
v___x_2046_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2047_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2045_);
v___x_2048_ = lean_mk_array(v_nargs_2045_, v_dummy_2047_);
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_sub(v_nargs_2045_, v___x_2049_);
lean_dec(v_nargs_2045_);
v___x_2051_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1993_, v___x_2048_, v___x_2050_);
v___x_2052_ = lean_array_push(v___x_2051_, v_a_2042_);
v___x_2053_ = l_Lean_mkAppN(v___x_2046_, v___x_2052_);
lean_dec_ref(v___x_2052_);
lean_inc(v_val_1838_);
v___x_2054_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2055_ = l_Lean_Meta_mkAbsurd(v_a_2044_, v___x_2054_, v___x_2053_, v___y_1989_, v___y_1988_, v___y_1990_, v___y_1987_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
lean_inc(v_mvarId_1807_);
v___x_2057_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2056_, v___y_1988_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; 
v_unused_2067_ = lean_ctor_get(v___x_2057_, 0);
lean_dec(v_unused_2067_);
v___x_2059_ = v___x_2057_;
v_isShared_2060_ = v_isSharedCheck_2066_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v___x_2057_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2066_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2061_ = lean_box(v___x_1817_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 1);
lean_ctor_set(v___x_2059_, 0, v___x_2061_);
v___x_2063_ = v___x_2059_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___x_1842_);
v_a_1824_ = v___x_2064_;
goto v___jp_1823_;
}
}
}
else
{
lean_object* v_a_2068_; 
v_a_2068_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2057_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1989_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1987_;
v___y_1980_ = v___y_1990_;
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_a_2068_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2069_; 
v_a_2069_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2055_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1989_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1987_;
v___y_1980_ = v___y_1990_;
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_a_2069_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2070_; 
lean_dec(v_a_2042_);
lean_dec(v_a_1993_);
v_a_2070_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2043_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1989_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1987_;
v___y_1980_ = v___y_1990_;
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_a_2070_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2071_; 
lean_dec(v_a_1993_);
v_a_2071_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2041_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1989_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1987_;
v___y_1980_ = v___y_1990_;
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_a_2071_;
goto v___jp_1975_;
}
}
}
else
{
lean_object* v_a_2072_; 
lean_dec(v_a_1993_);
v_a_2072_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2037_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1989_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1987_;
v___y_1980_ = v___y_1990_;
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_a_2072_;
goto v___jp_1975_;
}
}
}
}
else
{
lean_object* v_a_2075_; 
v_a_2075_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_1992_, 1);
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1989_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1987_;
v___y_1980_ = v___y_1990_;
v___y_1981_ = v___y_1991_;
v_a_1982_ = v_a_2075_;
goto v___jp_1975_;
}
}
v___jp_2076_:
{
if (v___y_2083_ == 0)
{
v___y_1957_ = v___y_2077_;
v___y_1958_ = v___y_2082_;
v___y_1959_ = v___y_2080_;
v___y_1960_ = v___y_2079_;
v___y_1961_ = v___y_2081_;
v___y_1962_ = v___y_2078_;
goto v___jp_1956_;
}
else
{
v___y_1986_ = v___y_2077_;
v___y_1987_ = v___y_2078_;
v___y_1988_ = v___y_2079_;
v___y_1989_ = v___y_2080_;
v___y_1990_ = v___y_2081_;
v___y_1991_ = v___y_2082_;
goto v___jp_1985_;
}
}
v___jp_2084_:
{
if (v___y_2092_ == 0)
{
lean_dec_ref(v___y_2090_);
v___y_2077_ = v___y_2085_;
v___y_2078_ = v___y_2088_;
v___y_2079_ = v___y_2087_;
v___y_2080_ = v___y_2086_;
v___y_2081_ = v___y_2089_;
v___y_2082_ = v___y_2091_;
v___y_2083_ = v___x_1911_;
goto v___jp_2076_;
}
else
{
uint8_t v___x_2093_; 
v___x_2093_ = l_Lean_Expr_hasFVar(v___y_2090_);
lean_dec_ref(v___y_2090_);
if (v___x_2093_ == 0)
{
v___y_1986_ = v___y_2085_;
v___y_1987_ = v___y_2088_;
v___y_1988_ = v___y_2087_;
v___y_1989_ = v___y_2086_;
v___y_1990_ = v___y_2089_;
v___y_1991_ = v___y_2091_;
goto v___jp_1985_;
}
else
{
v___y_2077_ = v___y_2085_;
v___y_2078_ = v___y_2088_;
v___y_2079_ = v___y_2087_;
v___y_2080_ = v___y_2086_;
v___y_2081_ = v___y_2089_;
v___y_2082_ = v___y_2091_;
v___y_2083_ = v___x_1911_;
goto v___jp_2076_;
}
}
}
v___jp_2094_:
{
lean_object* v___x_2102_; 
lean_inc_ref(v___x_1955_);
v___x_2102_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1955_, v___y_2098_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; uint8_t v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = l_Lean_Expr_hasMVar(v_a_2103_);
if (v___x_2104_ == 0)
{
v___y_2085_ = v___y_2095_;
v___y_2086_ = v___y_2096_;
v___y_2087_ = v___y_2098_;
v___y_2088_ = v___y_2097_;
v___y_2089_ = v___y_2099_;
v___y_2090_ = v_a_2103_;
v___y_2091_ = v___y_2100_;
v___y_2092_ = v___y_2101_;
goto v___jp_2084_;
}
else
{
v___y_2085_ = v___y_2095_;
v___y_2086_ = v___y_2096_;
v___y_2087_ = v___y_2098_;
v___y_2088_ = v___y_2097_;
v___y_2089_ = v___y_2099_;
v___y_2090_ = v_a_2103_;
v___y_2091_ = v___y_2100_;
v___y_2092_ = v___x_1911_;
goto v___jp_2084_;
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2105_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2102_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2102_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
v___jp_2113_:
{
if (v___y_2120_ == 0)
{
v___y_1957_ = v___y_2114_;
v___y_1958_ = v___y_2119_;
v___y_1959_ = v___y_2117_;
v___y_1960_ = v___y_2116_;
v___y_1961_ = v___y_2118_;
v___y_1962_ = v___y_2115_;
goto v___jp_1956_;
}
else
{
v___y_2095_ = v___y_2114_;
v___y_2096_ = v___y_2117_;
v___y_2097_ = v___y_2115_;
v___y_2098_ = v___y_2116_;
v___y_2099_ = v___y_2118_;
v___y_2100_ = v___y_2119_;
v___y_2101_ = v___y_2120_;
goto v___jp_2094_;
}
}
v___jp_2121_:
{
uint8_t v_useDecide_2128_; 
v_useDecide_2128_ = lean_ctor_get_uint8(v_config_1806_, sizeof(void*)*1);
if (v_useDecide_2128_ == 0)
{
v___y_2114_ = v___y_2122_;
v___y_2115_ = v___y_2127_;
v___y_2116_ = v___y_2125_;
v___y_2117_ = v___y_2124_;
v___y_2118_ = v___y_2126_;
v___y_2119_ = v_isHEq_2123_;
v___y_2120_ = v___x_1911_;
goto v___jp_2113_;
}
else
{
uint8_t v___x_2129_; 
v___x_2129_ = l_Lean_Expr_hasFVar(v___x_1955_);
if (v___x_2129_ == 0)
{
v___y_2095_ = v___y_2122_;
v___y_2096_ = v___y_2124_;
v___y_2097_ = v___y_2127_;
v___y_2098_ = v___y_2125_;
v___y_2099_ = v___y_2126_;
v___y_2100_ = v_isHEq_2123_;
v___y_2101_ = v_useDecide_2128_;
goto v___jp_2094_;
}
else
{
v___y_2114_ = v___y_2122_;
v___y_2115_ = v___y_2127_;
v___y_2116_ = v___y_2125_;
v___y_2117_ = v___y_2124_;
v___y_2118_ = v___y_2126_;
v___y_2119_ = v_isHEq_2123_;
v___y_2120_ = v___x_1911_;
goto v___jp_2113_;
}
}
}
v___jp_2130_:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_Meta_isExprDefEq(v___y_2132_, v___y_2137_, v___y_2136_, v___y_2135_, v___y_2131_, v___y_2134_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; uint8_t v___x_2140_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = lean_unbox(v_a_2139_);
lean_dec(v_a_2139_);
if (v___x_2140_ == 0)
{
v___y_2122_ = v___y_2133_;
v_isHEq_2123_ = v___x_1817_;
v___y_2124_ = v___y_2136_;
v___y_2125_ = v___y_2135_;
v___y_2126_ = v___y_2131_;
v___y_2127_ = v___y_2134_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2141_; 
lean_dec_ref(v___x_1955_);
lean_dec_ref(v_config_1806_);
lean_inc(v_mvarId_1807_);
v___x_2141_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_2136_, v___y_2135_, v___y_2131_, v___y_2134_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2144_ = l_Lean_Meta_mkEqOfHEq(v___x_2143_, v___x_1817_, v___y_2136_, v___y_2135_, v___y_2131_, v___y_2134_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Lean_Meta_mkNoConfusion(v_a_2142_, v_a_2145_, v___y_2136_, v___y_2135_, v___y_2131_, v___y_2134_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2147_, v___y_2135_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref_known(v___x_2148_, 1);
v___x_2149_ = lean_box(v___x_1817_);
v___x_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
lean_ctor_set(v___x_2151_, 1, v___x_1842_);
v_a_1824_ = v___x_2151_;
goto v___jp_1823_;
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_2152_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2148_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2148_);
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
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2160_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2146_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2146_);
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
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_a_2142_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2168_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2144_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2144_);
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
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2176_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2141_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2141_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2184_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2138_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2138_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
v___jp_2192_:
{
lean_object* v___x_2198_; 
lean_inc_ref(v___x_1955_);
v___x_2198_ = l_Lean_Meta_matchHEq_x3f(v___x_1955_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
if (lean_obj_tag(v_a_2199_) == 1)
{
lean_object* v_val_2200_; lean_object* v_snd_2201_; lean_object* v_snd_2202_; lean_object* v_fst_2203_; lean_object* v_fst_2204_; lean_object* v_fst_2205_; lean_object* v_snd_2206_; lean_object* v___x_2207_; 
v_val_2200_ = lean_ctor_get(v_a_2199_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v_a_2199_, 1);
v_snd_2201_ = lean_ctor_get(v_val_2200_, 1);
lean_inc(v_snd_2201_);
v_snd_2202_ = lean_ctor_get(v_snd_2201_, 1);
lean_inc(v_snd_2202_);
v_fst_2203_ = lean_ctor_get(v_val_2200_, 0);
lean_inc(v_fst_2203_);
lean_dec(v_val_2200_);
v_fst_2204_ = lean_ctor_get(v_snd_2201_, 0);
lean_inc(v_fst_2204_);
lean_dec(v_snd_2201_);
v_fst_2205_ = lean_ctor_get(v_snd_2202_, 0);
lean_inc(v_fst_2205_);
v_snd_2206_ = lean_ctor_get(v_snd_2202_, 1);
lean_inc(v_snd_2206_);
lean_dec(v_snd_2202_);
v___x_2207_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2204_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
if (lean_obj_tag(v_a_2208_) == 1)
{
lean_object* v_val_2209_; lean_object* v___x_2210_; 
v_val_2209_ = lean_ctor_get(v_a_2208_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v_a_2208_, 1);
v___x_2210_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2206_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2210_, 1);
if (lean_obj_tag(v_a_2211_) == 1)
{
lean_object* v_toConstantVal_2212_; lean_object* v_val_2213_; lean_object* v_toConstantVal_2214_; lean_object* v_name_2215_; lean_object* v_name_2216_; uint8_t v___x_2217_; 
v_toConstantVal_2212_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_toConstantVal_2212_);
lean_dec(v_val_2209_);
v_val_2213_ = lean_ctor_get(v_a_2211_, 0);
lean_inc(v_val_2213_);
lean_dec_ref_known(v_a_2211_, 1);
v_toConstantVal_2214_ = lean_ctor_get(v_val_2213_, 0);
lean_inc_ref(v_toConstantVal_2214_);
lean_dec(v_val_2213_);
v_name_2215_ = lean_ctor_get(v_toConstantVal_2212_, 0);
lean_inc(v_name_2215_);
lean_dec_ref(v_toConstantVal_2212_);
v_name_2216_ = lean_ctor_get(v_toConstantVal_2214_, 0);
lean_inc(v_name_2216_);
lean_dec_ref(v_toConstantVal_2214_);
v___x_2217_ = lean_name_eq(v_name_2215_, v_name_2216_);
lean_dec(v_name_2216_);
lean_dec(v_name_2215_);
if (v___x_2217_ == 0)
{
v___y_2131_ = v___y_2196_;
v___y_2132_ = v_fst_2203_;
v___y_2133_ = v_isEq_2193_;
v___y_2134_ = v___y_2197_;
v___y_2135_ = v___y_2195_;
v___y_2136_ = v___y_2194_;
v___y_2137_ = v_fst_2205_;
goto v___jp_2130_;
}
else
{
if (v___x_1911_ == 0)
{
lean_dec(v_fst_2205_);
lean_dec(v_fst_2203_);
v___y_2122_ = v_isEq_2193_;
v_isHEq_2123_ = v___x_1817_;
v___y_2124_ = v___y_2194_;
v___y_2125_ = v___y_2195_;
v___y_2126_ = v___y_2196_;
v___y_2127_ = v___y_2197_;
goto v___jp_2121_;
}
else
{
v___y_2131_ = v___y_2196_;
v___y_2132_ = v_fst_2203_;
v___y_2133_ = v_isEq_2193_;
v___y_2134_ = v___y_2197_;
v___y_2135_ = v___y_2195_;
v___y_2136_ = v___y_2194_;
v___y_2137_ = v_fst_2205_;
goto v___jp_2130_;
}
}
}
else
{
lean_dec(v_a_2211_);
lean_dec(v_val_2209_);
lean_dec(v_fst_2205_);
lean_dec(v_fst_2203_);
v___y_2122_ = v_isEq_2193_;
v_isHEq_2123_ = v___x_1817_;
v___y_2124_ = v___y_2194_;
v___y_2125_ = v___y_2195_;
v___y_2126_ = v___y_2196_;
v___y_2127_ = v___y_2197_;
goto v___jp_2121_;
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_val_2209_);
lean_dec(v_fst_2205_);
lean_dec(v_fst_2203_);
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2218_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2210_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2210_);
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
lean_dec(v_a_2208_);
lean_dec(v_snd_2206_);
lean_dec(v_fst_2205_);
lean_dec(v_fst_2203_);
v___y_2122_ = v_isEq_2193_;
v_isHEq_2123_ = v___x_1817_;
v___y_2124_ = v___y_2194_;
v___y_2125_ = v___y_2195_;
v___y_2126_ = v___y_2196_;
v___y_2127_ = v___y_2197_;
goto v___jp_2121_;
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_snd_2206_);
lean_dec(v_fst_2205_);
lean_dec(v_fst_2203_);
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2226_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2207_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2207_);
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
lean_dec(v_a_2199_);
v___y_2122_ = v_isEq_2193_;
v_isHEq_2123_ = v___x_1911_;
v___y_2124_ = v___y_2194_;
v___y_2125_ = v___y_2195_;
v___y_2126_ = v___y_2196_;
v___y_2127_ = v___y_2197_;
goto v___jp_2121_;
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec_ref(v___x_1955_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2234_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2198_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2198_);
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
v___jp_2242_:
{
lean_object* v___x_2247_; 
lean_inc_ref(v___x_1955_);
v___x_2247_ = l_Lean_Meta_matchEq_x3f(v___x_1955_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2247_, 1);
if (lean_obj_tag(v_a_2248_) == 1)
{
lean_object* v_val_2249_; lean_object* v_snd_2250_; lean_object* v_fst_2251_; lean_object* v_snd_2252_; lean_object* v___x_2253_; 
v_val_2249_ = lean_ctor_get(v_a_2248_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v_a_2248_, 1);
v_snd_2250_ = lean_ctor_get(v_val_2249_, 1);
lean_inc(v_snd_2250_);
lean_dec(v_val_2249_);
v_fst_2251_ = lean_ctor_get(v_snd_2250_, 0);
lean_inc(v_fst_2251_);
v_snd_2252_ = lean_ctor_get(v_snd_2250_, 1);
lean_inc(v_snd_2252_);
lean_dec(v_snd_2250_);
v___x_2253_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2251_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
if (lean_obj_tag(v_a_2254_) == 1)
{
lean_object* v_val_2255_; lean_object* v___x_2256_; 
v_val_2255_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_val_2255_);
lean_dec_ref_known(v_a_2254_, 1);
v___x_2256_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2252_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
if (lean_obj_tag(v_a_2257_) == 1)
{
lean_object* v_toConstantVal_2258_; lean_object* v_val_2259_; lean_object* v_toConstantVal_2260_; lean_object* v_name_2261_; lean_object* v_name_2262_; uint8_t v___x_2263_; 
v_toConstantVal_2258_ = lean_ctor_get(v_val_2255_, 0);
lean_inc_ref(v_toConstantVal_2258_);
lean_dec(v_val_2255_);
v_val_2259_ = lean_ctor_get(v_a_2257_, 0);
lean_inc(v_val_2259_);
lean_dec_ref_known(v_a_2257_, 1);
v_toConstantVal_2260_ = lean_ctor_get(v_val_2259_, 0);
lean_inc_ref(v_toConstantVal_2260_);
lean_dec(v_val_2259_);
v_name_2261_ = lean_ctor_get(v_toConstantVal_2258_, 0);
lean_inc(v_name_2261_);
lean_dec_ref(v_toConstantVal_2258_);
v_name_2262_ = lean_ctor_get(v_toConstantVal_2260_, 0);
lean_inc(v_name_2262_);
lean_dec_ref(v_toConstantVal_2260_);
v___x_2263_ = lean_name_eq(v_name_2261_, v_name_2262_);
lean_dec(v_name_2262_);
lean_dec(v_name_2261_);
if (v___x_2263_ == 0)
{
lean_dec_ref(v___x_1955_);
lean_dec_ref(v_config_1806_);
v___y_1844_ = v___y_2245_;
v___y_1845_ = v___y_2243_;
v___y_1846_ = v___y_2244_;
v___y_1847_ = v___y_2246_;
goto v___jp_1843_;
}
else
{
if (v___x_1911_ == 0)
{
lean_del_object(v___x_1840_);
v_isEq_2193_ = v___x_1817_;
v___y_2194_ = v___y_2243_;
v___y_2195_ = v___y_2244_;
v___y_2196_ = v___y_2245_;
v___y_2197_ = v___y_2246_;
goto v___jp_2192_;
}
else
{
lean_dec_ref(v___x_1955_);
lean_dec_ref(v_config_1806_);
v___y_1844_ = v___y_2245_;
v___y_1845_ = v___y_2243_;
v___y_1846_ = v___y_2244_;
v___y_1847_ = v___y_2246_;
goto v___jp_1843_;
}
}
}
else
{
lean_dec(v_a_2257_);
lean_dec(v_val_2255_);
lean_del_object(v___x_1840_);
v_isEq_2193_ = v___x_1817_;
v___y_2194_ = v___y_2243_;
v___y_2195_ = v___y_2244_;
v___y_2196_ = v___y_2245_;
v___y_2197_ = v___y_2246_;
goto v___jp_2192_;
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_val_2255_);
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2264_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2256_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2256_);
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
else
{
lean_dec(v_a_2254_);
lean_dec(v_snd_2252_);
lean_del_object(v___x_1840_);
v_isEq_2193_ = v___x_1817_;
v___y_2194_ = v___y_2243_;
v___y_2195_ = v___y_2244_;
v___y_2196_ = v___y_2245_;
v___y_2197_ = v___y_2246_;
goto v___jp_2192_;
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_snd_2252_);
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2272_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2253_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2253_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_dec(v_a_2248_);
lean_del_object(v___x_1840_);
v_isEq_2193_ = v___x_1911_;
v___y_2194_ = v___y_2243_;
v___y_2195_ = v___y_2244_;
v___y_2196_ = v___y_2245_;
v___y_2197_ = v___y_2246_;
goto v___jp_2192_;
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2280_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2247_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2247_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
v___jp_2288_:
{
lean_object* v___x_2293_; 
lean_inc_ref(v___x_1955_);
v___x_2293_ = l_refutableHasNotBit_x3f(v___x_1955_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
if (lean_obj_tag(v_a_2294_) == 1)
{
lean_object* v_val_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec_ref(v_config_1806_);
v_val_2295_ = lean_ctor_get(v_a_2294_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_a_2294_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2297_ = v_a_2294_;
v_isShared_2298_ = v_isSharedCheck_2334_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_val_2295_);
lean_dec(v_a_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2334_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; 
lean_inc(v_mvarId_1807_);
v___x_2299_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2302_ = l_Lean_Meta_mkAbsurd(v_a_2300_, v_val_2295_, v___x_2301_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2303_, v___y_2290_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2307_; 
lean_dec_ref_known(v___x_2304_, 1);
v___x_2305_ = lean_box(v___x_1817_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2305_);
v___x_2307_ = v___x_2297_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v___x_1842_);
v_a_1824_ = v___x_2308_;
goto v___jp_1823_;
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_del_object(v___x_2297_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_2310_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2304_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2304_);
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
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_del_object(v___x_2297_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2318_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2302_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2302_);
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
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_del_object(v___x_2297_);
lean_dec(v_val_2295_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2326_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2299_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2299_);
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
lean_object* v___x_2335_; 
lean_dec(v_a_2294_);
lean_inc_ref(v___x_1955_);
v___x_2335_ = l_Lean_Meta_matchNe_x3f(v___x_1955_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
if (lean_obj_tag(v_a_2336_) == 1)
{
lean_object* v_val_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2406_; 
v_val_2337_ = lean_ctor_get(v_a_2336_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_a_2336_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2339_ = v_a_2336_;
v_isShared_2340_ = v_isSharedCheck_2406_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_val_2337_);
lean_dec(v_a_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2406_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_snd_2341_; lean_object* v_fst_2342_; lean_object* v_snd_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2405_; 
v_snd_2341_ = lean_ctor_get(v_val_2337_, 1);
lean_inc(v_snd_2341_);
lean_dec(v_val_2337_);
v_fst_2342_ = lean_ctor_get(v_snd_2341_, 0);
v_snd_2343_ = lean_ctor_get(v_snd_2341_, 1);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_snd_2341_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2345_ = v_snd_2341_;
v_isShared_2346_ = v_isSharedCheck_2405_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_snd_2343_);
lean_inc(v_fst_2342_);
lean_dec(v_snd_2341_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2405_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; 
lean_inc(v_fst_2342_);
v___x_2347_ = l_Lean_Meta_isExprDefEq(v_fst_2342_, v_snd_2343_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; uint8_t v___x_2349_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = lean_unbox(v_a_2348_);
lean_dec(v_a_2348_);
if (v___x_2349_ == 0)
{
lean_del_object(v___x_2345_);
lean_dec(v_fst_2342_);
lean_del_object(v___x_2339_);
v___y_2243_ = v___y_2289_;
v___y_2244_ = v___y_2290_;
v___y_2245_ = v___y_2291_;
v___y_2246_ = v___y_2292_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2350_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec_ref(v_config_1806_);
lean_inc(v_mvarId_1807_);
v___x_2350_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v___x_2352_ = l_Lean_Meta_mkEqRefl(v_fst_2342_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_2355_ = l_Lean_Meta_mkAbsurd(v_a_2351_, v_a_2353_, v___x_2354_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2357_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v___x_2357_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1807_, v_a_2356_, v___y_2290_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
lean_dec_ref_known(v___x_2357_, 1);
v___x_2358_ = lean_box(v___x_1817_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2358_);
v___x_2360_ = v___x_2339_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 1, v___x_1842_);
lean_ctor_set(v___x_2345_, 0, v___x_2360_);
v___x_2362_ = v___x_2345_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v___x_1842_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
v_a_1824_ = v___x_2362_;
goto v___jp_1823_;
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_del_object(v___x_2345_);
lean_del_object(v___x_2339_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
v_a_2365_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2357_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2357_);
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
lean_del_object(v___x_2345_);
lean_del_object(v___x_2339_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2373_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2355_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2355_);
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
lean_dec(v_a_2351_);
lean_del_object(v___x_2345_);
lean_del_object(v___x_2339_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2381_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2352_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2352_);
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
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_del_object(v___x_2345_);
lean_dec(v_fst_2342_);
lean_del_object(v___x_2339_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
v_a_2389_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2350_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2350_);
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
lean_del_object(v___x_2345_);
lean_dec(v_fst_2342_);
lean_del_object(v___x_2339_);
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2397_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2347_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2347_);
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
}
else
{
lean_dec(v_a_2336_);
v___y_2243_ = v___y_2289_;
v___y_2244_ = v___y_2290_;
v___y_2245_ = v___y_2291_;
v___y_2246_ = v___y_2292_;
goto v___jp_2242_;
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2407_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2335_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2335_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec_ref(v___x_1955_);
lean_del_object(v___x_1840_);
lean_dec(v_val_1838_);
lean_del_object(v___x_1821_);
lean_dec(v_snd_1819_);
lean_dec(v_mvarId_1807_);
lean_dec_ref(v_config_1806_);
v_a_2415_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2293_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2293_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
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
v___x_1848_ = l_Lean_MVarId_getType(v_mvarId_1807_, v___y_1845_, v___y_1846_, v___y_1844_, v___y_1847_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = l_Lean_LocalDecl_toExpr(v_val_1838_);
v___x_1851_ = l_Lean_Meta_mkNoConfusion(v_a_1849_, v___x_1850_, v___y_1845_, v___y_1846_, v___y_1844_, v___y_1847_);
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
v___x_1891_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1807_, v___x_1890_, v_searchFuel_1889_, v___y_1886_, v___y_1885_, v___y_1888_, v___y_1887_);
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
v___y_1887_ = v___y_1909_;
v___y_1888_ = v___y_1908_;
goto v___jp_1884_;
}
}
v___jp_1912_:
{
if (v___y_1917_ == 0)
{
v___y_1885_ = v___y_1913_;
v___y_1886_ = v___y_1914_;
v___y_1887_ = v___y_1916_;
v___y_1888_ = v___y_1915_;
goto v___jp_1884_;
}
else
{
v___y_1906_ = v___y_1913_;
v___y_1907_ = v___y_1914_;
v___y_1908_ = v___y_1915_;
v___y_1909_ = v___y_1916_;
v___y_1910_ = v___x_1911_;
goto v___jp_1905_;
}
}
v___jp_1918_:
{
if (v___y_1924_ == 0)
{
v___y_1906_ = v___y_1919_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1923_;
v___y_1909_ = v___y_1922_;
v___y_1910_ = v___x_1911_;
goto v___jp_1905_;
}
else
{
v___y_1913_ = v___y_1919_;
v___y_1914_ = v___y_1920_;
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___y_1922_;
v___y_1917_ = v___y_1921_;
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
v___y_1920_ = v___y_1928_;
v___y_1921_ = v___y_1927_;
v___y_1922_ = v___y_1931_;
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___x_1911_;
goto v___jp_1918_;
}
else
{
if (v___y_1926_ == 0)
{
v___y_1913_ = v___y_1929_;
v___y_1914_ = v___y_1928_;
v___y_1915_ = v___y_1930_;
v___y_1916_ = v___y_1931_;
v___y_1917_ = v___y_1927_;
goto v___jp_1912_;
}
else
{
v___y_1919_ = v___y_1929_;
v___y_1920_ = v___y_1928_;
v___y_1921_ = v___y_1927_;
v___y_1922_ = v___y_1931_;
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
v___y_1927_ = v___y_1938_;
v___y_1928_ = v___y_1937_;
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___y_1939_;
v___y_1931_ = v___y_1935_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1941_; 
lean_inc(v_val_1838_);
lean_inc(v_mvarId_1807_);
v___x_1941_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1807_, v_val_1838_, v___y_1937_, v___y_1936_, v___y_1939_, v___y_1935_);
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
v___y_1927_ = v___y_1938_;
v___y_1928_ = v___y_1937_;
v___y_1929_ = v___y_1936_;
v___y_1930_ = v___y_1939_;
v___y_1931_ = v___y_1935_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2489_, lean_object* v_mvarId_2490_, lean_object* v_as_2491_, lean_object* v_sz_2492_, lean_object* v_i_2493_, lean_object* v_b_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
size_t v_sz_boxed_2500_; size_t v_i_boxed_2501_; lean_object* v_res_2502_; 
v_sz_boxed_2500_ = lean_unbox_usize(v_sz_2492_);
lean_dec(v_sz_2492_);
v_i_boxed_2501_ = lean_unbox_usize(v_i_2493_);
lean_dec(v_i_2493_);
v_res_2502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2489_, v_mvarId_2490_, v_as_2491_, v_sz_boxed_2500_, v_i_boxed_2501_, v_b_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v_as_2491_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2503_, lean_object* v_mvarId_2504_, lean_object* v_as_2505_, size_t v_sz_2506_, size_t v_i_2507_, lean_object* v_b_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_usize_dec_lt(v_i_2507_, v_sz_2506_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_b_2508_);
return v___x_2515_;
}
else
{
lean_object* v_snd_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_3184_; 
v_snd_2516_ = lean_ctor_get(v_b_2508_, 1);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_b_2508_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; 
v_unused_3185_ = lean_ctor_get(v_b_2508_, 0);
lean_dec(v_unused_3185_);
v___x_2518_ = v_b_2508_;
v_isShared_2519_ = v_isSharedCheck_3184_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_snd_2516_);
lean_dec(v_b_2508_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_3184_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_a_2521_; lean_object* v___x_2527_; lean_object* v_a_2529_; lean_object* v_a_2534_; 
v___x_2527_ = lean_box(0);
v_a_2534_ = lean_array_uget(v_as_2505_, v_i_2507_);
if (lean_obj_tag(v_a_2534_) == 0)
{
lean_del_object(v___x_2518_);
v_a_2529_ = v_snd_2516_;
goto v___jp_2528_;
}
else
{
lean_object* v_val_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_3183_; 
v_val_2535_ = lean_ctor_get(v_a_2534_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_a_2534_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_2537_ = v_a_2534_;
v_isShared_2538_ = v_isSharedCheck_3183_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_val_2535_);
lean_dec(v_a_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_3183_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___x_2580_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; uint8_t v___y_2607_; uint8_t v___x_2608_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; uint8_t v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; uint8_t v___y_2619_; lean_object* v___y_2620_; uint8_t v___y_2621_; uint8_t v___y_2623_; uint8_t v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; uint8_t v___y_2631_; lean_object* v___y_2632_; uint8_t v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; uint8_t v___y_2637_; 
v___x_2539_ = lean_box(0);
v___x_2580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2608_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2535_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2652_; uint8_t v___y_2654_; uint8_t v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; uint8_t v___y_2663_; lean_object* v___y_2664_; uint8_t v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; uint8_t v___y_2670_; lean_object* v___y_2673_; uint8_t v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; uint8_t v___y_2677_; lean_object* v___y_2678_; lean_object* v_a_2679_; uint8_t v___y_2683_; lean_object* v___y_2684_; uint8_t v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; uint8_t v___y_2774_; lean_object* v___y_2775_; uint8_t v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; uint8_t v___y_2787_; lean_object* v___y_2788_; uint8_t v___y_2789_; uint8_t v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; uint8_t v___y_2796_; lean_object* v___y_2797_; uint8_t v___y_2798_; uint8_t v___y_2811_; lean_object* v___y_2812_; uint8_t v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; uint8_t v___y_2817_; uint8_t v___y_2819_; uint8_t v_isHEq_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2828_; lean_object* v___y_2829_; uint8_t v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; uint8_t v_isEq_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___x_3120_; 
v___x_2652_ = l_Lean_LocalDecl_type(v_val_2535_);
lean_inc_ref(v___x_2652_);
v___x_3120_ = l_Lean_Meta_matchNot_x3f(v___x_2652_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
if (lean_obj_tag(v_a_3121_) == 1)
{
lean_object* v_val_3122_; lean_object* v___x_3123_; 
v_val_3122_ = lean_ctor_get(v_a_3121_, 0);
lean_inc(v_val_3122_);
lean_dec_ref_known(v_a_3121_, 1);
v___x_3123_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3122_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
if (lean_obj_tag(v_a_3124_) == 1)
{
lean_object* v_val_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3166_; 
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec_ref(v_config_2503_);
v_val_3125_ = lean_ctor_get(v_a_3124_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_a_3124_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3127_ = v_a_3124_;
v_isShared_3128_ = v_isSharedCheck_3166_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_val_3125_);
lean_dec(v_a_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3166_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; 
lean_inc(v_mvarId_2504_);
v___x_3129_ = l_Lean_MVarId_getType(v_mvarId_2504_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref_known(v___x_3129_, 1);
v___x_3131_ = l_Lean_LocalDecl_toExpr(v_val_2535_);
v___x_3132_ = l_Lean_mkFVar(v_val_3125_);
v___x_3133_ = l_Lean_Expr_app___override(v___x_3131_, v___x_3132_);
v___x_3134_ = l_Lean_Meta_mkFalseElim(v_a_3130_, v___x_3133_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3136_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref_known(v___x_3134_, 1);
v___x_3136_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2504_, v_a_3135_, v___y_2510_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
lean_dec_ref_known(v___x_3136_, 1);
v___x_3137_ = lean_box(v___x_2514_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3137_);
v___x_3139_ = v___x_3127_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
lean_ctor_set(v___x_3140_, 1, v___x_2539_);
v_a_2521_ = v___x_3140_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_del_object(v___x_3127_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
v_a_3142_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3136_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3136_);
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
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_del_object(v___x_3127_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_3150_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3134_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3134_);
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
lean_del_object(v___x_3127_);
lean_dec(v_val_3125_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_3158_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3129_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3129_);
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
}
else
{
lean_dec(v_a_3124_);
v___y_2986_ = v___y_2509_;
v___y_2987_ = v___y_2510_;
v___y_2988_ = v___y_2511_;
v___y_2989_ = v___y_2512_;
goto v___jp_2985_;
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_3167_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3123_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3123_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_dec(v_a_3121_);
v___y_2986_ = v___y_2509_;
v___y_2987_ = v___y_2510_;
v___y_2988_ = v___y_2511_;
v___y_2989_ = v___y_2512_;
goto v___jp_2985_;
}
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_3175_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3120_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3120_);
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
v___jp_2653_:
{
uint8_t v_genDiseq_2660_; 
v_genDiseq_2660_ = lean_ctor_get_uint8(v_config_2503_, sizeof(void*)*1 + 2);
if (v_genDiseq_2660_ == 0)
{
lean_dec_ref(v___x_2652_);
v___y_2631_ = v___y_2654_;
v___y_2632_ = v___y_2659_;
v___y_2633_ = v___y_2655_;
v___y_2634_ = v___y_2656_;
v___y_2635_ = v___y_2658_;
v___y_2636_ = v___y_2657_;
v___y_2637_ = v___x_2608_;
goto v___jp_2630_;
}
else
{
uint8_t v___x_2661_; 
v___x_2661_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2652_);
v___y_2631_ = v___y_2654_;
v___y_2632_ = v___y_2659_;
v___y_2633_ = v___y_2655_;
v___y_2634_ = v___y_2656_;
v___y_2635_ = v___y_2658_;
v___y_2636_ = v___y_2657_;
v___y_2637_ = v___x_2661_;
goto v___jp_2630_;
}
}
v___jp_2662_:
{
if (v___y_2670_ == 0)
{
lean_dec_ref(v___y_2668_);
v___y_2654_ = v___y_2663_;
v___y_2655_ = v___y_2665_;
v___y_2656_ = v___y_2667_;
v___y_2657_ = v___y_2664_;
v___y_2658_ = v___y_2666_;
v___y_2659_ = v___y_2669_;
goto v___jp_2653_;
}
else
{
lean_object* v___x_2671_; 
lean_dec_ref(v___x_2652_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v___x_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___y_2668_);
return v___x_2671_;
}
}
v___jp_2672_:
{
uint8_t v___x_2680_; 
v___x_2680_ = l_Lean_Exception_isInterrupt(v_a_2679_);
if (v___x_2680_ == 0)
{
uint8_t v___x_2681_; 
lean_inc_ref(v_a_2679_);
v___x_2681_ = l_Lean_Exception_isRuntime(v_a_2679_);
v___y_2663_ = v___y_2674_;
v___y_2664_ = v___y_2673_;
v___y_2665_ = v___y_2677_;
v___y_2666_ = v___y_2676_;
v___y_2667_ = v___y_2675_;
v___y_2668_ = v_a_2679_;
v___y_2669_ = v___y_2678_;
v___y_2670_ = v___x_2681_;
goto v___jp_2662_;
}
else
{
v___y_2663_ = v___y_2674_;
v___y_2664_ = v___y_2673_;
v___y_2665_ = v___y_2677_;
v___y_2666_ = v___y_2676_;
v___y_2667_ = v___y_2675_;
v___y_2668_ = v_a_2679_;
v___y_2669_ = v___y_2678_;
v___y_2670_ = v___x_2680_;
goto v___jp_2662_;
}
}
v___jp_2682_:
{
lean_object* v___x_2689_; 
lean_inc_ref(v___x_2652_);
v___x_2689_ = l_Lean_Meta_mkDecide(v___x_2652_, v___y_2687_, v___y_2684_, v___y_2686_, v___y_2688_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; uint8_t v_foApprox_2692_; uint8_t v_ctxApprox_2693_; uint8_t v_quasiPatternApprox_2694_; uint8_t v_constApprox_2695_; uint8_t v_isDefEqStuckEx_2696_; uint8_t v_unificationHints_2697_; uint8_t v_proofIrrelevance_2698_; uint8_t v_assignSyntheticOpaque_2699_; uint8_t v_offsetCnstrs_2700_; uint8_t v_etaStruct_2701_; uint8_t v_univApprox_2702_; uint8_t v_iota_2703_; uint8_t v_beta_2704_; uint8_t v_proj_2705_; uint8_t v_zeta_2706_; uint8_t v_zetaDelta_2707_; uint8_t v_zetaUnused_2708_; uint8_t v_zetaHave_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2771_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v___x_2691_ = l_Lean_Meta_Context_config(v___y_2687_);
v_foApprox_2692_ = lean_ctor_get_uint8(v___x_2691_, 0);
v_ctxApprox_2693_ = lean_ctor_get_uint8(v___x_2691_, 1);
v_quasiPatternApprox_2694_ = lean_ctor_get_uint8(v___x_2691_, 2);
v_constApprox_2695_ = lean_ctor_get_uint8(v___x_2691_, 3);
v_isDefEqStuckEx_2696_ = lean_ctor_get_uint8(v___x_2691_, 4);
v_unificationHints_2697_ = lean_ctor_get_uint8(v___x_2691_, 5);
v_proofIrrelevance_2698_ = lean_ctor_get_uint8(v___x_2691_, 6);
v_assignSyntheticOpaque_2699_ = lean_ctor_get_uint8(v___x_2691_, 7);
v_offsetCnstrs_2700_ = lean_ctor_get_uint8(v___x_2691_, 8);
v_etaStruct_2701_ = lean_ctor_get_uint8(v___x_2691_, 10);
v_univApprox_2702_ = lean_ctor_get_uint8(v___x_2691_, 11);
v_iota_2703_ = lean_ctor_get_uint8(v___x_2691_, 12);
v_beta_2704_ = lean_ctor_get_uint8(v___x_2691_, 13);
v_proj_2705_ = lean_ctor_get_uint8(v___x_2691_, 14);
v_zeta_2706_ = lean_ctor_get_uint8(v___x_2691_, 15);
v_zetaDelta_2707_ = lean_ctor_get_uint8(v___x_2691_, 16);
v_zetaUnused_2708_ = lean_ctor_get_uint8(v___x_2691_, 17);
v_zetaHave_2709_ = lean_ctor_get_uint8(v___x_2691_, 18);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2711_ = v___x_2691_;
v_isShared_2712_ = v_isSharedCheck_2771_;
goto v_resetjp_2710_;
}
else
{
lean_dec(v___x_2691_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2771_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
uint8_t v_trackZetaDelta_2713_; lean_object* v_zetaDeltaSet_2714_; lean_object* v_lctx_2715_; lean_object* v_localInstances_2716_; lean_object* v_defEqCtx_x3f_2717_; lean_object* v_synthPendingDepth_2718_; lean_object* v_canUnfold_x3f_2719_; uint8_t v_univApprox_2720_; uint8_t v_inTypeClassResolution_2721_; uint8_t v_cacheInferType_2722_; uint8_t v___x_2723_; lean_object* v_config_2725_; 
v_trackZetaDelta_2713_ = lean_ctor_get_uint8(v___y_2687_, sizeof(void*)*7);
v_zetaDeltaSet_2714_ = lean_ctor_get(v___y_2687_, 1);
v_lctx_2715_ = lean_ctor_get(v___y_2687_, 2);
v_localInstances_2716_ = lean_ctor_get(v___y_2687_, 3);
v_defEqCtx_x3f_2717_ = lean_ctor_get(v___y_2687_, 4);
v_synthPendingDepth_2718_ = lean_ctor_get(v___y_2687_, 5);
v_canUnfold_x3f_2719_ = lean_ctor_get(v___y_2687_, 6);
v_univApprox_2720_ = lean_ctor_get_uint8(v___y_2687_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2721_ = lean_ctor_get_uint8(v___y_2687_, sizeof(void*)*7 + 2);
v_cacheInferType_2722_ = lean_ctor_get_uint8(v___y_2687_, sizeof(void*)*7 + 3);
v___x_2723_ = 1;
if (v_isShared_2712_ == 0)
{
v_config_2725_ = v___x_2711_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 0, v_foApprox_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 1, v_ctxApprox_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 2, v_quasiPatternApprox_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 3, v_constApprox_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 4, v_isDefEqStuckEx_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 5, v_unificationHints_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 6, v_proofIrrelevance_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 7, v_assignSyntheticOpaque_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 8, v_offsetCnstrs_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 10, v_etaStruct_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 11, v_univApprox_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 12, v_iota_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 13, v_beta_2704_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 14, v_proj_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 15, v_zeta_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 16, v_zetaDelta_2707_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 17, v_zetaUnused_2708_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 18, v_zetaHave_2709_);
v_config_2725_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
uint64_t v___x_2726_; uint64_t v___x_2727_; uint64_t v___x_2728_; uint64_t v___x_2729_; uint64_t v___x_2730_; uint64_t v_key_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_ctor_set_uint8(v_config_2725_, 9, v___x_2723_);
v___x_2726_ = l_Lean_Meta_Context_configKey(v___y_2687_);
v___x_2727_ = 3ULL;
v___x_2728_ = lean_uint64_shift_right(v___x_2726_, v___x_2727_);
v___x_2729_ = lean_uint64_shift_left(v___x_2728_, v___x_2727_);
v___x_2730_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_2731_ = lean_uint64_lor(v___x_2729_, v___x_2730_);
v___x_2732_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2732_, 0, v_config_2725_);
lean_ctor_set_uint64(v___x_2732_, sizeof(void*)*1, v_key_2731_);
lean_inc(v_canUnfold_x3f_2719_);
lean_inc(v_synthPendingDepth_2718_);
lean_inc(v_defEqCtx_x3f_2717_);
lean_inc_ref(v_localInstances_2716_);
lean_inc_ref(v_lctx_2715_);
lean_inc(v_zetaDeltaSet_2714_);
v___x_2733_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v_zetaDeltaSet_2714_);
lean_ctor_set(v___x_2733_, 2, v_lctx_2715_);
lean_ctor_set(v___x_2733_, 3, v_localInstances_2716_);
lean_ctor_set(v___x_2733_, 4, v_defEqCtx_x3f_2717_);
lean_ctor_set(v___x_2733_, 5, v_synthPendingDepth_2718_);
lean_ctor_set(v___x_2733_, 6, v_canUnfold_x3f_2719_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*7, v_trackZetaDelta_2713_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*7 + 1, v_univApprox_2720_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2721_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*7 + 3, v_cacheInferType_2722_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2686_);
lean_inc(v___y_2684_);
lean_inc(v_a_2690_);
v___x_2734_ = lean_whnf(v_a_2690_, v___x_2733_, v___y_2684_, v___y_2686_, v___y_2688_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_2737_ = l_Lean_Expr_isConstOf(v_a_2735_, v___x_2736_);
lean_dec(v_a_2735_);
if (v___x_2737_ == 0)
{
lean_dec(v_a_2690_);
v___y_2654_ = v___y_2683_;
v___y_2655_ = v___y_2685_;
v___y_2656_ = v___y_2687_;
v___y_2657_ = v___y_2684_;
v___y_2658_ = v___y_2686_;
v___y_2659_ = v___y_2688_;
goto v___jp_2653_;
}
else
{
lean_object* v___x_2738_; 
lean_inc(v_a_2690_);
v___x_2738_ = l_Lean_Meta_mkEqRefl(v_a_2690_, v___y_2687_, v___y_2684_, v___y_2686_, v___y_2688_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2740_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2738_, 1);
lean_inc(v_mvarId_2504_);
v___x_2740_ = l_Lean_MVarId_getType(v_mvarId_2504_, v___y_2687_, v___y_2684_, v___y_2686_, v___y_2688_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v_nargs_2742_; lean_object* v___x_2743_; lean_object* v_dummy_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v_nargs_2742_ = l_Lean_Expr_getAppNumArgs(v_a_2690_);
v___x_2743_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2744_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2742_);
v___x_2745_ = lean_mk_array(v_nargs_2742_, v_dummy_2744_);
v___x_2746_ = lean_unsigned_to_nat(1u);
v___x_2747_ = lean_nat_sub(v_nargs_2742_, v___x_2746_);
lean_dec(v_nargs_2742_);
v___x_2748_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2690_, v___x_2745_, v___x_2747_);
v___x_2749_ = lean_array_push(v___x_2748_, v_a_2739_);
v___x_2750_ = l_Lean_mkAppN(v___x_2743_, v___x_2749_);
lean_dec_ref(v___x_2749_);
lean_inc(v_val_2535_);
v___x_2751_ = l_Lean_LocalDecl_toExpr(v_val_2535_);
v___x_2752_ = l_Lean_Meta_mkAbsurd(v_a_2741_, v___x_2751_, v___x_2750_, v___y_2687_, v___y_2684_, v___y_2686_, v___y_2688_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
lean_inc(v_mvarId_2504_);
v___x_2754_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2504_, v_a_2753_, v___y_2684_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v___x_2652_);
lean_dec(v_val_2535_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; 
v_unused_2764_ = lean_ctor_get(v___x_2754_, 0);
lean_dec(v_unused_2764_);
v___x_2756_ = v___x_2754_;
v_isShared_2757_ = v_isSharedCheck_2763_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v___x_2754_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2763_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2758_ = lean_box(v___x_2514_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set_tag(v___x_2756_, 1);
lean_ctor_set(v___x_2756_, 0, v___x_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
lean_ctor_set(v___x_2761_, 1, v___x_2539_);
v_a_2521_ = v___x_2761_;
goto v___jp_2520_;
}
}
}
else
{
lean_object* v_a_2765_; 
v_a_2765_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2754_, 1);
v___y_2673_ = v___y_2684_;
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2687_;
v___y_2676_ = v___y_2686_;
v___y_2677_ = v___y_2685_;
v___y_2678_ = v___y_2688_;
v_a_2679_ = v_a_2765_;
goto v___jp_2672_;
}
}
else
{
lean_object* v_a_2766_; 
v_a_2766_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2752_, 1);
v___y_2673_ = v___y_2684_;
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2687_;
v___y_2676_ = v___y_2686_;
v___y_2677_ = v___y_2685_;
v___y_2678_ = v___y_2688_;
v_a_2679_ = v_a_2766_;
goto v___jp_2672_;
}
}
else
{
lean_object* v_a_2767_; 
lean_dec(v_a_2739_);
lean_dec(v_a_2690_);
v_a_2767_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2740_, 1);
v___y_2673_ = v___y_2684_;
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2687_;
v___y_2676_ = v___y_2686_;
v___y_2677_ = v___y_2685_;
v___y_2678_ = v___y_2688_;
v_a_2679_ = v_a_2767_;
goto v___jp_2672_;
}
}
else
{
lean_object* v_a_2768_; 
lean_dec(v_a_2690_);
v_a_2768_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2738_, 1);
v___y_2673_ = v___y_2684_;
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2687_;
v___y_2676_ = v___y_2686_;
v___y_2677_ = v___y_2685_;
v___y_2678_ = v___y_2688_;
v_a_2679_ = v_a_2768_;
goto v___jp_2672_;
}
}
}
else
{
lean_object* v_a_2769_; 
lean_dec(v_a_2690_);
v_a_2769_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2734_, 1);
v___y_2673_ = v___y_2684_;
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2687_;
v___y_2676_ = v___y_2686_;
v___y_2677_ = v___y_2685_;
v___y_2678_ = v___y_2688_;
v_a_2679_ = v_a_2769_;
goto v___jp_2672_;
}
}
}
}
else
{
lean_object* v_a_2772_; 
v_a_2772_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2689_, 1);
v___y_2673_ = v___y_2684_;
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2687_;
v___y_2676_ = v___y_2686_;
v___y_2677_ = v___y_2685_;
v___y_2678_ = v___y_2688_;
v_a_2679_ = v_a_2772_;
goto v___jp_2672_;
}
}
v___jp_2773_:
{
if (v___y_2780_ == 0)
{
v___y_2654_ = v___y_2774_;
v___y_2655_ = v___y_2776_;
v___y_2656_ = v___y_2778_;
v___y_2657_ = v___y_2775_;
v___y_2658_ = v___y_2777_;
v___y_2659_ = v___y_2779_;
goto v___jp_2653_;
}
else
{
v___y_2683_ = v___y_2774_;
v___y_2684_ = v___y_2775_;
v___y_2685_ = v___y_2776_;
v___y_2686_ = v___y_2777_;
v___y_2687_ = v___y_2778_;
v___y_2688_ = v___y_2779_;
goto v___jp_2682_;
}
}
v___jp_2781_:
{
if (v___y_2789_ == 0)
{
lean_dec_ref(v___y_2782_);
v___y_2774_ = v___y_2784_;
v___y_2775_ = v___y_2783_;
v___y_2776_ = v___y_2787_;
v___y_2777_ = v___y_2786_;
v___y_2778_ = v___y_2785_;
v___y_2779_ = v___y_2788_;
v___y_2780_ = v___x_2608_;
goto v___jp_2773_;
}
else
{
uint8_t v___x_2790_; 
v___x_2790_ = l_Lean_Expr_hasFVar(v___y_2782_);
lean_dec_ref(v___y_2782_);
if (v___x_2790_ == 0)
{
v___y_2683_ = v___y_2784_;
v___y_2684_ = v___y_2783_;
v___y_2685_ = v___y_2787_;
v___y_2686_ = v___y_2786_;
v___y_2687_ = v___y_2785_;
v___y_2688_ = v___y_2788_;
goto v___jp_2682_;
}
else
{
v___y_2774_ = v___y_2784_;
v___y_2775_ = v___y_2783_;
v___y_2776_ = v___y_2787_;
v___y_2777_ = v___y_2786_;
v___y_2778_ = v___y_2785_;
v___y_2779_ = v___y_2788_;
v___y_2780_ = v___x_2608_;
goto v___jp_2773_;
}
}
}
v___jp_2791_:
{
lean_object* v___x_2799_; 
lean_inc_ref(v___x_2652_);
v___x_2799_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2652_, v___y_2793_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; uint8_t v___x_2801_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = l_Lean_Expr_hasMVar(v_a_2800_);
if (v___x_2801_ == 0)
{
v___y_2782_ = v_a_2800_;
v___y_2783_ = v___y_2793_;
v___y_2784_ = v___y_2792_;
v___y_2785_ = v___y_2794_;
v___y_2786_ = v___y_2795_;
v___y_2787_ = v___y_2796_;
v___y_2788_ = v___y_2797_;
v___y_2789_ = v___y_2798_;
goto v___jp_2781_;
}
else
{
v___y_2782_ = v_a_2800_;
v___y_2783_ = v___y_2793_;
v___y_2784_ = v___y_2792_;
v___y_2785_ = v___y_2794_;
v___y_2786_ = v___y_2795_;
v___y_2787_ = v___y_2796_;
v___y_2788_ = v___y_2797_;
v___y_2789_ = v___x_2608_;
goto v___jp_2781_;
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec_ref(v___x_2652_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2802_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2799_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2799_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
v___jp_2810_:
{
if (v___y_2817_ == 0)
{
v___y_2654_ = v___y_2811_;
v___y_2655_ = v___y_2813_;
v___y_2656_ = v___y_2815_;
v___y_2657_ = v___y_2812_;
v___y_2658_ = v___y_2814_;
v___y_2659_ = v___y_2816_;
goto v___jp_2653_;
}
else
{
v___y_2792_ = v___y_2811_;
v___y_2793_ = v___y_2812_;
v___y_2794_ = v___y_2815_;
v___y_2795_ = v___y_2814_;
v___y_2796_ = v___y_2813_;
v___y_2797_ = v___y_2816_;
v___y_2798_ = v___y_2817_;
goto v___jp_2791_;
}
}
v___jp_2818_:
{
uint8_t v_useDecide_2825_; 
v_useDecide_2825_ = lean_ctor_get_uint8(v_config_2503_, sizeof(void*)*1);
if (v_useDecide_2825_ == 0)
{
v___y_2811_ = v___y_2819_;
v___y_2812_ = v___y_2822_;
v___y_2813_ = v_isHEq_2820_;
v___y_2814_ = v___y_2823_;
v___y_2815_ = v___y_2821_;
v___y_2816_ = v___y_2824_;
v___y_2817_ = v___x_2608_;
goto v___jp_2810_;
}
else
{
uint8_t v___x_2826_; 
v___x_2826_ = l_Lean_Expr_hasFVar(v___x_2652_);
if (v___x_2826_ == 0)
{
v___y_2792_ = v___y_2819_;
v___y_2793_ = v___y_2822_;
v___y_2794_ = v___y_2821_;
v___y_2795_ = v___y_2823_;
v___y_2796_ = v_isHEq_2820_;
v___y_2797_ = v___y_2824_;
v___y_2798_ = v_useDecide_2825_;
goto v___jp_2791_;
}
else
{
v___y_2811_ = v___y_2819_;
v___y_2812_ = v___y_2822_;
v___y_2813_ = v_isHEq_2820_;
v___y_2814_ = v___y_2823_;
v___y_2815_ = v___y_2821_;
v___y_2816_ = v___y_2824_;
v___y_2817_ = v___x_2608_;
goto v___jp_2810_;
}
}
}
v___jp_2827_:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_Meta_isExprDefEq(v___y_2833_, v___y_2834_, v___y_2829_, v___y_2828_, v___y_2832_, v___y_2831_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; uint8_t v___x_2837_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v___x_2837_ = lean_unbox(v_a_2836_);
lean_dec(v_a_2836_);
if (v___x_2837_ == 0)
{
v___y_2819_ = v___y_2830_;
v_isHEq_2820_ = v___x_2514_;
v___y_2821_ = v___y_2829_;
v___y_2822_ = v___y_2828_;
v___y_2823_ = v___y_2832_;
v___y_2824_ = v___y_2831_;
goto v___jp_2818_;
}
else
{
lean_object* v___x_2838_; 
lean_dec_ref(v___x_2652_);
lean_dec_ref(v_config_2503_);
lean_inc(v_mvarId_2504_);
v___x_2838_ = l_Lean_MVarId_getType(v_mvarId_2504_, v___y_2829_, v___y_2828_, v___y_2832_, v___y_2831_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = l_Lean_LocalDecl_toExpr(v_val_2535_);
v___x_2841_ = l_Lean_Meta_mkEqOfHEq(v___x_2840_, v___x_2514_, v___y_2829_, v___y_2828_, v___y_2832_, v___y_2831_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2843_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v___x_2843_ = l_Lean_Meta_mkNoConfusion(v_a_2839_, v_a_2842_, v___y_2829_, v___y_2828_, v___y_2832_, v___y_2831_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2504_, v_a_2844_, v___y_2828_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec_ref_known(v___x_2845_, 1);
v___x_2846_ = lean_box(v___x_2514_);
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
lean_ctor_set(v___x_2848_, 1, v___x_2539_);
v_a_2521_ = v___x_2848_;
goto v___jp_2520_;
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
v_a_2849_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2845_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2845_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_2857_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2843_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2843_);
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
lean_dec(v_a_2839_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_2865_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2841_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2841_);
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
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_2873_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2838_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2838_);
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
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec_ref(v___x_2652_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2881_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2835_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2835_);
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
v___jp_2889_:
{
lean_object* v___x_2895_; 
lean_inc_ref(v___x_2652_);
v___x_2895_ = l_Lean_Meta_matchHEq_x3f(v___x_2652_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
if (lean_obj_tag(v_a_2896_) == 1)
{
lean_object* v_val_2897_; lean_object* v_snd_2898_; lean_object* v_snd_2899_; lean_object* v_fst_2900_; lean_object* v_fst_2901_; lean_object* v_fst_2902_; lean_object* v_snd_2903_; lean_object* v___x_2904_; 
v_val_2897_ = lean_ctor_get(v_a_2896_, 0);
lean_inc(v_val_2897_);
lean_dec_ref_known(v_a_2896_, 1);
v_snd_2898_ = lean_ctor_get(v_val_2897_, 1);
lean_inc(v_snd_2898_);
v_snd_2899_ = lean_ctor_get(v_snd_2898_, 1);
lean_inc(v_snd_2899_);
v_fst_2900_ = lean_ctor_get(v_val_2897_, 0);
lean_inc(v_fst_2900_);
lean_dec(v_val_2897_);
v_fst_2901_ = lean_ctor_get(v_snd_2898_, 0);
lean_inc(v_fst_2901_);
lean_dec(v_snd_2898_);
v_fst_2902_ = lean_ctor_get(v_snd_2899_, 0);
lean_inc(v_fst_2902_);
v_snd_2903_ = lean_ctor_get(v_snd_2899_, 1);
lean_inc(v_snd_2903_);
lean_dec(v_snd_2899_);
v___x_2904_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2901_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
if (lean_obj_tag(v_a_2905_) == 1)
{
lean_object* v_val_2906_; lean_object* v___x_2907_; 
v_val_2906_ = lean_ctor_get(v_a_2905_, 0);
lean_inc(v_val_2906_);
lean_dec_ref_known(v_a_2905_, 1);
v___x_2907_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2903_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
if (lean_obj_tag(v_a_2908_) == 1)
{
lean_object* v_toConstantVal_2909_; lean_object* v_val_2910_; lean_object* v_toConstantVal_2911_; lean_object* v_name_2912_; lean_object* v_name_2913_; uint8_t v___x_2914_; 
v_toConstantVal_2909_ = lean_ctor_get(v_val_2906_, 0);
lean_inc_ref(v_toConstantVal_2909_);
lean_dec(v_val_2906_);
v_val_2910_ = lean_ctor_get(v_a_2908_, 0);
lean_inc(v_val_2910_);
lean_dec_ref_known(v_a_2908_, 1);
v_toConstantVal_2911_ = lean_ctor_get(v_val_2910_, 0);
lean_inc_ref(v_toConstantVal_2911_);
lean_dec(v_val_2910_);
v_name_2912_ = lean_ctor_get(v_toConstantVal_2909_, 0);
lean_inc(v_name_2912_);
lean_dec_ref(v_toConstantVal_2909_);
v_name_2913_ = lean_ctor_get(v_toConstantVal_2911_, 0);
lean_inc(v_name_2913_);
lean_dec_ref(v_toConstantVal_2911_);
v___x_2914_ = lean_name_eq(v_name_2912_, v_name_2913_);
lean_dec(v_name_2913_);
lean_dec(v_name_2912_);
if (v___x_2914_ == 0)
{
v___y_2828_ = v___y_2892_;
v___y_2829_ = v___y_2891_;
v___y_2830_ = v_isEq_2890_;
v___y_2831_ = v___y_2894_;
v___y_2832_ = v___y_2893_;
v___y_2833_ = v_fst_2900_;
v___y_2834_ = v_fst_2902_;
goto v___jp_2827_;
}
else
{
if (v___x_2608_ == 0)
{
lean_dec(v_fst_2902_);
lean_dec(v_fst_2900_);
v___y_2819_ = v_isEq_2890_;
v_isHEq_2820_ = v___x_2514_;
v___y_2821_ = v___y_2891_;
v___y_2822_ = v___y_2892_;
v___y_2823_ = v___y_2893_;
v___y_2824_ = v___y_2894_;
goto v___jp_2818_;
}
else
{
v___y_2828_ = v___y_2892_;
v___y_2829_ = v___y_2891_;
v___y_2830_ = v_isEq_2890_;
v___y_2831_ = v___y_2894_;
v___y_2832_ = v___y_2893_;
v___y_2833_ = v_fst_2900_;
v___y_2834_ = v_fst_2902_;
goto v___jp_2827_;
}
}
}
else
{
lean_dec(v_a_2908_);
lean_dec(v_val_2906_);
lean_dec(v_fst_2902_);
lean_dec(v_fst_2900_);
v___y_2819_ = v_isEq_2890_;
v_isHEq_2820_ = v___x_2514_;
v___y_2821_ = v___y_2891_;
v___y_2822_ = v___y_2892_;
v___y_2823_ = v___y_2893_;
v___y_2824_ = v___y_2894_;
goto v___jp_2818_;
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_val_2906_);
lean_dec(v_fst_2902_);
lean_dec(v_fst_2900_);
lean_dec_ref(v___x_2652_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2915_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2907_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2907_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_dec(v_a_2905_);
lean_dec(v_snd_2903_);
lean_dec(v_fst_2902_);
lean_dec(v_fst_2900_);
v___y_2819_ = v_isEq_2890_;
v_isHEq_2820_ = v___x_2514_;
v___y_2821_ = v___y_2891_;
v___y_2822_ = v___y_2892_;
v___y_2823_ = v___y_2893_;
v___y_2824_ = v___y_2894_;
goto v___jp_2818_;
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_snd_2903_);
lean_dec(v_fst_2902_);
lean_dec(v_fst_2900_);
lean_dec_ref(v___x_2652_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2923_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2904_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2904_);
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
lean_dec(v_a_2896_);
v___y_2819_ = v_isEq_2890_;
v_isHEq_2820_ = v___x_2608_;
v___y_2821_ = v___y_2891_;
v___y_2822_ = v___y_2892_;
v___y_2823_ = v___y_2893_;
v___y_2824_ = v___y_2894_;
goto v___jp_2818_;
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec_ref(v___x_2652_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2931_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2895_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2895_);
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
v___jp_2939_:
{
lean_object* v___x_2944_; 
lean_inc_ref(v___x_2652_);
v___x_2944_ = l_Lean_Meta_matchEq_x3f(v___x_2652_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2944_, 1);
if (lean_obj_tag(v_a_2945_) == 1)
{
lean_object* v_val_2946_; lean_object* v_snd_2947_; lean_object* v_fst_2948_; lean_object* v_snd_2949_; lean_object* v___x_2950_; 
v_val_2946_ = lean_ctor_get(v_a_2945_, 0);
lean_inc(v_val_2946_);
lean_dec_ref_known(v_a_2945_, 1);
v_snd_2947_ = lean_ctor_get(v_val_2946_, 1);
lean_inc(v_snd_2947_);
lean_dec(v_val_2946_);
v_fst_2948_ = lean_ctor_get(v_snd_2947_, 0);
lean_inc(v_fst_2948_);
v_snd_2949_ = lean_ctor_get(v_snd_2947_, 1);
lean_inc(v_snd_2949_);
lean_dec(v_snd_2947_);
v___x_2950_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2948_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
if (lean_obj_tag(v_a_2951_) == 1)
{
lean_object* v_val_2952_; lean_object* v___x_2953_; 
v_val_2952_ = lean_ctor_get(v_a_2951_, 0);
lean_inc(v_val_2952_);
lean_dec_ref_known(v_a_2951_, 1);
v___x_2953_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2949_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
if (lean_obj_tag(v_a_2954_) == 1)
{
lean_object* v_toConstantVal_2955_; lean_object* v_val_2956_; lean_object* v_toConstantVal_2957_; lean_object* v_name_2958_; lean_object* v_name_2959_; uint8_t v___x_2960_; 
v_toConstantVal_2955_ = lean_ctor_get(v_val_2952_, 0);
lean_inc_ref(v_toConstantVal_2955_);
lean_dec(v_val_2952_);
v_val_2956_ = lean_ctor_get(v_a_2954_, 0);
lean_inc(v_val_2956_);
lean_dec_ref_known(v_a_2954_, 1);
v_toConstantVal_2957_ = lean_ctor_get(v_val_2956_, 0);
lean_inc_ref(v_toConstantVal_2957_);
lean_dec(v_val_2956_);
v_name_2958_ = lean_ctor_get(v_toConstantVal_2955_, 0);
lean_inc(v_name_2958_);
lean_dec_ref(v_toConstantVal_2955_);
v_name_2959_ = lean_ctor_get(v_toConstantVal_2957_, 0);
lean_inc(v_name_2959_);
lean_dec_ref(v_toConstantVal_2957_);
v___x_2960_ = lean_name_eq(v_name_2958_, v_name_2959_);
lean_dec(v_name_2959_);
lean_dec(v_name_2958_);
if (v___x_2960_ == 0)
{
lean_dec_ref(v___x_2652_);
lean_dec_ref(v_config_2503_);
v___y_2541_ = v___y_2942_;
v___y_2542_ = v___y_2941_;
v___y_2543_ = v___y_2943_;
v___y_2544_ = v___y_2940_;
goto v___jp_2540_;
}
else
{
if (v___x_2608_ == 0)
{
lean_del_object(v___x_2537_);
v_isEq_2890_ = v___x_2514_;
v___y_2891_ = v___y_2940_;
v___y_2892_ = v___y_2941_;
v___y_2893_ = v___y_2942_;
v___y_2894_ = v___y_2943_;
goto v___jp_2889_;
}
else
{
lean_dec_ref(v___x_2652_);
lean_dec_ref(v_config_2503_);
v___y_2541_ = v___y_2942_;
v___y_2542_ = v___y_2941_;
v___y_2543_ = v___y_2943_;
v___y_2544_ = v___y_2940_;
goto v___jp_2540_;
}
}
}
else
{
lean_dec(v_a_2954_);
lean_dec(v_val_2952_);
lean_del_object(v___x_2537_);
v_isEq_2890_ = v___x_2514_;
v___y_2891_ = v___y_2940_;
v___y_2892_ = v___y_2941_;
v___y_2893_ = v___y_2942_;
v___y_2894_ = v___y_2943_;
goto v___jp_2889_;
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_val_2952_);
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2961_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2953_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2953_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_dec(v_a_2951_);
lean_dec(v_snd_2949_);
lean_del_object(v___x_2537_);
v_isEq_2890_ = v___x_2514_;
v___y_2891_ = v___y_2940_;
v___y_2892_ = v___y_2941_;
v___y_2893_ = v___y_2942_;
v___y_2894_ = v___y_2943_;
goto v___jp_2889_;
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_snd_2949_);
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2969_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2950_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2950_);
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
lean_dec(v_a_2945_);
lean_del_object(v___x_2537_);
v_isEq_2890_ = v___x_2608_;
v___y_2891_ = v___y_2940_;
v___y_2892_ = v___y_2941_;
v___y_2893_ = v___y_2942_;
v___y_2894_ = v___y_2943_;
goto v___jp_2889_;
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2977_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2944_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2944_);
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
v___jp_2985_:
{
lean_object* v___x_2990_; 
lean_inc_ref(v___x_2652_);
v___x_2990_ = l_refutableHasNotBit_x3f(v___x_2652_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
if (lean_obj_tag(v_a_2991_) == 1)
{
lean_object* v_val_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec_ref(v_config_2503_);
v_val_2992_ = lean_ctor_get(v_a_2991_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v_a_2991_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2994_ = v_a_2991_;
v_isShared_2995_ = v_isSharedCheck_3031_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_val_2992_);
lean_dec(v_a_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3031_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; 
lean_inc(v_mvarId_2504_);
v___x_2996_ = l_Lean_MVarId_getType(v_mvarId_2504_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = l_Lean_LocalDecl_toExpr(v_val_2535_);
v___x_2999_ = l_Lean_Meta_mkAbsurd(v_a_2997_, v_val_2992_, v___x_2998_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2504_, v_a_3000_, v___y_2987_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3004_; 
lean_dec_ref_known(v___x_3001_, 1);
v___x_3002_ = lean_box(v___x_2514_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_3002_);
v___x_3004_ = v___x_2994_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
lean_ctor_set(v___x_3005_, 1, v___x_2539_);
v_a_2521_ = v___x_3005_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_del_object(v___x_2994_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
v_a_3007_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_3001_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3001_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_del_object(v___x_2994_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_3015_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2999_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2999_);
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
lean_del_object(v___x_2994_);
lean_dec(v_val_2992_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_3023_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2996_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2996_);
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
}
else
{
lean_object* v___x_3032_; 
lean_dec(v_a_2991_);
lean_inc_ref(v___x_2652_);
v___x_3032_ = l_Lean_Meta_matchNe_x3f(v___x_2652_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
if (lean_obj_tag(v_a_3033_) == 1)
{
lean_object* v_val_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3103_; 
v_val_3034_ = lean_ctor_get(v_a_3033_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_a_3033_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3036_ = v_a_3033_;
v_isShared_3037_ = v_isSharedCheck_3103_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_val_3034_);
lean_dec(v_a_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3103_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v_snd_3038_; lean_object* v_fst_3039_; lean_object* v_snd_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3102_; 
v_snd_3038_ = lean_ctor_get(v_val_3034_, 1);
lean_inc(v_snd_3038_);
lean_dec(v_val_3034_);
v_fst_3039_ = lean_ctor_get(v_snd_3038_, 0);
v_snd_3040_ = lean_ctor_get(v_snd_3038_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_snd_3038_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3042_ = v_snd_3038_;
v_isShared_3043_ = v_isSharedCheck_3102_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_snd_3040_);
lean_inc(v_fst_3039_);
lean_dec(v_snd_3038_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3102_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; 
lean_inc(v_fst_3039_);
v___x_3044_ = l_Lean_Meta_isExprDefEq(v_fst_3039_, v_snd_3040_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; uint8_t v___x_3046_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = lean_unbox(v_a_3045_);
lean_dec(v_a_3045_);
if (v___x_3046_ == 0)
{
lean_del_object(v___x_3042_);
lean_dec(v_fst_3039_);
lean_del_object(v___x_3036_);
v___y_2940_ = v___y_2986_;
v___y_2941_ = v___y_2987_;
v___y_2942_ = v___y_2988_;
v___y_2943_ = v___y_2989_;
goto v___jp_2939_;
}
else
{
lean_object* v___x_3047_; 
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec_ref(v_config_2503_);
lean_inc(v_mvarId_2504_);
v___x_3047_ = l_Lean_MVarId_getType(v_mvarId_2504_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___x_3049_ = l_Lean_Meta_mkEqRefl(v_fst_3039_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref_known(v___x_3049_, 1);
v___x_3051_ = l_Lean_LocalDecl_toExpr(v_val_2535_);
v___x_3052_ = l_Lean_Meta_mkAbsurd(v_a_3048_, v_a_3050_, v___x_3051_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3054_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2504_, v_a_3053_, v___y_2987_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3057_; 
lean_dec_ref_known(v___x_3054_, 1);
v___x_3055_ = lean_box(v___x_2514_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3055_);
v___x_3057_ = v___x_3036_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3059_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 1, v___x_2539_);
lean_ctor_set(v___x_3042_, 0, v___x_3057_);
v___x_3059_ = v___x_3042_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_2539_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
v_a_2521_ = v___x_3059_;
goto v___jp_2520_;
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_del_object(v___x_3042_);
lean_del_object(v___x_3036_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
v_a_3062_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3054_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3054_);
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
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_del_object(v___x_3042_);
lean_del_object(v___x_3036_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_3070_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3052_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3052_);
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
lean_dec(v_a_3048_);
lean_del_object(v___x_3042_);
lean_del_object(v___x_3036_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_3078_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3049_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3049_);
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
lean_del_object(v___x_3042_);
lean_dec(v_fst_3039_);
lean_del_object(v___x_3036_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_3086_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3047_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3047_);
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
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_del_object(v___x_3042_);
lean_dec(v_fst_3039_);
lean_del_object(v___x_3036_);
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_3094_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3044_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3044_);
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
}
else
{
lean_dec(v_a_3033_);
v___y_2940_ = v___y_2986_;
v___y_2941_ = v___y_2987_;
v___y_2942_ = v___y_2988_;
v___y_2943_ = v___y_2989_;
goto v___jp_2939_;
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_3104_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3032_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3032_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v___x_2652_);
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_3112_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_2990_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_2990_);
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
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
v_a_2529_ = v___x_2580_;
goto v___jp_2528_;
}
v___jp_2540_:
{
lean_object* v___x_2545_; 
lean_inc(v_mvarId_2504_);
v___x_2545_ = l_Lean_MVarId_getType(v_mvarId_2504_, v___y_2544_, v___y_2542_, v___y_2541_, v___y_2543_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = l_Lean_LocalDecl_toExpr(v_val_2535_);
v___x_2548_ = l_Lean_Meta_mkNoConfusion(v_a_2546_, v___x_2547_, v___y_2544_, v___y_2542_, v___y_2541_, v___y_2543_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2504_, v_a_2549_, v___y_2542_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
lean_dec_ref_known(v___x_2550_, 1);
v___x_2551_ = lean_box(v___x_2514_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2551_);
v___x_2553_ = v___x_2537_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v___x_2539_);
v_a_2521_ = v___x_2554_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_del_object(v___x_2537_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
v_a_2556_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2550_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2550_);
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
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_del_object(v___x_2537_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_2564_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2548_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2548_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_del_object(v___x_2537_);
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
v_a_2572_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2545_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2545_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
v___jp_2581_:
{
lean_object* v_searchFuel_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_searchFuel_2586_ = lean_ctor_get(v_config_2503_, 0);
v___x_2587_ = l_Lean_LocalDecl_fvarId(v_val_2535_);
lean_dec(v_val_2535_);
lean_inc(v_searchFuel_2586_);
lean_inc(v_mvarId_2504_);
v___x_2588_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2504_, v___x_2587_, v_searchFuel_2586_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2582_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; uint8_t v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = lean_unbox(v_a_2589_);
lean_dec(v_a_2589_);
if (v___x_2590_ == 0)
{
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
v_a_2529_ = v___x_2580_;
goto v___jp_2528_;
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v___x_2591_ = lean_box(v___x_2514_);
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v___x_2539_);
v_a_2521_ = v___x_2593_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2594_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2588_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2588_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
v___jp_2602_:
{
if (v___y_2607_ == 0)
{
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
v_a_2529_ = v___x_2580_;
goto v___jp_2528_;
}
else
{
v___y_2582_ = v___y_2603_;
v___y_2583_ = v___y_2604_;
v___y_2584_ = v___y_2605_;
v___y_2585_ = v___y_2606_;
goto v___jp_2581_;
}
}
v___jp_2609_:
{
if (v___y_2613_ == 0)
{
v___y_2582_ = v___y_2610_;
v___y_2583_ = v___y_2611_;
v___y_2584_ = v___y_2612_;
v___y_2585_ = v___y_2614_;
goto v___jp_2581_;
}
else
{
v___y_2603_ = v___y_2610_;
v___y_2604_ = v___y_2611_;
v___y_2605_ = v___y_2612_;
v___y_2606_ = v___y_2614_;
v___y_2607_ = v___x_2608_;
goto v___jp_2602_;
}
}
v___jp_2615_:
{
if (v___y_2621_ == 0)
{
v___y_2603_ = v___y_2616_;
v___y_2604_ = v___y_2617_;
v___y_2605_ = v___y_2618_;
v___y_2606_ = v___y_2620_;
v___y_2607_ = v___x_2608_;
goto v___jp_2602_;
}
else
{
v___y_2610_ = v___y_2616_;
v___y_2611_ = v___y_2617_;
v___y_2612_ = v___y_2618_;
v___y_2613_ = v___y_2619_;
v___y_2614_ = v___y_2620_;
goto v___jp_2609_;
}
}
v___jp_2622_:
{
uint8_t v_emptyType_2629_; 
v_emptyType_2629_ = lean_ctor_get_uint8(v_config_2503_, sizeof(void*)*1 + 1);
if (v_emptyType_2629_ == 0)
{
v___y_2616_ = v___y_2628_;
v___y_2617_ = v___y_2625_;
v___y_2618_ = v___y_2626_;
v___y_2619_ = v___y_2624_;
v___y_2620_ = v___y_2627_;
v___y_2621_ = v___x_2608_;
goto v___jp_2615_;
}
else
{
if (v___y_2623_ == 0)
{
v___y_2610_ = v___y_2628_;
v___y_2611_ = v___y_2625_;
v___y_2612_ = v___y_2626_;
v___y_2613_ = v___y_2624_;
v___y_2614_ = v___y_2627_;
goto v___jp_2609_;
}
else
{
v___y_2616_ = v___y_2628_;
v___y_2617_ = v___y_2625_;
v___y_2618_ = v___y_2626_;
v___y_2619_ = v___y_2624_;
v___y_2620_ = v___y_2627_;
v___y_2621_ = v___x_2608_;
goto v___jp_2615_;
}
}
}
v___jp_2630_:
{
if (v___y_2637_ == 0)
{
v___y_2623_ = v___y_2631_;
v___y_2624_ = v___y_2633_;
v___y_2625_ = v___y_2634_;
v___y_2626_ = v___y_2636_;
v___y_2627_ = v___y_2635_;
v___y_2628_ = v___y_2632_;
goto v___jp_2622_;
}
else
{
lean_object* v___x_2638_; 
lean_inc(v_val_2535_);
lean_inc(v_mvarId_2504_);
v___x_2638_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2504_, v_val_2535_, v___y_2634_, v___y_2636_, v___y_2635_, v___y_2632_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; uint8_t v___x_2640_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2640_ = lean_unbox(v_a_2639_);
lean_dec(v_a_2639_);
if (v___x_2640_ == 0)
{
v___y_2623_ = v___y_2631_;
v___y_2624_ = v___y_2633_;
v___y_2625_ = v___y_2634_;
v___y_2626_ = v___y_2636_;
v___y_2627_ = v___y_2635_;
v___y_2628_ = v___y_2632_;
goto v___jp_2622_;
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
lean_dec(v_val_2535_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v___x_2641_ = lean_box(v___x_2514_);
v___x_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
v___x_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
lean_ctor_set(v___x_2643_, 1, v___x_2539_);
v_a_2521_ = v___x_2643_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_val_2535_);
lean_del_object(v___x_2518_);
lean_dec(v_snd_2516_);
lean_dec(v_mvarId_2504_);
lean_dec_ref(v_config_2503_);
v_a_2644_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2638_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2638_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
}
}
v___jp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_a_2521_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2522_);
v___x_2524_ = v___x_2518_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_snd_2516_);
v___x_2524_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
return v___x_2525_;
}
}
v___jp_2528_:
{
lean_object* v___x_2530_; size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2527_);
lean_ctor_set(v___x_2530_, 1, v_a_2529_);
v___x_2531_ = ((size_t)1ULL);
v___x_2532_ = lean_usize_add(v_i_2507_, v___x_2531_);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2503_, v_mvarId_2504_, v_as_2505_, v_sz_2506_, v___x_2532_, v___x_2530_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3186_, lean_object* v_mvarId_3187_, lean_object* v_as_3188_, lean_object* v_sz_3189_, lean_object* v_i_3190_, lean_object* v_b_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
size_t v_sz_boxed_3197_; size_t v_i_boxed_3198_; lean_object* v_res_3199_; 
v_sz_boxed_3197_ = lean_unbox_usize(v_sz_3189_);
lean_dec(v_sz_3189_);
v_i_boxed_3198_ = lean_unbox_usize(v_i_3190_);
lean_dec(v_i_3190_);
v_res_3199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3186_, v_mvarId_3187_, v_as_3188_, v_sz_boxed_3197_, v_i_boxed_3198_, v_b_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec_ref(v_as_3188_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3203_, lean_object* v_mvarId_3204_, lean_object* v_as_3205_, size_t v_sz_3206_, size_t v_i_3207_, lean_object* v_b_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
uint8_t v___x_3214_; 
v___x_3214_ = lean_usize_dec_lt(v_i_3207_, v_sz_3206_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; 
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v_b_3208_);
return v___x_3215_;
}
else
{
lean_object* v_snd_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3904_; 
v_snd_3216_ = lean_ctor_get(v_b_3208_, 1);
v_isSharedCheck_3904_ = !lean_is_exclusive(v_b_3208_);
if (v_isSharedCheck_3904_ == 0)
{
lean_object* v_unused_3905_; 
v_unused_3905_ = lean_ctor_get(v_b_3208_, 0);
lean_dec(v_unused_3905_);
v___x_3218_ = v_b_3208_;
v_isShared_3219_ = v_isSharedCheck_3904_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_snd_3216_);
lean_dec(v_b_3208_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3904_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v_a_3221_; lean_object* v___x_3227_; lean_object* v_a_3229_; lean_object* v_a_3234_; 
v___x_3227_ = lean_box(0);
v_a_3234_ = lean_array_uget(v_as_3205_, v_i_3207_);
if (lean_obj_tag(v_a_3234_) == 0)
{
lean_del_object(v___x_3218_);
v_a_3229_ = v_snd_3216_;
goto v___jp_3228_;
}
else
{
lean_object* v_val_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3903_; 
v_val_3235_ = lean_ctor_get(v_a_3234_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v_a_3234_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3237_ = v_a_3234_;
v_isShared_3238_ = v_isSharedCheck_3903_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_val_3235_);
lean_dec(v_a_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3903_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___x_3281_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; uint8_t v___y_3309_; uint8_t v___x_3310_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; uint8_t v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; uint8_t v___y_3321_; lean_object* v___y_3322_; uint8_t v___y_3323_; uint8_t v___y_3325_; uint8_t v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3333_; lean_object* v___y_3334_; uint8_t v___y_3335_; lean_object* v___y_3336_; uint8_t v___y_3337_; lean_object* v___y_3338_; uint8_t v___y_3339_; 
v___x_3239_ = lean_box(0);
v___x_3281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3310_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3235_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3355_; uint8_t v___y_3357_; uint8_t v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3366_; lean_object* v___y_3367_; uint8_t v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; uint8_t v___y_3371_; lean_object* v___y_3372_; uint8_t v___y_3373_; lean_object* v___y_3376_; lean_object* v___y_3377_; uint8_t v___y_3378_; lean_object* v___y_3379_; uint8_t v___y_3380_; lean_object* v___y_3381_; lean_object* v_a_3382_; lean_object* v___y_3386_; lean_object* v___y_3387_; uint8_t v___y_3388_; lean_object* v___y_3389_; uint8_t v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3484_; lean_object* v___y_3485_; uint8_t v___y_3486_; lean_object* v___y_3487_; uint8_t v___y_3488_; lean_object* v___y_3489_; uint8_t v___y_3490_; lean_object* v___y_3492_; lean_object* v___y_3493_; uint8_t v___y_3494_; lean_object* v___y_3495_; uint8_t v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; uint8_t v___y_3499_; lean_object* v___y_3502_; lean_object* v___y_3503_; uint8_t v___y_3504_; lean_object* v___y_3505_; uint8_t v___y_3506_; lean_object* v___y_3507_; uint8_t v___y_3508_; lean_object* v___y_3521_; lean_object* v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; uint8_t v___y_3525_; lean_object* v___y_3526_; uint8_t v___y_3527_; uint8_t v___y_3529_; uint8_t v_isHEq_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; uint8_t v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; uint8_t v_isEq_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___x_3833_; 
v___x_3355_ = l_Lean_LocalDecl_type(v_val_3235_);
lean_inc_ref(v___x_3355_);
v___x_3833_ = l_Lean_Meta_matchNot_x3f(v___x_3355_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
if (lean_obj_tag(v_a_3834_) == 1)
{
lean_object* v_val_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3894_; 
v_val_3835_ = lean_ctor_get(v_a_3834_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_a_3834_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3837_ = v_a_3834_;
v_isShared_3838_ = v_isSharedCheck_3894_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_val_3835_);
lean_dec(v_a_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3894_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3835_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v___x_3839_, 1);
if (lean_obj_tag(v_a_3840_) == 1)
{
lean_object* v_val_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec_ref(v_config_3203_);
v_val_3841_ = lean_ctor_get(v_a_3840_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_a_3840_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3843_ = v_a_3840_;
v_isShared_3844_ = v_isSharedCheck_3885_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_val_3841_);
lean_dec(v_a_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3885_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; 
lean_inc(v_mvarId_3204_);
v___x_3845_ = l_Lean_MVarId_getType(v_mvarId_3204_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___x_3847_ = l_Lean_LocalDecl_toExpr(v_val_3235_);
v___x_3848_ = l_Lean_mkFVar(v_val_3841_);
v___x_3849_ = l_Lean_Expr_app___override(v___x_3847_, v___x_3848_);
v___x_3850_ = l_Lean_Meta_mkFalseElim(v_a_3846_, v___x_3849_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3852_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v___x_3852_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3204_, v_a_3851_, v___y_3210_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3855_; 
lean_dec_ref_known(v___x_3852_, 1);
v___x_3853_ = lean_box(v___x_3214_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3853_);
v___x_3855_ = v___x_3843_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
lean_ctor_set(v___x_3856_, 1, v___x_3239_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set_tag(v___x_3837_, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3856_);
v___x_3858_ = v___x_3837_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
v_a_3221_ = v___x_3858_;
goto v___jp_3220_;
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_del_object(v___x_3843_);
lean_del_object(v___x_3837_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
v_a_3861_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3852_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3852_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_del_object(v___x_3843_);
lean_del_object(v___x_3837_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3869_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3850_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3850_);
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
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_del_object(v___x_3843_);
lean_dec(v_val_3841_);
lean_del_object(v___x_3837_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3877_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3845_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3845_);
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
lean_dec(v_a_3840_);
lean_del_object(v___x_3837_);
v___y_3697_ = v___y_3209_;
v___y_3698_ = v___y_3210_;
v___y_3699_ = v___y_3211_;
v___y_3700_ = v___y_3212_;
goto v___jp_3696_;
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_del_object(v___x_3837_);
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3886_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3839_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3839_);
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
}
}
else
{
lean_dec(v_a_3834_);
v___y_3697_ = v___y_3209_;
v___y_3698_ = v___y_3210_;
v___y_3699_ = v___y_3211_;
v___y_3700_ = v___y_3212_;
goto v___jp_3696_;
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3895_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3833_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3833_);
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
v___jp_3356_:
{
uint8_t v_genDiseq_3363_; 
v_genDiseq_3363_ = lean_ctor_get_uint8(v_config_3203_, sizeof(void*)*1 + 2);
if (v_genDiseq_3363_ == 0)
{
lean_dec_ref(v___x_3355_);
v___y_3333_ = v___y_3362_;
v___y_3334_ = v___y_3360_;
v___y_3335_ = v___y_3357_;
v___y_3336_ = v___y_3361_;
v___y_3337_ = v___y_3358_;
v___y_3338_ = v___y_3359_;
v___y_3339_ = v___x_3310_;
goto v___jp_3332_;
}
else
{
uint8_t v___x_3364_; 
v___x_3364_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3355_);
v___y_3333_ = v___y_3362_;
v___y_3334_ = v___y_3360_;
v___y_3335_ = v___y_3357_;
v___y_3336_ = v___y_3361_;
v___y_3337_ = v___y_3358_;
v___y_3338_ = v___y_3359_;
v___y_3339_ = v___x_3364_;
goto v___jp_3332_;
}
}
v___jp_3365_:
{
if (v___y_3373_ == 0)
{
lean_dec_ref(v___y_3370_);
v___y_3357_ = v___y_3368_;
v___y_3358_ = v___y_3371_;
v___y_3359_ = v___y_3372_;
v___y_3360_ = v___y_3369_;
v___y_3361_ = v___y_3366_;
v___y_3362_ = v___y_3367_;
goto v___jp_3356_;
}
else
{
lean_object* v___x_3374_; 
lean_dec_ref(v___x_3355_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v___x_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___y_3370_);
return v___x_3374_;
}
}
v___jp_3375_:
{
uint8_t v___x_3383_; 
v___x_3383_ = l_Lean_Exception_isInterrupt(v_a_3382_);
if (v___x_3383_ == 0)
{
uint8_t v___x_3384_; 
lean_inc_ref(v_a_3382_);
v___x_3384_ = l_Lean_Exception_isRuntime(v_a_3382_);
v___y_3366_ = v___y_3376_;
v___y_3367_ = v___y_3377_;
v___y_3368_ = v___y_3378_;
v___y_3369_ = v___y_3379_;
v___y_3370_ = v_a_3382_;
v___y_3371_ = v___y_3380_;
v___y_3372_ = v___y_3381_;
v___y_3373_ = v___x_3384_;
goto v___jp_3365_;
}
else
{
v___y_3366_ = v___y_3376_;
v___y_3367_ = v___y_3377_;
v___y_3368_ = v___y_3378_;
v___y_3369_ = v___y_3379_;
v___y_3370_ = v_a_3382_;
v___y_3371_ = v___y_3380_;
v___y_3372_ = v___y_3381_;
v___y_3373_ = v___x_3383_;
goto v___jp_3365_;
}
}
v___jp_3385_:
{
lean_object* v___x_3392_; 
lean_inc_ref(v___x_3355_);
v___x_3392_ = l_Lean_Meta_mkDecide(v___x_3355_, v___y_3391_, v___y_3389_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3394_; uint8_t v_foApprox_3395_; uint8_t v_ctxApprox_3396_; uint8_t v_quasiPatternApprox_3397_; uint8_t v_constApprox_3398_; uint8_t v_isDefEqStuckEx_3399_; uint8_t v_unificationHints_3400_; uint8_t v_proofIrrelevance_3401_; uint8_t v_assignSyntheticOpaque_3402_; uint8_t v_offsetCnstrs_3403_; uint8_t v_etaStruct_3404_; uint8_t v_univApprox_3405_; uint8_t v_iota_3406_; uint8_t v_beta_3407_; uint8_t v_proj_3408_; uint8_t v_zeta_3409_; uint8_t v_zetaDelta_3410_; uint8_t v_zetaUnused_3411_; uint8_t v_zetaHave_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3481_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v___x_3394_ = l_Lean_Meta_Context_config(v___y_3391_);
v_foApprox_3395_ = lean_ctor_get_uint8(v___x_3394_, 0);
v_ctxApprox_3396_ = lean_ctor_get_uint8(v___x_3394_, 1);
v_quasiPatternApprox_3397_ = lean_ctor_get_uint8(v___x_3394_, 2);
v_constApprox_3398_ = lean_ctor_get_uint8(v___x_3394_, 3);
v_isDefEqStuckEx_3399_ = lean_ctor_get_uint8(v___x_3394_, 4);
v_unificationHints_3400_ = lean_ctor_get_uint8(v___x_3394_, 5);
v_proofIrrelevance_3401_ = lean_ctor_get_uint8(v___x_3394_, 6);
v_assignSyntheticOpaque_3402_ = lean_ctor_get_uint8(v___x_3394_, 7);
v_offsetCnstrs_3403_ = lean_ctor_get_uint8(v___x_3394_, 8);
v_etaStruct_3404_ = lean_ctor_get_uint8(v___x_3394_, 10);
v_univApprox_3405_ = lean_ctor_get_uint8(v___x_3394_, 11);
v_iota_3406_ = lean_ctor_get_uint8(v___x_3394_, 12);
v_beta_3407_ = lean_ctor_get_uint8(v___x_3394_, 13);
v_proj_3408_ = lean_ctor_get_uint8(v___x_3394_, 14);
v_zeta_3409_ = lean_ctor_get_uint8(v___x_3394_, 15);
v_zetaDelta_3410_ = lean_ctor_get_uint8(v___x_3394_, 16);
v_zetaUnused_3411_ = lean_ctor_get_uint8(v___x_3394_, 17);
v_zetaHave_3412_ = lean_ctor_get_uint8(v___x_3394_, 18);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3414_ = v___x_3394_;
v_isShared_3415_ = v_isSharedCheck_3481_;
goto v_resetjp_3413_;
}
else
{
lean_dec(v___x_3394_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3481_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
uint8_t v_trackZetaDelta_3416_; lean_object* v_zetaDeltaSet_3417_; lean_object* v_lctx_3418_; lean_object* v_localInstances_3419_; lean_object* v_defEqCtx_x3f_3420_; lean_object* v_synthPendingDepth_3421_; lean_object* v_canUnfold_x3f_3422_; uint8_t v_univApprox_3423_; uint8_t v_inTypeClassResolution_3424_; uint8_t v_cacheInferType_3425_; uint8_t v___x_3426_; lean_object* v_config_3428_; 
v_trackZetaDelta_3416_ = lean_ctor_get_uint8(v___y_3391_, sizeof(void*)*7);
v_zetaDeltaSet_3417_ = lean_ctor_get(v___y_3391_, 1);
v_lctx_3418_ = lean_ctor_get(v___y_3391_, 2);
v_localInstances_3419_ = lean_ctor_get(v___y_3391_, 3);
v_defEqCtx_x3f_3420_ = lean_ctor_get(v___y_3391_, 4);
v_synthPendingDepth_3421_ = lean_ctor_get(v___y_3391_, 5);
v_canUnfold_x3f_3422_ = lean_ctor_get(v___y_3391_, 6);
v_univApprox_3423_ = lean_ctor_get_uint8(v___y_3391_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3424_ = lean_ctor_get_uint8(v___y_3391_, sizeof(void*)*7 + 2);
v_cacheInferType_3425_ = lean_ctor_get_uint8(v___y_3391_, sizeof(void*)*7 + 3);
v___x_3426_ = 1;
if (v_isShared_3415_ == 0)
{
v_config_3428_ = v___x_3414_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 0, v_foApprox_3395_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 1, v_ctxApprox_3396_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 2, v_quasiPatternApprox_3397_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 3, v_constApprox_3398_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 4, v_isDefEqStuckEx_3399_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 5, v_unificationHints_3400_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 6, v_proofIrrelevance_3401_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 7, v_assignSyntheticOpaque_3402_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 8, v_offsetCnstrs_3403_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 10, v_etaStruct_3404_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 11, v_univApprox_3405_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 12, v_iota_3406_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 13, v_beta_3407_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 14, v_proj_3408_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 15, v_zeta_3409_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 16, v_zetaDelta_3410_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 17, v_zetaUnused_3411_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, 18, v_zetaHave_3412_);
v_config_3428_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
uint64_t v___x_3429_; uint64_t v___x_3430_; uint64_t v___x_3431_; uint64_t v___x_3432_; uint64_t v___x_3433_; uint64_t v_key_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_ctor_set_uint8(v_config_3428_, 9, v___x_3426_);
v___x_3429_ = l_Lean_Meta_Context_configKey(v___y_3391_);
v___x_3430_ = 3ULL;
v___x_3431_ = lean_uint64_shift_right(v___x_3429_, v___x_3430_);
v___x_3432_ = lean_uint64_shift_left(v___x_3431_, v___x_3430_);
v___x_3433_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_3434_ = lean_uint64_lor(v___x_3432_, v___x_3433_);
v___x_3435_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3435_, 0, v_config_3428_);
lean_ctor_set_uint64(v___x_3435_, sizeof(void*)*1, v_key_3434_);
lean_inc(v_canUnfold_x3f_3422_);
lean_inc(v_synthPendingDepth_3421_);
lean_inc(v_defEqCtx_x3f_3420_);
lean_inc_ref(v_localInstances_3419_);
lean_inc_ref(v_lctx_3418_);
lean_inc(v_zetaDeltaSet_3417_);
v___x_3436_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
lean_ctor_set(v___x_3436_, 1, v_zetaDeltaSet_3417_);
lean_ctor_set(v___x_3436_, 2, v_lctx_3418_);
lean_ctor_set(v___x_3436_, 3, v_localInstances_3419_);
lean_ctor_set(v___x_3436_, 4, v_defEqCtx_x3f_3420_);
lean_ctor_set(v___x_3436_, 5, v_synthPendingDepth_3421_);
lean_ctor_set(v___x_3436_, 6, v_canUnfold_x3f_3422_);
lean_ctor_set_uint8(v___x_3436_, sizeof(void*)*7, v_trackZetaDelta_3416_);
lean_ctor_set_uint8(v___x_3436_, sizeof(void*)*7 + 1, v_univApprox_3423_);
lean_ctor_set_uint8(v___x_3436_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3424_);
lean_ctor_set_uint8(v___x_3436_, sizeof(void*)*7 + 3, v_cacheInferType_3425_);
lean_inc(v___y_3387_);
lean_inc_ref(v___y_3386_);
lean_inc(v___y_3389_);
lean_inc(v_a_3393_);
v___x_3437_ = lean_whnf(v_a_3393_, v___x_3436_, v___y_3389_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; uint8_t v___x_3440_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_3440_ = l_Lean_Expr_isConstOf(v_a_3438_, v___x_3439_);
lean_dec(v_a_3438_);
if (v___x_3440_ == 0)
{
lean_dec(v_a_3393_);
v___y_3357_ = v___y_3388_;
v___y_3358_ = v___y_3390_;
v___y_3359_ = v___y_3391_;
v___y_3360_ = v___y_3389_;
v___y_3361_ = v___y_3386_;
v___y_3362_ = v___y_3387_;
goto v___jp_3356_;
}
else
{
lean_object* v___x_3441_; 
lean_inc(v_a_3393_);
v___x_3441_ = l_Lean_Meta_mkEqRefl(v_a_3393_, v___y_3391_, v___y_3389_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3441_, 1);
lean_inc(v_mvarId_3204_);
v___x_3443_ = l_Lean_MVarId_getType(v_mvarId_3204_, v___y_3391_, v___y_3389_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v_nargs_3445_; lean_object* v___x_3446_; lean_object* v_dummy_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v___x_3443_, 1);
v_nargs_3445_ = l_Lean_Expr_getAppNumArgs(v_a_3393_);
v___x_3446_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_3447_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_3445_);
v___x_3448_ = lean_mk_array(v_nargs_3445_, v_dummy_3447_);
v___x_3449_ = lean_unsigned_to_nat(1u);
v___x_3450_ = lean_nat_sub(v_nargs_3445_, v___x_3449_);
lean_dec(v_nargs_3445_);
v___x_3451_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3393_, v___x_3448_, v___x_3450_);
v___x_3452_ = lean_array_push(v___x_3451_, v_a_3442_);
v___x_3453_ = l_Lean_mkAppN(v___x_3446_, v___x_3452_);
lean_dec_ref(v___x_3452_);
lean_inc(v_val_3235_);
v___x_3454_ = l_Lean_LocalDecl_toExpr(v_val_3235_);
v___x_3455_ = l_Lean_Meta_mkAbsurd(v_a_3444_, v___x_3454_, v___x_3453_, v___y_3391_, v___y_3389_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3475_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3475_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3475_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; 
lean_inc(v_mvarId_3204_);
v___x_3460_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3204_, v_a_3456_, v___y_3389_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3472_; 
lean_dec_ref(v___x_3355_);
lean_dec(v_val_3235_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v___x_3460_, 0);
lean_dec(v_unused_3473_);
v___x_3462_ = v___x_3460_;
v_isShared_3463_ = v_isSharedCheck_3472_;
goto v_resetjp_3461_;
}
else
{
lean_dec(v___x_3460_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3472_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3464_ = lean_box(v___x_3214_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set_tag(v___x_3462_, 1);
lean_ctor_set(v___x_3462_, 0, v___x_3464_);
v___x_3466_ = v___x_3462_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
lean_ctor_set(v___x_3467_, 1, v___x_3239_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3467_);
v___x_3469_ = v___x_3458_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
v_a_3221_ = v___x_3469_;
goto v___jp_3220_;
}
}
}
}
else
{
lean_object* v_a_3474_; 
lean_del_object(v___x_3458_);
v_a_3474_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3460_, 1);
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3389_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3391_;
v_a_3382_ = v_a_3474_;
goto v___jp_3375_;
}
}
}
else
{
lean_object* v_a_3476_; 
v_a_3476_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3455_, 1);
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3389_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3391_;
v_a_3382_ = v_a_3476_;
goto v___jp_3375_;
}
}
else
{
lean_object* v_a_3477_; 
lean_dec(v_a_3442_);
lean_dec(v_a_3393_);
v_a_3477_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3443_, 1);
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3389_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3391_;
v_a_3382_ = v_a_3477_;
goto v___jp_3375_;
}
}
else
{
lean_object* v_a_3478_; 
lean_dec(v_a_3393_);
v_a_3478_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3441_, 1);
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3389_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3391_;
v_a_3382_ = v_a_3478_;
goto v___jp_3375_;
}
}
}
else
{
lean_object* v_a_3479_; 
lean_dec(v_a_3393_);
v_a_3479_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3437_, 1);
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3389_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3391_;
v_a_3382_ = v_a_3479_;
goto v___jp_3375_;
}
}
}
}
else
{
lean_object* v_a_3482_; 
v_a_3482_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3392_, 1);
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3389_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3391_;
v_a_3382_ = v_a_3482_;
goto v___jp_3375_;
}
}
v___jp_3483_:
{
if (v___y_3490_ == 0)
{
v___y_3357_ = v___y_3486_;
v___y_3358_ = v___y_3488_;
v___y_3359_ = v___y_3489_;
v___y_3360_ = v___y_3487_;
v___y_3361_ = v___y_3484_;
v___y_3362_ = v___y_3485_;
goto v___jp_3356_;
}
else
{
v___y_3386_ = v___y_3484_;
v___y_3387_ = v___y_3485_;
v___y_3388_ = v___y_3486_;
v___y_3389_ = v___y_3487_;
v___y_3390_ = v___y_3488_;
v___y_3391_ = v___y_3489_;
goto v___jp_3385_;
}
}
v___jp_3491_:
{
if (v___y_3499_ == 0)
{
lean_dec_ref(v___y_3497_);
v___y_3484_ = v___y_3492_;
v___y_3485_ = v___y_3493_;
v___y_3486_ = v___y_3494_;
v___y_3487_ = v___y_3495_;
v___y_3488_ = v___y_3496_;
v___y_3489_ = v___y_3498_;
v___y_3490_ = v___x_3310_;
goto v___jp_3483_;
}
else
{
uint8_t v___x_3500_; 
v___x_3500_ = l_Lean_Expr_hasFVar(v___y_3497_);
lean_dec_ref(v___y_3497_);
if (v___x_3500_ == 0)
{
v___y_3386_ = v___y_3492_;
v___y_3387_ = v___y_3493_;
v___y_3388_ = v___y_3494_;
v___y_3389_ = v___y_3495_;
v___y_3390_ = v___y_3496_;
v___y_3391_ = v___y_3498_;
goto v___jp_3385_;
}
else
{
v___y_3484_ = v___y_3492_;
v___y_3485_ = v___y_3493_;
v___y_3486_ = v___y_3494_;
v___y_3487_ = v___y_3495_;
v___y_3488_ = v___y_3496_;
v___y_3489_ = v___y_3498_;
v___y_3490_ = v___x_3310_;
goto v___jp_3483_;
}
}
}
v___jp_3501_:
{
lean_object* v___x_3509_; 
lean_inc_ref(v___x_3355_);
v___x_3509_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3355_, v___y_3505_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; uint8_t v___x_3511_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = l_Lean_Expr_hasMVar(v_a_3510_);
if (v___x_3511_ == 0)
{
v___y_3492_ = v___y_3502_;
v___y_3493_ = v___y_3503_;
v___y_3494_ = v___y_3504_;
v___y_3495_ = v___y_3505_;
v___y_3496_ = v___y_3506_;
v___y_3497_ = v_a_3510_;
v___y_3498_ = v___y_3507_;
v___y_3499_ = v___y_3508_;
goto v___jp_3491_;
}
else
{
v___y_3492_ = v___y_3502_;
v___y_3493_ = v___y_3503_;
v___y_3494_ = v___y_3504_;
v___y_3495_ = v___y_3505_;
v___y_3496_ = v___y_3506_;
v___y_3497_ = v_a_3510_;
v___y_3498_ = v___y_3507_;
v___y_3499_ = v___x_3310_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v___x_3355_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3512_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3509_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3509_);
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
v___jp_3520_:
{
if (v___y_3527_ == 0)
{
v___y_3357_ = v___y_3523_;
v___y_3358_ = v___y_3525_;
v___y_3359_ = v___y_3526_;
v___y_3360_ = v___y_3524_;
v___y_3361_ = v___y_3521_;
v___y_3362_ = v___y_3522_;
goto v___jp_3356_;
}
else
{
v___y_3502_ = v___y_3521_;
v___y_3503_ = v___y_3522_;
v___y_3504_ = v___y_3523_;
v___y_3505_ = v___y_3524_;
v___y_3506_ = v___y_3525_;
v___y_3507_ = v___y_3526_;
v___y_3508_ = v___y_3527_;
goto v___jp_3501_;
}
}
v___jp_3528_:
{
uint8_t v_useDecide_3535_; 
v_useDecide_3535_ = lean_ctor_get_uint8(v_config_3203_, sizeof(void*)*1);
if (v_useDecide_3535_ == 0)
{
v___y_3521_ = v___y_3533_;
v___y_3522_ = v___y_3534_;
v___y_3523_ = v___y_3529_;
v___y_3524_ = v___y_3532_;
v___y_3525_ = v_isHEq_3530_;
v___y_3526_ = v___y_3531_;
v___y_3527_ = v___x_3310_;
goto v___jp_3520_;
}
else
{
uint8_t v___x_3536_; 
v___x_3536_ = l_Lean_Expr_hasFVar(v___x_3355_);
if (v___x_3536_ == 0)
{
v___y_3502_ = v___y_3533_;
v___y_3503_ = v___y_3534_;
v___y_3504_ = v___y_3529_;
v___y_3505_ = v___y_3532_;
v___y_3506_ = v_isHEq_3530_;
v___y_3507_ = v___y_3531_;
v___y_3508_ = v_useDecide_3535_;
goto v___jp_3501_;
}
else
{
v___y_3521_ = v___y_3533_;
v___y_3522_ = v___y_3534_;
v___y_3523_ = v___y_3529_;
v___y_3524_ = v___y_3532_;
v___y_3525_ = v_isHEq_3530_;
v___y_3526_ = v___y_3531_;
v___y_3527_ = v___x_3310_;
goto v___jp_3520_;
}
}
}
v___jp_3537_:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_Meta_isExprDefEq(v___y_3542_, v___y_3543_, v___y_3544_, v___y_3540_, v___y_3539_, v___y_3538_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; uint8_t v___x_3547_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = lean_unbox(v_a_3546_);
lean_dec(v_a_3546_);
if (v___x_3547_ == 0)
{
v___y_3529_ = v___y_3541_;
v_isHEq_3530_ = v___x_3214_;
v___y_3531_ = v___y_3544_;
v___y_3532_ = v___y_3540_;
v___y_3533_ = v___y_3539_;
v___y_3534_ = v___y_3538_;
goto v___jp_3528_;
}
else
{
lean_object* v___x_3548_; 
lean_dec_ref(v___x_3355_);
lean_dec_ref(v_config_3203_);
lean_inc(v_mvarId_3204_);
v___x_3548_ = l_Lean_MVarId_getType(v_mvarId_3204_, v___y_3544_, v___y_3540_, v___y_3539_, v___y_3538_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3550_ = l_Lean_LocalDecl_toExpr(v_val_3235_);
v___x_3551_ = l_Lean_Meta_mkEqOfHEq(v___x_3550_, v___x_3214_, v___y_3544_, v___y_3540_, v___y_3539_, v___y_3538_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3553_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v___x_3553_ = l_Lean_Meta_mkNoConfusion(v_a_3549_, v_a_3552_, v___y_3544_, v___y_3540_, v___y_3539_, v___y_3538_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3555_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3204_, v_a_3554_, v___y_3540_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
lean_dec_ref_known(v___x_3555_, 1);
v___x_3556_ = lean_box(v___x_3214_);
v___x_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
v___x_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
lean_ctor_set(v___x_3558_, 1, v___x_3239_);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
v_a_3221_ = v___x_3559_;
goto v___jp_3220_;
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
v_a_3560_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3555_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3555_);
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
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3568_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3553_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3553_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec(v_a_3549_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3576_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3551_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3551_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3584_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3548_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3548_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec_ref(v___x_3355_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3592_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3545_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3545_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
v___jp_3600_:
{
lean_object* v___x_3606_; 
lean_inc_ref(v___x_3355_);
v___x_3606_ = l_Lean_Meta_matchHEq_x3f(v___x_3355_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
if (lean_obj_tag(v_a_3607_) == 1)
{
lean_object* v_val_3608_; lean_object* v_snd_3609_; lean_object* v_snd_3610_; lean_object* v_fst_3611_; lean_object* v_fst_3612_; lean_object* v_fst_3613_; lean_object* v_snd_3614_; lean_object* v___x_3615_; 
v_val_3608_ = lean_ctor_get(v_a_3607_, 0);
lean_inc(v_val_3608_);
lean_dec_ref_known(v_a_3607_, 1);
v_snd_3609_ = lean_ctor_get(v_val_3608_, 1);
lean_inc(v_snd_3609_);
v_snd_3610_ = lean_ctor_get(v_snd_3609_, 1);
lean_inc(v_snd_3610_);
v_fst_3611_ = lean_ctor_get(v_val_3608_, 0);
lean_inc(v_fst_3611_);
lean_dec(v_val_3608_);
v_fst_3612_ = lean_ctor_get(v_snd_3609_, 0);
lean_inc(v_fst_3612_);
lean_dec(v_snd_3609_);
v_fst_3613_ = lean_ctor_get(v_snd_3610_, 0);
lean_inc(v_fst_3613_);
v_snd_3614_ = lean_ctor_get(v_snd_3610_, 1);
lean_inc(v_snd_3614_);
lean_dec(v_snd_3610_);
v___x_3615_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3612_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
if (lean_obj_tag(v_a_3616_) == 1)
{
lean_object* v_val_3617_; lean_object* v___x_3618_; 
v_val_3617_ = lean_ctor_get(v_a_3616_, 0);
lean_inc(v_val_3617_);
lean_dec_ref_known(v_a_3616_, 1);
v___x_3618_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3614_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
if (lean_obj_tag(v_a_3619_) == 1)
{
lean_object* v_toConstantVal_3620_; lean_object* v_val_3621_; lean_object* v_toConstantVal_3622_; lean_object* v_name_3623_; lean_object* v_name_3624_; uint8_t v___x_3625_; 
v_toConstantVal_3620_ = lean_ctor_get(v_val_3617_, 0);
lean_inc_ref(v_toConstantVal_3620_);
lean_dec(v_val_3617_);
v_val_3621_ = lean_ctor_get(v_a_3619_, 0);
lean_inc(v_val_3621_);
lean_dec_ref_known(v_a_3619_, 1);
v_toConstantVal_3622_ = lean_ctor_get(v_val_3621_, 0);
lean_inc_ref(v_toConstantVal_3622_);
lean_dec(v_val_3621_);
v_name_3623_ = lean_ctor_get(v_toConstantVal_3620_, 0);
lean_inc(v_name_3623_);
lean_dec_ref(v_toConstantVal_3620_);
v_name_3624_ = lean_ctor_get(v_toConstantVal_3622_, 0);
lean_inc(v_name_3624_);
lean_dec_ref(v_toConstantVal_3622_);
v___x_3625_ = lean_name_eq(v_name_3623_, v_name_3624_);
lean_dec(v_name_3624_);
lean_dec(v_name_3623_);
if (v___x_3625_ == 0)
{
v___y_3538_ = v___y_3605_;
v___y_3539_ = v___y_3604_;
v___y_3540_ = v___y_3603_;
v___y_3541_ = v_isEq_3601_;
v___y_3542_ = v_fst_3611_;
v___y_3543_ = v_fst_3613_;
v___y_3544_ = v___y_3602_;
goto v___jp_3537_;
}
else
{
if (v___x_3310_ == 0)
{
lean_dec(v_fst_3613_);
lean_dec(v_fst_3611_);
v___y_3529_ = v_isEq_3601_;
v_isHEq_3530_ = v___x_3214_;
v___y_3531_ = v___y_3602_;
v___y_3532_ = v___y_3603_;
v___y_3533_ = v___y_3604_;
v___y_3534_ = v___y_3605_;
goto v___jp_3528_;
}
else
{
v___y_3538_ = v___y_3605_;
v___y_3539_ = v___y_3604_;
v___y_3540_ = v___y_3603_;
v___y_3541_ = v_isEq_3601_;
v___y_3542_ = v_fst_3611_;
v___y_3543_ = v_fst_3613_;
v___y_3544_ = v___y_3602_;
goto v___jp_3537_;
}
}
}
else
{
lean_dec(v_a_3619_);
lean_dec(v_val_3617_);
lean_dec(v_fst_3613_);
lean_dec(v_fst_3611_);
v___y_3529_ = v_isEq_3601_;
v_isHEq_3530_ = v___x_3214_;
v___y_3531_ = v___y_3602_;
v___y_3532_ = v___y_3603_;
v___y_3533_ = v___y_3604_;
v___y_3534_ = v___y_3605_;
goto v___jp_3528_;
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v_val_3617_);
lean_dec(v_fst_3613_);
lean_dec(v_fst_3611_);
lean_dec_ref(v___x_3355_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3626_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3618_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3618_);
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
lean_dec(v_a_3616_);
lean_dec(v_snd_3614_);
lean_dec(v_fst_3613_);
lean_dec(v_fst_3611_);
v___y_3529_ = v_isEq_3601_;
v_isHEq_3530_ = v___x_3214_;
v___y_3531_ = v___y_3602_;
v___y_3532_ = v___y_3603_;
v___y_3533_ = v___y_3604_;
v___y_3534_ = v___y_3605_;
goto v___jp_3528_;
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_snd_3614_);
lean_dec(v_fst_3613_);
lean_dec(v_fst_3611_);
lean_dec_ref(v___x_3355_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3634_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3615_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3615_);
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
else
{
lean_dec(v_a_3607_);
v___y_3529_ = v_isEq_3601_;
v_isHEq_3530_ = v___x_3310_;
v___y_3531_ = v___y_3602_;
v___y_3532_ = v___y_3603_;
v___y_3533_ = v___y_3604_;
v___y_3534_ = v___y_3605_;
goto v___jp_3528_;
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v___x_3355_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3642_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3606_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3606_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
v___jp_3650_:
{
lean_object* v___x_3655_; 
lean_inc_ref(v___x_3355_);
v___x_3655_ = l_Lean_Meta_matchEq_x3f(v___x_3355_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
if (lean_obj_tag(v_a_3656_) == 1)
{
lean_object* v_val_3657_; lean_object* v_snd_3658_; lean_object* v_fst_3659_; lean_object* v_snd_3660_; lean_object* v___x_3661_; 
v_val_3657_ = lean_ctor_get(v_a_3656_, 0);
lean_inc(v_val_3657_);
lean_dec_ref_known(v_a_3656_, 1);
v_snd_3658_ = lean_ctor_get(v_val_3657_, 1);
lean_inc(v_snd_3658_);
lean_dec(v_val_3657_);
v_fst_3659_ = lean_ctor_get(v_snd_3658_, 0);
lean_inc(v_fst_3659_);
v_snd_3660_ = lean_ctor_get(v_snd_3658_, 1);
lean_inc(v_snd_3660_);
lean_dec(v_snd_3658_);
v___x_3661_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3659_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
if (lean_obj_tag(v_a_3662_) == 1)
{
lean_object* v_val_3663_; lean_object* v___x_3664_; 
v_val_3663_ = lean_ctor_get(v_a_3662_, 0);
lean_inc(v_val_3663_);
lean_dec_ref_known(v_a_3662_, 1);
v___x_3664_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3660_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3664_, 1);
if (lean_obj_tag(v_a_3665_) == 1)
{
lean_object* v_toConstantVal_3666_; lean_object* v_val_3667_; lean_object* v_toConstantVal_3668_; lean_object* v_name_3669_; lean_object* v_name_3670_; uint8_t v___x_3671_; 
v_toConstantVal_3666_ = lean_ctor_get(v_val_3663_, 0);
lean_inc_ref(v_toConstantVal_3666_);
lean_dec(v_val_3663_);
v_val_3667_ = lean_ctor_get(v_a_3665_, 0);
lean_inc(v_val_3667_);
lean_dec_ref_known(v_a_3665_, 1);
v_toConstantVal_3668_ = lean_ctor_get(v_val_3667_, 0);
lean_inc_ref(v_toConstantVal_3668_);
lean_dec(v_val_3667_);
v_name_3669_ = lean_ctor_get(v_toConstantVal_3666_, 0);
lean_inc(v_name_3669_);
lean_dec_ref(v_toConstantVal_3666_);
v_name_3670_ = lean_ctor_get(v_toConstantVal_3668_, 0);
lean_inc(v_name_3670_);
lean_dec_ref(v_toConstantVal_3668_);
v___x_3671_ = lean_name_eq(v_name_3669_, v_name_3670_);
lean_dec(v_name_3670_);
lean_dec(v_name_3669_);
if (v___x_3671_ == 0)
{
lean_dec_ref(v___x_3355_);
lean_dec_ref(v_config_3203_);
v___y_3241_ = v___y_3653_;
v___y_3242_ = v___y_3651_;
v___y_3243_ = v___y_3654_;
v___y_3244_ = v___y_3652_;
goto v___jp_3240_;
}
else
{
if (v___x_3310_ == 0)
{
lean_del_object(v___x_3237_);
v_isEq_3601_ = v___x_3214_;
v___y_3602_ = v___y_3651_;
v___y_3603_ = v___y_3652_;
v___y_3604_ = v___y_3653_;
v___y_3605_ = v___y_3654_;
goto v___jp_3600_;
}
else
{
lean_dec_ref(v___x_3355_);
lean_dec_ref(v_config_3203_);
v___y_3241_ = v___y_3653_;
v___y_3242_ = v___y_3651_;
v___y_3243_ = v___y_3654_;
v___y_3244_ = v___y_3652_;
goto v___jp_3240_;
}
}
}
else
{
lean_dec(v_a_3665_);
lean_dec(v_val_3663_);
lean_del_object(v___x_3237_);
v_isEq_3601_ = v___x_3214_;
v___y_3602_ = v___y_3651_;
v___y_3603_ = v___y_3652_;
v___y_3604_ = v___y_3653_;
v___y_3605_ = v___y_3654_;
goto v___jp_3600_;
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v_val_3663_);
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3672_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3664_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3664_);
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
lean_dec(v_a_3662_);
lean_dec(v_snd_3660_);
lean_del_object(v___x_3237_);
v_isEq_3601_ = v___x_3214_;
v___y_3602_ = v___y_3651_;
v___y_3603_ = v___y_3652_;
v___y_3604_ = v___y_3653_;
v___y_3605_ = v___y_3654_;
goto v___jp_3600_;
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec(v_snd_3660_);
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3680_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3661_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3661_);
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
else
{
lean_dec(v_a_3656_);
lean_del_object(v___x_3237_);
v_isEq_3601_ = v___x_3310_;
v___y_3602_ = v___y_3651_;
v___y_3603_ = v___y_3652_;
v___y_3604_ = v___y_3653_;
v___y_3605_ = v___y_3654_;
goto v___jp_3600_;
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3688_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3655_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3655_);
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
v___jp_3696_:
{
lean_object* v___x_3701_; 
lean_inc_ref(v___x_3355_);
v___x_3701_ = l_refutableHasNotBit_x3f(v___x_3355_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref_known(v___x_3701_, 1);
if (lean_obj_tag(v_a_3702_) == 1)
{
lean_object* v_val_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3743_; 
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec_ref(v_config_3203_);
v_val_3703_ = lean_ctor_get(v_a_3702_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_a_3702_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3705_ = v_a_3702_;
v_isShared_3706_ = v_isSharedCheck_3743_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_val_3703_);
lean_dec(v_a_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3743_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; 
lean_inc(v_mvarId_3204_);
v___x_3707_ = l_Lean_MVarId_getType(v_mvarId_3204_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v___x_3709_ = l_Lean_LocalDecl_toExpr(v_val_3235_);
v___x_3710_ = l_Lean_Meta_mkAbsurd(v_a_3708_, v_val_3703_, v___x_3709_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3712_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v___x_3712_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3204_, v_a_3711_, v___y_3698_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
lean_dec_ref_known(v___x_3712_, 1);
v___x_3713_ = lean_box(v___x_3214_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3713_);
v___x_3715_ = v___x_3705_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
lean_ctor_set(v___x_3716_, 1, v___x_3239_);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
v_a_3221_ = v___x_3717_;
goto v___jp_3220_;
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_del_object(v___x_3705_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
v_a_3719_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3712_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3712_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_del_object(v___x_3705_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3727_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3710_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3710_);
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
lean_del_object(v___x_3705_);
lean_dec(v_val_3703_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3735_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3707_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3707_);
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
}
else
{
lean_object* v___x_3744_; 
lean_dec(v_a_3702_);
lean_inc_ref(v___x_3355_);
v___x_3744_ = l_Lean_Meta_matchNe_x3f(v___x_3355_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___x_3744_, 1);
if (lean_obj_tag(v_a_3745_) == 1)
{
lean_object* v_val_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3816_; 
v_val_3746_ = lean_ctor_get(v_a_3745_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_a_3745_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3748_ = v_a_3745_;
v_isShared_3749_ = v_isSharedCheck_3816_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_val_3746_);
lean_dec(v_a_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3816_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v_snd_3750_; lean_object* v_fst_3751_; lean_object* v_snd_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3815_; 
v_snd_3750_ = lean_ctor_get(v_val_3746_, 1);
lean_inc(v_snd_3750_);
lean_dec(v_val_3746_);
v_fst_3751_ = lean_ctor_get(v_snd_3750_, 0);
v_snd_3752_ = lean_ctor_get(v_snd_3750_, 1);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_snd_3750_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3754_ = v_snd_3750_;
v_isShared_3755_ = v_isSharedCheck_3815_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_snd_3752_);
lean_inc(v_fst_3751_);
lean_dec(v_snd_3750_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3815_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; 
lean_inc(v_fst_3751_);
v___x_3756_ = l_Lean_Meta_isExprDefEq(v_fst_3751_, v_snd_3752_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; uint8_t v___x_3758_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3756_, 1);
v___x_3758_ = lean_unbox(v_a_3757_);
lean_dec(v_a_3757_);
if (v___x_3758_ == 0)
{
lean_del_object(v___x_3754_);
lean_dec(v_fst_3751_);
lean_del_object(v___x_3748_);
v___y_3651_ = v___y_3697_;
v___y_3652_ = v___y_3698_;
v___y_3653_ = v___y_3699_;
v___y_3654_ = v___y_3700_;
goto v___jp_3650_;
}
else
{
lean_object* v___x_3759_; 
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec_ref(v_config_3203_);
lean_inc(v_mvarId_3204_);
v___x_3759_ = l_Lean_MVarId_getType(v_mvarId_3204_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3761_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = l_Lean_Meta_mkEqRefl(v_fst_3751_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3761_, 1);
v___x_3763_ = l_Lean_LocalDecl_toExpr(v_val_3235_);
v___x_3764_ = l_Lean_Meta_mkAbsurd(v_a_3760_, v_a_3762_, v___x_3763_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3766_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
v___x_3766_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3204_, v_a_3765_, v___y_3698_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
lean_dec_ref_known(v___x_3766_, 1);
v___x_3767_ = lean_box(v___x_3214_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3767_);
v___x_3769_ = v___x_3748_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3771_; 
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 1, v___x_3239_);
lean_ctor_set(v___x_3754_, 0, v___x_3769_);
v___x_3771_ = v___x_3754_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v___x_3239_);
v___x_3771_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
v_a_3221_ = v___x_3772_;
goto v___jp_3220_;
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_del_object(v___x_3754_);
lean_del_object(v___x_3748_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
v_a_3775_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3766_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3766_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_del_object(v___x_3754_);
lean_del_object(v___x_3748_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3783_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3764_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3764_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec(v_a_3760_);
lean_del_object(v___x_3754_);
lean_del_object(v___x_3748_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3791_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3761_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3761_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_del_object(v___x_3754_);
lean_dec(v_fst_3751_);
lean_del_object(v___x_3748_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3799_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3759_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3759_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_del_object(v___x_3754_);
lean_dec(v_fst_3751_);
lean_del_object(v___x_3748_);
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3807_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3756_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3756_);
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
}
}
else
{
lean_dec(v_a_3745_);
v___y_3651_ = v___y_3697_;
v___y_3652_ = v___y_3698_;
v___y_3653_ = v___y_3699_;
v___y_3654_ = v___y_3700_;
goto v___jp_3650_;
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3817_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3744_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3744_);
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
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3825_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3701_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3701_);
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
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
v_a_3229_ = v___x_3281_;
goto v___jp_3228_;
}
v___jp_3240_:
{
lean_object* v___x_3245_; 
lean_inc(v_mvarId_3204_);
v___x_3245_ = l_Lean_MVarId_getType(v_mvarId_3204_, v___y_3242_, v___y_3244_, v___y_3241_, v___y_3243_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
v___x_3247_ = l_Lean_LocalDecl_toExpr(v_val_3235_);
v___x_3248_ = l_Lean_Meta_mkNoConfusion(v_a_3246_, v___x_3247_, v___y_3242_, v___y_3244_, v___y_3241_, v___y_3243_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3250_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3204_, v_a_3249_, v___y_3244_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
lean_dec_ref_known(v___x_3250_, 1);
v___x_3251_ = lean_box(v___x_3214_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3251_);
v___x_3253_ = v___x_3237_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
lean_ctor_set(v___x_3254_, 1, v___x_3239_);
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
v_a_3221_ = v___x_3255_;
goto v___jp_3220_;
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_del_object(v___x_3237_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
v_a_3257_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3250_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3250_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_del_object(v___x_3237_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3265_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3248_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3248_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_del_object(v___x_3237_);
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
v_a_3273_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3245_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3245_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
v___jp_3282_:
{
lean_object* v_searchFuel_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_searchFuel_3287_ = lean_ctor_get(v_config_3203_, 0);
v___x_3288_ = l_Lean_LocalDecl_fvarId(v_val_3235_);
lean_dec(v_val_3235_);
lean_inc(v_searchFuel_3287_);
lean_inc(v_mvarId_3204_);
v___x_3289_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3204_, v___x_3288_, v_searchFuel_3287_, v___y_3285_, v___y_3283_, v___y_3286_, v___y_3284_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; uint8_t v___x_3291_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref_known(v___x_3289_, 1);
v___x_3291_ = lean_unbox(v_a_3290_);
lean_dec(v_a_3290_);
if (v___x_3291_ == 0)
{
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
v_a_3229_ = v___x_3281_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v___x_3292_ = lean_box(v___x_3214_);
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v___x_3239_);
v___x_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
v_a_3221_ = v___x_3295_;
goto v___jp_3220_;
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3296_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3289_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3289_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
v___jp_3304_:
{
if (v___y_3309_ == 0)
{
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
v_a_3229_ = v___x_3281_;
goto v___jp_3228_;
}
else
{
v___y_3283_ = v___y_3305_;
v___y_3284_ = v___y_3306_;
v___y_3285_ = v___y_3307_;
v___y_3286_ = v___y_3308_;
goto v___jp_3282_;
}
}
v___jp_3311_:
{
if (v___y_3315_ == 0)
{
v___y_3283_ = v___y_3312_;
v___y_3284_ = v___y_3313_;
v___y_3285_ = v___y_3314_;
v___y_3286_ = v___y_3316_;
goto v___jp_3282_;
}
else
{
v___y_3305_ = v___y_3312_;
v___y_3306_ = v___y_3313_;
v___y_3307_ = v___y_3314_;
v___y_3308_ = v___y_3316_;
v___y_3309_ = v___x_3310_;
goto v___jp_3304_;
}
}
v___jp_3317_:
{
if (v___y_3323_ == 0)
{
v___y_3305_ = v___y_3318_;
v___y_3306_ = v___y_3319_;
v___y_3307_ = v___y_3320_;
v___y_3308_ = v___y_3322_;
v___y_3309_ = v___x_3310_;
goto v___jp_3304_;
}
else
{
v___y_3312_ = v___y_3318_;
v___y_3313_ = v___y_3319_;
v___y_3314_ = v___y_3320_;
v___y_3315_ = v___y_3321_;
v___y_3316_ = v___y_3322_;
goto v___jp_3311_;
}
}
v___jp_3324_:
{
uint8_t v_emptyType_3331_; 
v_emptyType_3331_ = lean_ctor_get_uint8(v_config_3203_, sizeof(void*)*1 + 1);
if (v_emptyType_3331_ == 0)
{
v___y_3318_ = v___y_3328_;
v___y_3319_ = v___y_3330_;
v___y_3320_ = v___y_3327_;
v___y_3321_ = v___y_3326_;
v___y_3322_ = v___y_3329_;
v___y_3323_ = v___x_3310_;
goto v___jp_3317_;
}
else
{
if (v___y_3325_ == 0)
{
v___y_3312_ = v___y_3328_;
v___y_3313_ = v___y_3330_;
v___y_3314_ = v___y_3327_;
v___y_3315_ = v___y_3326_;
v___y_3316_ = v___y_3329_;
goto v___jp_3311_;
}
else
{
v___y_3318_ = v___y_3328_;
v___y_3319_ = v___y_3330_;
v___y_3320_ = v___y_3327_;
v___y_3321_ = v___y_3326_;
v___y_3322_ = v___y_3329_;
v___y_3323_ = v___x_3310_;
goto v___jp_3317_;
}
}
}
v___jp_3332_:
{
if (v___y_3339_ == 0)
{
v___y_3325_ = v___y_3335_;
v___y_3326_ = v___y_3337_;
v___y_3327_ = v___y_3338_;
v___y_3328_ = v___y_3334_;
v___y_3329_ = v___y_3336_;
v___y_3330_ = v___y_3333_;
goto v___jp_3324_;
}
else
{
lean_object* v___x_3340_; 
lean_inc(v_val_3235_);
lean_inc(v_mvarId_3204_);
v___x_3340_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3204_, v_val_3235_, v___y_3338_, v___y_3334_, v___y_3336_, v___y_3333_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; uint8_t v___x_3342_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v___x_3342_ = lean_unbox(v_a_3341_);
lean_dec(v_a_3341_);
if (v___x_3342_ == 0)
{
v___y_3325_ = v___y_3335_;
v___y_3326_ = v___y_3337_;
v___y_3327_ = v___y_3338_;
v___y_3328_ = v___y_3334_;
v___y_3329_ = v___y_3336_;
v___y_3330_ = v___y_3333_;
goto v___jp_3324_;
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_dec(v_val_3235_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v___x_3343_ = lean_box(v___x_3214_);
v___x_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
lean_ctor_set(v___x_3345_, 1, v___x_3239_);
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
v_a_3221_ = v___x_3346_;
goto v___jp_3220_;
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec(v_val_3235_);
lean_del_object(v___x_3218_);
lean_dec(v_snd_3216_);
lean_dec(v_mvarId_3204_);
lean_dec_ref(v_config_3203_);
v_a_3347_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3340_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3340_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
}
}
v___jp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_a_3221_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v___x_3222_);
v___x_3224_ = v___x_3218_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_snd_3216_);
v___x_3224_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; 
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
return v___x_3225_;
}
}
v___jp_3228_:
{
lean_object* v___x_3230_; size_t v___x_3231_; size_t v___x_3232_; 
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3227_);
lean_ctor_set(v___x_3230_, 1, v_a_3229_);
v___x_3231_ = ((size_t)1ULL);
v___x_3232_ = lean_usize_add(v_i_3207_, v___x_3231_);
v_i_3207_ = v___x_3232_;
v_b_3208_ = v___x_3230_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3906_, lean_object* v_mvarId_3907_, lean_object* v_as_3908_, lean_object* v_sz_3909_, lean_object* v_i_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
size_t v_sz_boxed_3917_; size_t v_i_boxed_3918_; lean_object* v_res_3919_; 
v_sz_boxed_3917_ = lean_unbox_usize(v_sz_3909_);
lean_dec(v_sz_3909_);
v_i_boxed_3918_ = lean_unbox_usize(v_i_3910_);
lean_dec(v_i_3910_);
v_res_3919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3906_, v_mvarId_3907_, v_as_3908_, v_sz_boxed_3917_, v_i_boxed_3918_, v_b_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec_ref(v_as_3908_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3920_, lean_object* v_mvarId_3921_, lean_object* v_as_3922_, size_t v_sz_3923_, size_t v_i_3924_, lean_object* v_b_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
uint8_t v___x_3931_; 
v___x_3931_ = lean_usize_dec_lt(v_i_3924_, v_sz_3923_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; 
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v___x_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3932_, 0, v_b_3925_);
return v___x_3932_;
}
else
{
lean_object* v_snd_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_4621_; 
v_snd_3933_ = lean_ctor_get(v_b_3925_, 1);
v_isSharedCheck_4621_ = !lean_is_exclusive(v_b_3925_);
if (v_isSharedCheck_4621_ == 0)
{
lean_object* v_unused_4622_; 
v_unused_4622_ = lean_ctor_get(v_b_3925_, 0);
lean_dec(v_unused_4622_);
v___x_3935_ = v_b_3925_;
v_isShared_3936_ = v_isSharedCheck_4621_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_snd_3933_);
lean_dec(v_b_3925_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_4621_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v_a_3938_; lean_object* v___x_3944_; lean_object* v_a_3946_; lean_object* v_a_3951_; 
v___x_3944_ = lean_box(0);
v_a_3951_ = lean_array_uget(v_as_3922_, v_i_3924_);
if (lean_obj_tag(v_a_3951_) == 0)
{
lean_del_object(v___x_3935_);
v_a_3946_ = v_snd_3933_;
goto v___jp_3945_;
}
else
{
lean_object* v_val_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_4620_; 
v_val_3952_ = lean_ctor_get(v_a_3951_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v_a_3951_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_3954_ = v_a_3951_;
v_isShared_3955_ = v_isSharedCheck_4620_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_val_3952_);
lean_dec(v_a_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_4620_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___x_3998_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; uint8_t v___y_4026_; uint8_t v___x_4027_; uint8_t v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; uint8_t v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; uint8_t v___y_4040_; uint8_t v___y_4042_; uint8_t v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; uint8_t v___y_4050_; lean_object* v___y_4051_; uint8_t v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; uint8_t v___y_4056_; 
v___x_3956_ = lean_box(0);
v___x_3998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_4027_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3952_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4072_; uint8_t v___y_4074_; uint8_t v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; uint8_t v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; uint8_t v___y_4088_; lean_object* v___y_4089_; uint8_t v___y_4090_; uint8_t v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; uint8_t v___y_4097_; lean_object* v___y_4098_; lean_object* v_a_4099_; uint8_t v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; uint8_t v___y_4107_; lean_object* v___y_4108_; uint8_t v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; uint8_t v___y_4205_; lean_object* v___y_4206_; uint8_t v___y_4207_; uint8_t v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; uint8_t v___y_4214_; lean_object* v___y_4215_; uint8_t v___y_4216_; uint8_t v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; uint8_t v___y_4223_; lean_object* v___y_4224_; uint8_t v___y_4225_; uint8_t v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; uint8_t v___y_4242_; lean_object* v___y_4243_; uint8_t v___y_4244_; uint8_t v___y_4246_; uint8_t v_isHEq_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; uint8_t v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; uint8_t v_isEq_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___x_4550_; 
v___x_4072_ = l_Lean_LocalDecl_type(v_val_3952_);
lean_inc_ref(v___x_4072_);
v___x_4550_ = l_Lean_Meta_matchNot_x3f(v___x_4072_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_a_4551_);
lean_dec_ref_known(v___x_4550_, 1);
if (lean_obj_tag(v_a_4551_) == 1)
{
lean_object* v_val_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4611_; 
v_val_4552_ = lean_ctor_get(v_a_4551_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v_a_4551_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4554_ = v_a_4551_;
v_isShared_4555_ = v_isSharedCheck_4611_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_val_4552_);
lean_dec(v_a_4551_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4611_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4556_; 
v___x_4556_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4552_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
lean_dec_ref_known(v___x_4556_, 1);
if (lean_obj_tag(v_a_4557_) == 1)
{
lean_object* v_val_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4602_; 
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec_ref(v_config_3920_);
v_val_4558_ = lean_ctor_get(v_a_4557_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v_a_4557_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4560_ = v_a_4557_;
v_isShared_4561_ = v_isSharedCheck_4602_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_val_4558_);
lean_dec(v_a_4557_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4602_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4562_; 
lean_inc(v_mvarId_3921_);
v___x_4562_ = l_Lean_MVarId_getType(v_mvarId_3921_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
lean_dec_ref_known(v___x_4562_, 1);
v___x_4564_ = l_Lean_LocalDecl_toExpr(v_val_3952_);
v___x_4565_ = l_Lean_mkFVar(v_val_4558_);
v___x_4566_ = l_Lean_Expr_app___override(v___x_4564_, v___x_4565_);
v___x_4567_ = l_Lean_Meta_mkFalseElim(v_a_4563_, v___x_4566_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; lean_object* v___x_4569_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_a_4568_);
lean_dec_ref_known(v___x_4567_, 1);
v___x_4569_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3921_, v_a_4568_, v___y_3927_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v___x_4570_; lean_object* v___x_4572_; 
lean_dec_ref_known(v___x_4569_, 1);
v___x_4570_ = lean_box(v___x_3931_);
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v___x_4570_);
v___x_4572_ = v___x_4560_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4570_);
v___x_4572_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
lean_object* v___x_4573_; lean_object* v___x_4575_; 
v___x_4573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
lean_ctor_set(v___x_4573_, 1, v___x_3956_);
if (v_isShared_4555_ == 0)
{
lean_ctor_set_tag(v___x_4554_, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4573_);
v___x_4575_ = v___x_4554_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4573_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
v_a_3938_ = v___x_4575_;
goto v___jp_3937_;
}
}
}
else
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4585_; 
lean_del_object(v___x_4560_);
lean_del_object(v___x_4554_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
v_a_4578_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4580_ = v___x_4569_;
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4569_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4578_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
lean_del_object(v___x_4560_);
lean_del_object(v___x_4554_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4586_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4567_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4567_);
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
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4601_; 
lean_del_object(v___x_4560_);
lean_dec(v_val_4558_);
lean_del_object(v___x_4554_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4594_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4596_ = v___x_4562_;
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4562_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4594_);
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
}
else
{
lean_dec(v_a_4557_);
lean_del_object(v___x_4554_);
v___y_4414_ = v___y_3926_;
v___y_4415_ = v___y_3927_;
v___y_4416_ = v___y_3928_;
v___y_4417_ = v___y_3929_;
goto v___jp_4413_;
}
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
lean_del_object(v___x_4554_);
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4603_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4556_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4556_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
}
else
{
lean_dec(v_a_4551_);
v___y_4414_ = v___y_3926_;
v___y_4415_ = v___y_3927_;
v___y_4416_ = v___y_3928_;
v___y_4417_ = v___y_3929_;
goto v___jp_4413_;
}
}
else
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4612_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v___x_4550_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4550_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
v___jp_4073_:
{
uint8_t v_genDiseq_4080_; 
v_genDiseq_4080_ = lean_ctor_get_uint8(v_config_3920_, sizeof(void*)*1 + 2);
if (v_genDiseq_4080_ == 0)
{
lean_dec_ref(v___x_4072_);
v___y_4050_ = v___y_4074_;
v___y_4051_ = v___y_4076_;
v___y_4052_ = v___y_4075_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v___y_4078_;
v___y_4055_ = v___y_4077_;
v___y_4056_ = v___x_4027_;
goto v___jp_4049_;
}
else
{
uint8_t v___x_4081_; 
v___x_4081_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4072_);
v___y_4050_ = v___y_4074_;
v___y_4051_ = v___y_4076_;
v___y_4052_ = v___y_4075_;
v___y_4053_ = v___y_4079_;
v___y_4054_ = v___y_4078_;
v___y_4055_ = v___y_4077_;
v___y_4056_ = v___x_4081_;
goto v___jp_4049_;
}
}
v___jp_4082_:
{
if (v___y_4090_ == 0)
{
lean_dec_ref(v___y_4086_);
v___y_4074_ = v___y_4083_;
v___y_4075_ = v___y_4088_;
v___y_4076_ = v___y_4085_;
v___y_4077_ = v___y_4084_;
v___y_4078_ = v___y_4087_;
v___y_4079_ = v___y_4089_;
goto v___jp_4073_;
}
else
{
lean_object* v___x_4091_; 
lean_dec_ref(v___x_4072_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v___x_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4091_, 0, v___y_4086_);
return v___x_4091_;
}
}
v___jp_4092_:
{
uint8_t v___x_4100_; 
v___x_4100_ = l_Lean_Exception_isInterrupt(v_a_4099_);
if (v___x_4100_ == 0)
{
uint8_t v___x_4101_; 
lean_inc_ref(v_a_4099_);
v___x_4101_ = l_Lean_Exception_isRuntime(v_a_4099_);
v___y_4083_ = v___y_4093_;
v___y_4084_ = v___y_4095_;
v___y_4085_ = v___y_4094_;
v___y_4086_ = v_a_4099_;
v___y_4087_ = v___y_4096_;
v___y_4088_ = v___y_4097_;
v___y_4089_ = v___y_4098_;
v___y_4090_ = v___x_4101_;
goto v___jp_4082_;
}
else
{
v___y_4083_ = v___y_4093_;
v___y_4084_ = v___y_4095_;
v___y_4085_ = v___y_4094_;
v___y_4086_ = v_a_4099_;
v___y_4087_ = v___y_4096_;
v___y_4088_ = v___y_4097_;
v___y_4089_ = v___y_4098_;
v___y_4090_ = v___x_4100_;
goto v___jp_4082_;
}
}
v___jp_4102_:
{
lean_object* v___x_4109_; 
lean_inc_ref(v___x_4072_);
v___x_4109_ = l_Lean_Meta_mkDecide(v___x_4072_, v___y_4105_, v___y_4104_, v___y_4106_, v___y_4108_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4111_; uint8_t v_foApprox_4112_; uint8_t v_ctxApprox_4113_; uint8_t v_quasiPatternApprox_4114_; uint8_t v_constApprox_4115_; uint8_t v_isDefEqStuckEx_4116_; uint8_t v_unificationHints_4117_; uint8_t v_proofIrrelevance_4118_; uint8_t v_assignSyntheticOpaque_4119_; uint8_t v_offsetCnstrs_4120_; uint8_t v_etaStruct_4121_; uint8_t v_univApprox_4122_; uint8_t v_iota_4123_; uint8_t v_beta_4124_; uint8_t v_proj_4125_; uint8_t v_zeta_4126_; uint8_t v_zetaDelta_4127_; uint8_t v_zetaUnused_4128_; uint8_t v_zetaHave_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4198_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
v___x_4111_ = l_Lean_Meta_Context_config(v___y_4105_);
v_foApprox_4112_ = lean_ctor_get_uint8(v___x_4111_, 0);
v_ctxApprox_4113_ = lean_ctor_get_uint8(v___x_4111_, 1);
v_quasiPatternApprox_4114_ = lean_ctor_get_uint8(v___x_4111_, 2);
v_constApprox_4115_ = lean_ctor_get_uint8(v___x_4111_, 3);
v_isDefEqStuckEx_4116_ = lean_ctor_get_uint8(v___x_4111_, 4);
v_unificationHints_4117_ = lean_ctor_get_uint8(v___x_4111_, 5);
v_proofIrrelevance_4118_ = lean_ctor_get_uint8(v___x_4111_, 6);
v_assignSyntheticOpaque_4119_ = lean_ctor_get_uint8(v___x_4111_, 7);
v_offsetCnstrs_4120_ = lean_ctor_get_uint8(v___x_4111_, 8);
v_etaStruct_4121_ = lean_ctor_get_uint8(v___x_4111_, 10);
v_univApprox_4122_ = lean_ctor_get_uint8(v___x_4111_, 11);
v_iota_4123_ = lean_ctor_get_uint8(v___x_4111_, 12);
v_beta_4124_ = lean_ctor_get_uint8(v___x_4111_, 13);
v_proj_4125_ = lean_ctor_get_uint8(v___x_4111_, 14);
v_zeta_4126_ = lean_ctor_get_uint8(v___x_4111_, 15);
v_zetaDelta_4127_ = lean_ctor_get_uint8(v___x_4111_, 16);
v_zetaUnused_4128_ = lean_ctor_get_uint8(v___x_4111_, 17);
v_zetaHave_4129_ = lean_ctor_get_uint8(v___x_4111_, 18);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4131_ = v___x_4111_;
v_isShared_4132_ = v_isSharedCheck_4198_;
goto v_resetjp_4130_;
}
else
{
lean_dec(v___x_4111_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4198_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
uint8_t v_trackZetaDelta_4133_; lean_object* v_zetaDeltaSet_4134_; lean_object* v_lctx_4135_; lean_object* v_localInstances_4136_; lean_object* v_defEqCtx_x3f_4137_; lean_object* v_synthPendingDepth_4138_; lean_object* v_canUnfold_x3f_4139_; uint8_t v_univApprox_4140_; uint8_t v_inTypeClassResolution_4141_; uint8_t v_cacheInferType_4142_; uint8_t v___x_4143_; lean_object* v_config_4145_; 
v_trackZetaDelta_4133_ = lean_ctor_get_uint8(v___y_4105_, sizeof(void*)*7);
v_zetaDeltaSet_4134_ = lean_ctor_get(v___y_4105_, 1);
v_lctx_4135_ = lean_ctor_get(v___y_4105_, 2);
v_localInstances_4136_ = lean_ctor_get(v___y_4105_, 3);
v_defEqCtx_x3f_4137_ = lean_ctor_get(v___y_4105_, 4);
v_synthPendingDepth_4138_ = lean_ctor_get(v___y_4105_, 5);
v_canUnfold_x3f_4139_ = lean_ctor_get(v___y_4105_, 6);
v_univApprox_4140_ = lean_ctor_get_uint8(v___y_4105_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4141_ = lean_ctor_get_uint8(v___y_4105_, sizeof(void*)*7 + 2);
v_cacheInferType_4142_ = lean_ctor_get_uint8(v___y_4105_, sizeof(void*)*7 + 3);
v___x_4143_ = 1;
if (v_isShared_4132_ == 0)
{
v_config_4145_ = v___x_4131_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 0, v_foApprox_4112_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 1, v_ctxApprox_4113_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 2, v_quasiPatternApprox_4114_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 3, v_constApprox_4115_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 4, v_isDefEqStuckEx_4116_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 5, v_unificationHints_4117_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 6, v_proofIrrelevance_4118_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 7, v_assignSyntheticOpaque_4119_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 8, v_offsetCnstrs_4120_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 10, v_etaStruct_4121_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 11, v_univApprox_4122_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 12, v_iota_4123_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 13, v_beta_4124_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 14, v_proj_4125_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 15, v_zeta_4126_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 16, v_zetaDelta_4127_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 17, v_zetaUnused_4128_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 18, v_zetaHave_4129_);
v_config_4145_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
uint64_t v___x_4146_; uint64_t v___x_4147_; uint64_t v___x_4148_; uint64_t v___x_4149_; uint64_t v___x_4150_; uint64_t v_key_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_ctor_set_uint8(v_config_4145_, 9, v___x_4143_);
v___x_4146_ = l_Lean_Meta_Context_configKey(v___y_4105_);
v___x_4147_ = 3ULL;
v___x_4148_ = lean_uint64_shift_right(v___x_4146_, v___x_4147_);
v___x_4149_ = lean_uint64_shift_left(v___x_4148_, v___x_4147_);
v___x_4150_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_4151_ = lean_uint64_lor(v___x_4149_, v___x_4150_);
v___x_4152_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4152_, 0, v_config_4145_);
lean_ctor_set_uint64(v___x_4152_, sizeof(void*)*1, v_key_4151_);
lean_inc(v_canUnfold_x3f_4139_);
lean_inc(v_synthPendingDepth_4138_);
lean_inc(v_defEqCtx_x3f_4137_);
lean_inc_ref(v_localInstances_4136_);
lean_inc_ref(v_lctx_4135_);
lean_inc(v_zetaDeltaSet_4134_);
v___x_4153_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
lean_ctor_set(v___x_4153_, 1, v_zetaDeltaSet_4134_);
lean_ctor_set(v___x_4153_, 2, v_lctx_4135_);
lean_ctor_set(v___x_4153_, 3, v_localInstances_4136_);
lean_ctor_set(v___x_4153_, 4, v_defEqCtx_x3f_4137_);
lean_ctor_set(v___x_4153_, 5, v_synthPendingDepth_4138_);
lean_ctor_set(v___x_4153_, 6, v_canUnfold_x3f_4139_);
lean_ctor_set_uint8(v___x_4153_, sizeof(void*)*7, v_trackZetaDelta_4133_);
lean_ctor_set_uint8(v___x_4153_, sizeof(void*)*7 + 1, v_univApprox_4140_);
lean_ctor_set_uint8(v___x_4153_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4141_);
lean_ctor_set_uint8(v___x_4153_, sizeof(void*)*7 + 3, v_cacheInferType_4142_);
lean_inc(v___y_4108_);
lean_inc_ref(v___y_4106_);
lean_inc(v___y_4104_);
lean_inc(v_a_4110_);
v___x_4154_ = lean_whnf(v_a_4110_, v___x_4153_, v___y_4104_, v___y_4106_, v___y_4108_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v___x_4156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_4157_ = l_Lean_Expr_isConstOf(v_a_4155_, v___x_4156_);
lean_dec(v_a_4155_);
if (v___x_4157_ == 0)
{
lean_dec(v_a_4110_);
v___y_4074_ = v___y_4103_;
v___y_4075_ = v___y_4107_;
v___y_4076_ = v___y_4105_;
v___y_4077_ = v___y_4104_;
v___y_4078_ = v___y_4106_;
v___y_4079_ = v___y_4108_;
goto v___jp_4073_;
}
else
{
lean_object* v___x_4158_; 
lean_inc(v_a_4110_);
v___x_4158_ = l_Lean_Meta_mkEqRefl(v_a_4110_, v___y_4105_, v___y_4104_, v___y_4106_, v___y_4108_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4160_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4158_, 1);
lean_inc(v_mvarId_3921_);
v___x_4160_ = l_Lean_MVarId_getType(v_mvarId_3921_, v___y_4105_, v___y_4104_, v___y_4106_, v___y_4108_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v_nargs_4162_; lean_object* v___x_4163_; lean_object* v_dummy_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v_nargs_4162_ = l_Lean_Expr_getAppNumArgs(v_a_4110_);
v___x_4163_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_4164_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_4162_);
v___x_4165_ = lean_mk_array(v_nargs_4162_, v_dummy_4164_);
v___x_4166_ = lean_unsigned_to_nat(1u);
v___x_4167_ = lean_nat_sub(v_nargs_4162_, v___x_4166_);
lean_dec(v_nargs_4162_);
v___x_4168_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4110_, v___x_4165_, v___x_4167_);
v___x_4169_ = lean_array_push(v___x_4168_, v_a_4159_);
v___x_4170_ = l_Lean_mkAppN(v___x_4163_, v___x_4169_);
lean_dec_ref(v___x_4169_);
lean_inc(v_val_3952_);
v___x_4171_ = l_Lean_LocalDecl_toExpr(v_val_3952_);
v___x_4172_ = l_Lean_Meta_mkAbsurd(v_a_4161_, v___x_4171_, v___x_4170_, v___y_4105_, v___y_4104_, v___y_4106_, v___y_4108_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4192_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4192_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4192_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4177_; 
lean_inc(v_mvarId_3921_);
v___x_4177_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3921_, v_a_4173_, v___y_4104_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4189_; 
lean_dec_ref(v___x_4072_);
lean_dec(v_val_3952_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4189_ == 0)
{
lean_object* v_unused_4190_; 
v_unused_4190_ = lean_ctor_get(v___x_4177_, 0);
lean_dec(v_unused_4190_);
v___x_4179_ = v___x_4177_;
v_isShared_4180_ = v_isSharedCheck_4189_;
goto v_resetjp_4178_;
}
else
{
lean_dec(v___x_4177_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4189_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4181_ = lean_box(v___x_3931_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set_tag(v___x_4179_, 1);
lean_ctor_set(v___x_4179_, 0, v___x_4181_);
v___x_4183_ = v___x_4179_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; lean_object* v___x_4186_; 
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
lean_ctor_set(v___x_4184_, 1, v___x_3956_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4184_);
v___x_4186_ = v___x_4175_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
v_a_3938_ = v___x_4186_;
goto v___jp_3937_;
}
}
}
}
else
{
lean_object* v_a_4191_; 
lean_del_object(v___x_4175_);
v_a_4191_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4191_);
lean_dec_ref_known(v___x_4177_, 1);
v___y_4093_ = v___y_4103_;
v___y_4094_ = v___y_4105_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___y_4106_;
v___y_4097_ = v___y_4107_;
v___y_4098_ = v___y_4108_;
v_a_4099_ = v_a_4191_;
goto v___jp_4092_;
}
}
}
else
{
lean_object* v_a_4193_; 
v_a_4193_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4172_, 1);
v___y_4093_ = v___y_4103_;
v___y_4094_ = v___y_4105_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___y_4106_;
v___y_4097_ = v___y_4107_;
v___y_4098_ = v___y_4108_;
v_a_4099_ = v_a_4193_;
goto v___jp_4092_;
}
}
else
{
lean_object* v_a_4194_; 
lean_dec(v_a_4159_);
lean_dec(v_a_4110_);
v_a_4194_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4194_);
lean_dec_ref_known(v___x_4160_, 1);
v___y_4093_ = v___y_4103_;
v___y_4094_ = v___y_4105_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___y_4106_;
v___y_4097_ = v___y_4107_;
v___y_4098_ = v___y_4108_;
v_a_4099_ = v_a_4194_;
goto v___jp_4092_;
}
}
else
{
lean_object* v_a_4195_; 
lean_dec(v_a_4110_);
v_a_4195_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4158_, 1);
v___y_4093_ = v___y_4103_;
v___y_4094_ = v___y_4105_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___y_4106_;
v___y_4097_ = v___y_4107_;
v___y_4098_ = v___y_4108_;
v_a_4099_ = v_a_4195_;
goto v___jp_4092_;
}
}
}
else
{
lean_object* v_a_4196_; 
lean_dec(v_a_4110_);
v_a_4196_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4154_, 1);
v___y_4093_ = v___y_4103_;
v___y_4094_ = v___y_4105_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___y_4106_;
v___y_4097_ = v___y_4107_;
v___y_4098_ = v___y_4108_;
v_a_4099_ = v_a_4196_;
goto v___jp_4092_;
}
}
}
}
else
{
lean_object* v_a_4199_; 
v_a_4199_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4109_, 1);
v___y_4093_ = v___y_4103_;
v___y_4094_ = v___y_4105_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___y_4106_;
v___y_4097_ = v___y_4107_;
v___y_4098_ = v___y_4108_;
v_a_4099_ = v_a_4199_;
goto v___jp_4092_;
}
}
v___jp_4200_:
{
if (v___y_4207_ == 0)
{
v___y_4074_ = v___y_4201_;
v___y_4075_ = v___y_4205_;
v___y_4076_ = v___y_4203_;
v___y_4077_ = v___y_4202_;
v___y_4078_ = v___y_4204_;
v___y_4079_ = v___y_4206_;
goto v___jp_4073_;
}
else
{
v___y_4103_ = v___y_4201_;
v___y_4104_ = v___y_4202_;
v___y_4105_ = v___y_4203_;
v___y_4106_ = v___y_4204_;
v___y_4107_ = v___y_4205_;
v___y_4108_ = v___y_4206_;
goto v___jp_4102_;
}
}
v___jp_4208_:
{
if (v___y_4216_ == 0)
{
lean_dec_ref(v___y_4210_);
v___y_4201_ = v___y_4209_;
v___y_4202_ = v___y_4212_;
v___y_4203_ = v___y_4211_;
v___y_4204_ = v___y_4213_;
v___y_4205_ = v___y_4214_;
v___y_4206_ = v___y_4215_;
v___y_4207_ = v___x_4027_;
goto v___jp_4200_;
}
else
{
uint8_t v___x_4217_; 
v___x_4217_ = l_Lean_Expr_hasFVar(v___y_4210_);
lean_dec_ref(v___y_4210_);
if (v___x_4217_ == 0)
{
v___y_4103_ = v___y_4209_;
v___y_4104_ = v___y_4212_;
v___y_4105_ = v___y_4211_;
v___y_4106_ = v___y_4213_;
v___y_4107_ = v___y_4214_;
v___y_4108_ = v___y_4215_;
goto v___jp_4102_;
}
else
{
v___y_4201_ = v___y_4209_;
v___y_4202_ = v___y_4212_;
v___y_4203_ = v___y_4211_;
v___y_4204_ = v___y_4213_;
v___y_4205_ = v___y_4214_;
v___y_4206_ = v___y_4215_;
v___y_4207_ = v___x_4027_;
goto v___jp_4200_;
}
}
}
v___jp_4218_:
{
lean_object* v___x_4226_; 
lean_inc_ref(v___x_4072_);
v___x_4226_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4072_, v___y_4221_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; uint8_t v___x_4228_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref_known(v___x_4226_, 1);
v___x_4228_ = l_Lean_Expr_hasMVar(v_a_4227_);
if (v___x_4228_ == 0)
{
v___y_4209_ = v___y_4219_;
v___y_4210_ = v_a_4227_;
v___y_4211_ = v___y_4220_;
v___y_4212_ = v___y_4221_;
v___y_4213_ = v___y_4222_;
v___y_4214_ = v___y_4223_;
v___y_4215_ = v___y_4224_;
v___y_4216_ = v___y_4225_;
goto v___jp_4208_;
}
else
{
v___y_4209_ = v___y_4219_;
v___y_4210_ = v_a_4227_;
v___y_4211_ = v___y_4220_;
v___y_4212_ = v___y_4221_;
v___y_4213_ = v___y_4222_;
v___y_4214_ = v___y_4223_;
v___y_4215_ = v___y_4224_;
v___y_4216_ = v___x_4027_;
goto v___jp_4208_;
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec_ref(v___x_4072_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4229_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4226_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4226_);
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
v___jp_4237_:
{
if (v___y_4244_ == 0)
{
v___y_4074_ = v___y_4238_;
v___y_4075_ = v___y_4242_;
v___y_4076_ = v___y_4240_;
v___y_4077_ = v___y_4239_;
v___y_4078_ = v___y_4241_;
v___y_4079_ = v___y_4243_;
goto v___jp_4073_;
}
else
{
v___y_4219_ = v___y_4238_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4239_;
v___y_4222_ = v___y_4241_;
v___y_4223_ = v___y_4242_;
v___y_4224_ = v___y_4243_;
v___y_4225_ = v___y_4244_;
goto v___jp_4218_;
}
}
v___jp_4245_:
{
uint8_t v_useDecide_4252_; 
v_useDecide_4252_ = lean_ctor_get_uint8(v_config_3920_, sizeof(void*)*1);
if (v_useDecide_4252_ == 0)
{
v___y_4238_ = v_isHEq_4247_;
v___y_4239_ = v___y_4249_;
v___y_4240_ = v___y_4248_;
v___y_4241_ = v___y_4250_;
v___y_4242_ = v___y_4246_;
v___y_4243_ = v___y_4251_;
v___y_4244_ = v___x_4027_;
goto v___jp_4237_;
}
else
{
uint8_t v___x_4253_; 
v___x_4253_ = l_Lean_Expr_hasFVar(v___x_4072_);
if (v___x_4253_ == 0)
{
v___y_4219_ = v_isHEq_4247_;
v___y_4220_ = v___y_4248_;
v___y_4221_ = v___y_4249_;
v___y_4222_ = v___y_4250_;
v___y_4223_ = v___y_4246_;
v___y_4224_ = v___y_4251_;
v___y_4225_ = v_useDecide_4252_;
goto v___jp_4218_;
}
else
{
v___y_4238_ = v_isHEq_4247_;
v___y_4239_ = v___y_4249_;
v___y_4240_ = v___y_4248_;
v___y_4241_ = v___y_4250_;
v___y_4242_ = v___y_4246_;
v___y_4243_ = v___y_4251_;
v___y_4244_ = v___x_4027_;
goto v___jp_4237_;
}
}
}
v___jp_4254_:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Lean_Meta_isExprDefEq(v___y_4255_, v___y_4260_, v___y_4258_, v___y_4257_, v___y_4261_, v___y_4256_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; uint8_t v___x_4264_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
v___x_4264_ = lean_unbox(v_a_4263_);
lean_dec(v_a_4263_);
if (v___x_4264_ == 0)
{
v___y_4246_ = v___y_4259_;
v_isHEq_4247_ = v___x_3931_;
v___y_4248_ = v___y_4258_;
v___y_4249_ = v___y_4257_;
v___y_4250_ = v___y_4261_;
v___y_4251_ = v___y_4256_;
goto v___jp_4245_;
}
else
{
lean_object* v___x_4265_; 
lean_dec_ref(v___x_4072_);
lean_dec_ref(v_config_3920_);
lean_inc(v_mvarId_3921_);
v___x_4265_ = l_Lean_MVarId_getType(v_mvarId_3921_, v___y_4258_, v___y_4257_, v___y_4261_, v___y_4256_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v___x_4265_, 1);
v___x_4267_ = l_Lean_LocalDecl_toExpr(v_val_3952_);
v___x_4268_ = l_Lean_Meta_mkEqOfHEq(v___x_4267_, v___x_3931_, v___y_4258_, v___y_4257_, v___y_4261_, v___y_4256_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; lean_object* v___x_4270_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4268_, 1);
v___x_4270_ = l_Lean_Meta_mkNoConfusion(v_a_4266_, v_a_4269_, v___y_4258_, v___y_4257_, v___y_4261_, v___y_4256_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4272_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc(v_a_4271_);
lean_dec_ref_known(v___x_4270_, 1);
v___x_4272_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3921_, v_a_4271_, v___y_4257_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
lean_dec_ref_known(v___x_4272_, 1);
v___x_4273_ = lean_box(v___x_3931_);
v___x_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4273_);
v___x_4275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
lean_ctor_set(v___x_4275_, 1, v___x_3956_);
v___x_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
v_a_3938_ = v___x_4276_;
goto v___jp_3937_;
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
v_a_4277_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4272_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4272_);
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
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4285_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4270_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4270_);
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
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v_a_4266_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4293_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4268_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4268_);
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
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4301_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4265_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4265_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec_ref(v___x_4072_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4309_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4262_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4262_);
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
v___jp_4317_:
{
lean_object* v___x_4323_; 
lean_inc_ref(v___x_4072_);
v___x_4323_ = l_Lean_Meta_matchHEq_x3f(v___x_4072_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4323_, 1);
if (lean_obj_tag(v_a_4324_) == 1)
{
lean_object* v_val_4325_; lean_object* v_snd_4326_; lean_object* v_snd_4327_; lean_object* v_fst_4328_; lean_object* v_fst_4329_; lean_object* v_fst_4330_; lean_object* v_snd_4331_; lean_object* v___x_4332_; 
v_val_4325_ = lean_ctor_get(v_a_4324_, 0);
lean_inc(v_val_4325_);
lean_dec_ref_known(v_a_4324_, 1);
v_snd_4326_ = lean_ctor_get(v_val_4325_, 1);
lean_inc(v_snd_4326_);
v_snd_4327_ = lean_ctor_get(v_snd_4326_, 1);
lean_inc(v_snd_4327_);
v_fst_4328_ = lean_ctor_get(v_val_4325_, 0);
lean_inc(v_fst_4328_);
lean_dec(v_val_4325_);
v_fst_4329_ = lean_ctor_get(v_snd_4326_, 0);
lean_inc(v_fst_4329_);
lean_dec(v_snd_4326_);
v_fst_4330_ = lean_ctor_get(v_snd_4327_, 0);
lean_inc(v_fst_4330_);
v_snd_4331_ = lean_ctor_get(v_snd_4327_, 1);
lean_inc(v_snd_4331_);
lean_dec(v_snd_4327_);
v___x_4332_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4329_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v___x_4332_, 1);
if (lean_obj_tag(v_a_4333_) == 1)
{
lean_object* v_val_4334_; lean_object* v___x_4335_; 
v_val_4334_ = lean_ctor_get(v_a_4333_, 0);
lean_inc(v_val_4334_);
lean_dec_ref_known(v_a_4333_, 1);
v___x_4335_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4331_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
if (lean_obj_tag(v_a_4336_) == 1)
{
lean_object* v_toConstantVal_4337_; lean_object* v_val_4338_; lean_object* v_toConstantVal_4339_; lean_object* v_name_4340_; lean_object* v_name_4341_; uint8_t v___x_4342_; 
v_toConstantVal_4337_ = lean_ctor_get(v_val_4334_, 0);
lean_inc_ref(v_toConstantVal_4337_);
lean_dec(v_val_4334_);
v_val_4338_ = lean_ctor_get(v_a_4336_, 0);
lean_inc(v_val_4338_);
lean_dec_ref_known(v_a_4336_, 1);
v_toConstantVal_4339_ = lean_ctor_get(v_val_4338_, 0);
lean_inc_ref(v_toConstantVal_4339_);
lean_dec(v_val_4338_);
v_name_4340_ = lean_ctor_get(v_toConstantVal_4337_, 0);
lean_inc(v_name_4340_);
lean_dec_ref(v_toConstantVal_4337_);
v_name_4341_ = lean_ctor_get(v_toConstantVal_4339_, 0);
lean_inc(v_name_4341_);
lean_dec_ref(v_toConstantVal_4339_);
v___x_4342_ = lean_name_eq(v_name_4340_, v_name_4341_);
lean_dec(v_name_4341_);
lean_dec(v_name_4340_);
if (v___x_4342_ == 0)
{
v___y_4255_ = v_fst_4328_;
v___y_4256_ = v___y_4322_;
v___y_4257_ = v___y_4320_;
v___y_4258_ = v___y_4319_;
v___y_4259_ = v_isEq_4318_;
v___y_4260_ = v_fst_4330_;
v___y_4261_ = v___y_4321_;
goto v___jp_4254_;
}
else
{
if (v___x_4027_ == 0)
{
lean_dec(v_fst_4330_);
lean_dec(v_fst_4328_);
v___y_4246_ = v_isEq_4318_;
v_isHEq_4247_ = v___x_3931_;
v___y_4248_ = v___y_4319_;
v___y_4249_ = v___y_4320_;
v___y_4250_ = v___y_4321_;
v___y_4251_ = v___y_4322_;
goto v___jp_4245_;
}
else
{
v___y_4255_ = v_fst_4328_;
v___y_4256_ = v___y_4322_;
v___y_4257_ = v___y_4320_;
v___y_4258_ = v___y_4319_;
v___y_4259_ = v_isEq_4318_;
v___y_4260_ = v_fst_4330_;
v___y_4261_ = v___y_4321_;
goto v___jp_4254_;
}
}
}
else
{
lean_dec(v_a_4336_);
lean_dec(v_val_4334_);
lean_dec(v_fst_4330_);
lean_dec(v_fst_4328_);
v___y_4246_ = v_isEq_4318_;
v_isHEq_4247_ = v___x_3931_;
v___y_4248_ = v___y_4319_;
v___y_4249_ = v___y_4320_;
v___y_4250_ = v___y_4321_;
v___y_4251_ = v___y_4322_;
goto v___jp_4245_;
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec(v_val_4334_);
lean_dec(v_fst_4330_);
lean_dec(v_fst_4328_);
lean_dec_ref(v___x_4072_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4343_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4335_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4335_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
else
{
lean_dec(v_a_4333_);
lean_dec(v_snd_4331_);
lean_dec(v_fst_4330_);
lean_dec(v_fst_4328_);
v___y_4246_ = v_isEq_4318_;
v_isHEq_4247_ = v___x_3931_;
v___y_4248_ = v___y_4319_;
v___y_4249_ = v___y_4320_;
v___y_4250_ = v___y_4321_;
v___y_4251_ = v___y_4322_;
goto v___jp_4245_;
}
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec(v_snd_4331_);
lean_dec(v_fst_4330_);
lean_dec(v_fst_4328_);
lean_dec_ref(v___x_4072_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4351_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4332_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4332_);
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
else
{
lean_dec(v_a_4324_);
v___y_4246_ = v_isEq_4318_;
v_isHEq_4247_ = v___x_4027_;
v___y_4248_ = v___y_4319_;
v___y_4249_ = v___y_4320_;
v___y_4250_ = v___y_4321_;
v___y_4251_ = v___y_4322_;
goto v___jp_4245_;
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec_ref(v___x_4072_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4359_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4323_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4323_);
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
v___jp_4367_:
{
lean_object* v___x_4372_; 
lean_inc_ref(v___x_4072_);
v___x_4372_ = l_Lean_Meta_matchEq_x3f(v___x_4072_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_a_4373_);
lean_dec_ref_known(v___x_4372_, 1);
if (lean_obj_tag(v_a_4373_) == 1)
{
lean_object* v_val_4374_; lean_object* v_snd_4375_; lean_object* v_fst_4376_; lean_object* v_snd_4377_; lean_object* v___x_4378_; 
v_val_4374_ = lean_ctor_get(v_a_4373_, 0);
lean_inc(v_val_4374_);
lean_dec_ref_known(v_a_4373_, 1);
v_snd_4375_ = lean_ctor_get(v_val_4374_, 1);
lean_inc(v_snd_4375_);
lean_dec(v_val_4374_);
v_fst_4376_ = lean_ctor_get(v_snd_4375_, 0);
lean_inc(v_fst_4376_);
v_snd_4377_ = lean_ctor_get(v_snd_4375_, 1);
lean_inc(v_snd_4377_);
lean_dec(v_snd_4375_);
v___x_4378_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4376_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v___x_4378_, 1);
if (lean_obj_tag(v_a_4379_) == 1)
{
lean_object* v_val_4380_; lean_object* v___x_4381_; 
v_val_4380_ = lean_ctor_get(v_a_4379_, 0);
lean_inc(v_val_4380_);
lean_dec_ref_known(v_a_4379_, 1);
v___x_4381_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4377_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4381_, 1);
if (lean_obj_tag(v_a_4382_) == 1)
{
lean_object* v_toConstantVal_4383_; lean_object* v_val_4384_; lean_object* v_toConstantVal_4385_; lean_object* v_name_4386_; lean_object* v_name_4387_; uint8_t v___x_4388_; 
v_toConstantVal_4383_ = lean_ctor_get(v_val_4380_, 0);
lean_inc_ref(v_toConstantVal_4383_);
lean_dec(v_val_4380_);
v_val_4384_ = lean_ctor_get(v_a_4382_, 0);
lean_inc(v_val_4384_);
lean_dec_ref_known(v_a_4382_, 1);
v_toConstantVal_4385_ = lean_ctor_get(v_val_4384_, 0);
lean_inc_ref(v_toConstantVal_4385_);
lean_dec(v_val_4384_);
v_name_4386_ = lean_ctor_get(v_toConstantVal_4383_, 0);
lean_inc(v_name_4386_);
lean_dec_ref(v_toConstantVal_4383_);
v_name_4387_ = lean_ctor_get(v_toConstantVal_4385_, 0);
lean_inc(v_name_4387_);
lean_dec_ref(v_toConstantVal_4385_);
v___x_4388_ = lean_name_eq(v_name_4386_, v_name_4387_);
lean_dec(v_name_4387_);
lean_dec(v_name_4386_);
if (v___x_4388_ == 0)
{
lean_dec_ref(v___x_4072_);
lean_dec_ref(v_config_3920_);
v___y_3958_ = v___y_4368_;
v___y_3959_ = v___y_4371_;
v___y_3960_ = v___y_4369_;
v___y_3961_ = v___y_4370_;
goto v___jp_3957_;
}
else
{
if (v___x_4027_ == 0)
{
lean_del_object(v___x_3954_);
v_isEq_4318_ = v___x_3931_;
v___y_4319_ = v___y_4368_;
v___y_4320_ = v___y_4369_;
v___y_4321_ = v___y_4370_;
v___y_4322_ = v___y_4371_;
goto v___jp_4317_;
}
else
{
lean_dec_ref(v___x_4072_);
lean_dec_ref(v_config_3920_);
v___y_3958_ = v___y_4368_;
v___y_3959_ = v___y_4371_;
v___y_3960_ = v___y_4369_;
v___y_3961_ = v___y_4370_;
goto v___jp_3957_;
}
}
}
else
{
lean_dec(v_a_4382_);
lean_dec(v_val_4380_);
lean_del_object(v___x_3954_);
v_isEq_4318_ = v___x_3931_;
v___y_4319_ = v___y_4368_;
v___y_4320_ = v___y_4369_;
v___y_4321_ = v___y_4370_;
v___y_4322_ = v___y_4371_;
goto v___jp_4317_;
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec(v_val_4380_);
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4389_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4381_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4381_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
else
{
lean_dec(v_a_4379_);
lean_dec(v_snd_4377_);
lean_del_object(v___x_3954_);
v_isEq_4318_ = v___x_3931_;
v___y_4319_ = v___y_4368_;
v___y_4320_ = v___y_4369_;
v___y_4321_ = v___y_4370_;
v___y_4322_ = v___y_4371_;
goto v___jp_4317_;
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
lean_dec(v_snd_4377_);
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4397_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4378_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4378_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
else
{
lean_dec(v_a_4373_);
lean_del_object(v___x_3954_);
v_isEq_4318_ = v___x_4027_;
v___y_4319_ = v___y_4368_;
v___y_4320_ = v___y_4369_;
v___y_4321_ = v___y_4370_;
v___y_4322_ = v___y_4371_;
goto v___jp_4317_;
}
}
else
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4412_; 
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4405_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4407_ = v___x_4372_;
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4372_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_a_4405_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
}
v___jp_4413_:
{
lean_object* v___x_4418_; 
lean_inc_ref(v___x_4072_);
v___x_4418_ = l_refutableHasNotBit_x3f(v___x_4072_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4419_);
lean_dec_ref_known(v___x_4418_, 1);
if (lean_obj_tag(v_a_4419_) == 1)
{
lean_object* v_val_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4460_; 
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec_ref(v_config_3920_);
v_val_4420_ = lean_ctor_get(v_a_4419_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v_a_4419_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4422_ = v_a_4419_;
v_isShared_4423_ = v_isSharedCheck_4460_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_val_4420_);
lean_dec(v_a_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4460_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; 
lean_inc(v_mvarId_3921_);
v___x_4424_ = l_Lean_MVarId_getType(v_mvarId_3921_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4424_, 1);
v___x_4426_ = l_Lean_LocalDecl_toExpr(v_val_3952_);
v___x_4427_ = l_Lean_Meta_mkAbsurd(v_a_4425_, v_val_4420_, v___x_4426_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4429_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref_known(v___x_4427_, 1);
v___x_4429_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3921_, v_a_4428_, v___y_4415_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v___x_4430_; lean_object* v___x_4432_; 
lean_dec_ref_known(v___x_4429_, 1);
v___x_4430_ = lean_box(v___x_3931_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v___x_4430_);
v___x_4432_ = v___x_4422_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4430_);
v___x_4432_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
lean_ctor_set(v___x_4433_, 1, v___x_3956_);
v___x_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
v_a_3938_ = v___x_4434_;
goto v___jp_3937_;
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_del_object(v___x_4422_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
v_a_4436_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4429_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4429_);
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
lean_del_object(v___x_4422_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4444_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4427_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4427_);
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
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_del_object(v___x_4422_);
lean_dec(v_val_4420_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4452_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4424_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4424_);
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
else
{
lean_object* v___x_4461_; 
lean_dec(v_a_4419_);
lean_inc_ref(v___x_4072_);
v___x_4461_ = l_Lean_Meta_matchNe_x3f(v___x_4072_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4462_);
lean_dec_ref_known(v___x_4461_, 1);
if (lean_obj_tag(v_a_4462_) == 1)
{
lean_object* v_val_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4533_; 
v_val_4463_ = lean_ctor_get(v_a_4462_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_a_4462_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4465_ = v_a_4462_;
v_isShared_4466_ = v_isSharedCheck_4533_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_val_4463_);
lean_dec(v_a_4462_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4533_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v_snd_4467_; lean_object* v_fst_4468_; lean_object* v_snd_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4532_; 
v_snd_4467_ = lean_ctor_get(v_val_4463_, 1);
lean_inc(v_snd_4467_);
lean_dec(v_val_4463_);
v_fst_4468_ = lean_ctor_get(v_snd_4467_, 0);
v_snd_4469_ = lean_ctor_get(v_snd_4467_, 1);
v_isSharedCheck_4532_ = !lean_is_exclusive(v_snd_4467_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4471_ = v_snd_4467_;
v_isShared_4472_ = v_isSharedCheck_4532_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_snd_4469_);
lean_inc(v_fst_4468_);
lean_dec(v_snd_4467_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4532_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4473_; 
lean_inc(v_fst_4468_);
v___x_4473_ = l_Lean_Meta_isExprDefEq(v_fst_4468_, v_snd_4469_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; uint8_t v___x_4475_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4475_ = lean_unbox(v_a_4474_);
lean_dec(v_a_4474_);
if (v___x_4475_ == 0)
{
lean_del_object(v___x_4471_);
lean_dec(v_fst_4468_);
lean_del_object(v___x_4465_);
v___y_4368_ = v___y_4414_;
v___y_4369_ = v___y_4415_;
v___y_4370_ = v___y_4416_;
v___y_4371_ = v___y_4417_;
goto v___jp_4367_;
}
else
{
lean_object* v___x_4476_; 
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec_ref(v_config_3920_);
lean_inc(v_mvarId_3921_);
v___x_4476_ = l_Lean_MVarId_getType(v_mvarId_3921_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4478_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4476_, 1);
v___x_4478_ = l_Lean_Meta_mkEqRefl(v_fst_4468_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref_known(v___x_4478_, 1);
v___x_4480_ = l_Lean_LocalDecl_toExpr(v_val_3952_);
v___x_4481_ = l_Lean_Meta_mkAbsurd(v_a_4477_, v_a_4479_, v___x_4480_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4483_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
v___x_4483_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3921_, v_a_4482_, v___y_4415_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
lean_dec_ref_known(v___x_4483_, 1);
v___x_4484_ = lean_box(v___x_3931_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 0, v___x_4484_);
v___x_4486_ = v___x_4465_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4488_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 1, v___x_3956_);
lean_ctor_set(v___x_4471_, 0, v___x_4486_);
v___x_4488_ = v___x_4471_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4486_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v___x_3956_);
v___x_4488_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
lean_object* v___x_4489_; 
v___x_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
v_a_3938_ = v___x_4489_;
goto v___jp_3937_;
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_del_object(v___x_4471_);
lean_del_object(v___x_4465_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
v_a_4492_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4483_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4483_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_del_object(v___x_4471_);
lean_del_object(v___x_4465_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4500_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4481_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4481_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_dec(v_a_4477_);
lean_del_object(v___x_4471_);
lean_del_object(v___x_4465_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4508_ = lean_ctor_get(v___x_4478_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4478_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4478_);
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
lean_del_object(v___x_4471_);
lean_dec(v_fst_4468_);
lean_del_object(v___x_4465_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_4516_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4476_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4476_);
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
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
lean_del_object(v___x_4471_);
lean_dec(v_fst_4468_);
lean_del_object(v___x_4465_);
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4524_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4473_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4473_);
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
}
else
{
lean_dec(v_a_4462_);
v___y_4368_ = v___y_4414_;
v___y_4369_ = v___y_4415_;
v___y_4370_ = v___y_4416_;
v___y_4371_ = v___y_4417_;
goto v___jp_4367_;
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4534_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4461_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4461_);
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
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
lean_dec_ref(v___x_4072_);
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4542_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4418_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4418_);
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
}
}
else
{
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
v_a_3946_ = v___x_3998_;
goto v___jp_3945_;
}
v___jp_3957_:
{
lean_object* v___x_3962_; 
lean_inc(v_mvarId_3921_);
v___x_3962_ = l_Lean_MVarId_getType(v_mvarId_3921_, v___y_3958_, v___y_3960_, v___y_3961_, v___y_3959_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v___x_3964_ = l_Lean_LocalDecl_toExpr(v_val_3952_);
v___x_3965_ = l_Lean_Meta_mkNoConfusion(v_a_3963_, v___x_3964_, v___y_3958_, v___y_3960_, v___y_3961_, v___y_3959_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v___x_3967_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3921_, v_a_3966_, v___y_3960_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3970_; 
lean_dec_ref_known(v___x_3967_, 1);
v___x_3968_ = lean_box(v___x_3931_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v___x_3968_);
v___x_3970_ = v___x_3954_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3968_);
v___x_3970_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
lean_ctor_set(v___x_3971_, 1, v___x_3956_);
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
v_a_3938_ = v___x_3972_;
goto v___jp_3937_;
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_del_object(v___x_3954_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
v_a_3974_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3967_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3967_);
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
lean_del_object(v___x_3954_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_3982_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3965_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3965_);
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
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
v_a_3990_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3962_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3962_);
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
v___jp_3999_:
{
lean_object* v_searchFuel_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v_searchFuel_4004_ = lean_ctor_get(v_config_3920_, 0);
v___x_4005_ = l_Lean_LocalDecl_fvarId(v_val_3952_);
lean_dec(v_val_3952_);
lean_inc(v_searchFuel_4004_);
lean_inc(v_mvarId_3921_);
v___x_4006_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3921_, v___x_4005_, v_searchFuel_4004_, v___y_4002_, v___y_4001_, v___y_4000_, v___y_4003_);
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
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
v_a_3946_ = v___x_3998_;
goto v___jp_3945_;
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v___x_4009_ = lean_box(v___x_3931_);
v___x_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
v___x_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
lean_ctor_set(v___x_4011_, 1, v___x_3956_);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
v_a_3938_ = v___x_4012_;
goto v___jp_3937_;
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
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
v___jp_4021_:
{
if (v___y_4026_ == 0)
{
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
v_a_3946_ = v___x_3998_;
goto v___jp_3945_;
}
else
{
v___y_4000_ = v___y_4022_;
v___y_4001_ = v___y_4023_;
v___y_4002_ = v___y_4024_;
v___y_4003_ = v___y_4025_;
goto v___jp_3999_;
}
}
v___jp_4028_:
{
if (v___y_4029_ == 0)
{
v___y_4000_ = v___y_4030_;
v___y_4001_ = v___y_4031_;
v___y_4002_ = v___y_4032_;
v___y_4003_ = v___y_4033_;
goto v___jp_3999_;
}
else
{
v___y_4022_ = v___y_4030_;
v___y_4023_ = v___y_4031_;
v___y_4024_ = v___y_4032_;
v___y_4025_ = v___y_4033_;
v___y_4026_ = v___x_4027_;
goto v___jp_4021_;
}
}
v___jp_4034_:
{
if (v___y_4040_ == 0)
{
v___y_4022_ = v___y_4036_;
v___y_4023_ = v___y_4037_;
v___y_4024_ = v___y_4038_;
v___y_4025_ = v___y_4039_;
v___y_4026_ = v___x_4027_;
goto v___jp_4021_;
}
else
{
v___y_4029_ = v___y_4035_;
v___y_4030_ = v___y_4036_;
v___y_4031_ = v___y_4037_;
v___y_4032_ = v___y_4038_;
v___y_4033_ = v___y_4039_;
goto v___jp_4028_;
}
}
v___jp_4041_:
{
uint8_t v_emptyType_4048_; 
v_emptyType_4048_ = lean_ctor_get_uint8(v_config_3920_, sizeof(void*)*1 + 1);
if (v_emptyType_4048_ == 0)
{
v___y_4035_ = v___y_4042_;
v___y_4036_ = v___y_4046_;
v___y_4037_ = v___y_4045_;
v___y_4038_ = v___y_4044_;
v___y_4039_ = v___y_4047_;
v___y_4040_ = v___x_4027_;
goto v___jp_4034_;
}
else
{
if (v___y_4043_ == 0)
{
v___y_4029_ = v___y_4042_;
v___y_4030_ = v___y_4046_;
v___y_4031_ = v___y_4045_;
v___y_4032_ = v___y_4044_;
v___y_4033_ = v___y_4047_;
goto v___jp_4028_;
}
else
{
v___y_4035_ = v___y_4042_;
v___y_4036_ = v___y_4046_;
v___y_4037_ = v___y_4045_;
v___y_4038_ = v___y_4044_;
v___y_4039_ = v___y_4047_;
v___y_4040_ = v___x_4027_;
goto v___jp_4034_;
}
}
}
v___jp_4049_:
{
if (v___y_4056_ == 0)
{
v___y_4042_ = v___y_4050_;
v___y_4043_ = v___y_4052_;
v___y_4044_ = v___y_4051_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4054_;
v___y_4047_ = v___y_4053_;
goto v___jp_4041_;
}
else
{
lean_object* v___x_4057_; 
lean_inc(v_val_3952_);
lean_inc(v_mvarId_3921_);
v___x_4057_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3921_, v_val_3952_, v___y_4051_, v___y_4055_, v___y_4054_, v___y_4053_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; uint8_t v___x_4059_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref_known(v___x_4057_, 1);
v___x_4059_ = lean_unbox(v_a_4058_);
lean_dec(v_a_4058_);
if (v___x_4059_ == 0)
{
v___y_4042_ = v___y_4050_;
v___y_4043_ = v___y_4052_;
v___y_4044_ = v___y_4051_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4054_;
v___y_4047_ = v___y_4053_;
goto v___jp_4041_;
}
else
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
lean_dec(v_val_3952_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v___x_4060_ = lean_box(v___x_3931_);
v___x_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
v___x_4062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
lean_ctor_set(v___x_4062_, 1, v___x_3956_);
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
v_a_3938_ = v___x_4063_;
goto v___jp_3937_;
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v_val_3952_);
lean_del_object(v___x_3935_);
lean_dec(v_snd_3933_);
lean_dec(v_mvarId_3921_);
lean_dec_ref(v_config_3920_);
v_a_4064_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4057_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4057_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
}
}
v___jp_3937_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3939_, 0, v_a_3938_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 0, v___x_3939_);
v___x_3941_ = v___x_3935_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_snd_3933_);
v___x_3941_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; 
v___x_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
return v___x_3942_;
}
}
v___jp_3945_:
{
lean_object* v___x_3947_; size_t v___x_3948_; size_t v___x_3949_; lean_object* v___x_3950_; 
v___x_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3944_);
lean_ctor_set(v___x_3947_, 1, v_a_3946_);
v___x_3948_ = ((size_t)1ULL);
v___x_3949_ = lean_usize_add(v_i_3924_, v___x_3948_);
v___x_3950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3920_, v_mvarId_3921_, v_as_3922_, v_sz_3923_, v___x_3949_, v___x_3947_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
return v___x_3950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4623_, lean_object* v_mvarId_4624_, lean_object* v_as_4625_, lean_object* v_sz_4626_, lean_object* v_i_4627_, lean_object* v_b_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
size_t v_sz_boxed_4634_; size_t v_i_boxed_4635_; lean_object* v_res_4636_; 
v_sz_boxed_4634_ = lean_unbox_usize(v_sz_4626_);
lean_dec(v_sz_4626_);
v_i_boxed_4635_ = lean_unbox_usize(v_i_4627_);
lean_dec(v_i_4627_);
v_res_4636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4623_, v_mvarId_4624_, v_as_4625_, v_sz_boxed_4634_, v_i_boxed_4635_, v_b_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
lean_dec_ref(v_as_4625_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4637_, lean_object* v_config_4638_, lean_object* v_mvarId_4639_, lean_object* v_n_4640_, lean_object* v_b_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
if (lean_obj_tag(v_n_4640_) == 0)
{
lean_object* v_cs_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; size_t v_sz_4650_; size_t v___x_4651_; lean_object* v___x_4652_; 
v_cs_4647_ = lean_ctor_get(v_n_4640_, 0);
v___x_4648_ = lean_box(0);
v___x_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
lean_ctor_set(v___x_4649_, 1, v_b_4641_);
v_sz_4650_ = lean_array_size(v_cs_4647_);
v___x_4651_ = ((size_t)0ULL);
v___x_4652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4637_, v_config_4638_, v_mvarId_4639_, v_cs_4647_, v_sz_4650_, v___x_4651_, v___x_4649_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4667_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4655_ = v___x_4652_;
v_isShared_4656_ = v_isSharedCheck_4667_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4652_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4667_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v_fst_4657_; 
v_fst_4657_ = lean_ctor_get(v_a_4653_, 0);
if (lean_obj_tag(v_fst_4657_) == 0)
{
lean_object* v_snd_4658_; lean_object* v___x_4659_; lean_object* v___x_4661_; 
v_snd_4658_ = lean_ctor_get(v_a_4653_, 1);
lean_inc(v_snd_4658_);
lean_dec(v_a_4653_);
v___x_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4659_, 0, v_snd_4658_);
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
else
{
lean_object* v_val_4663_; lean_object* v___x_4665_; 
lean_inc_ref(v_fst_4657_);
lean_dec(v_a_4653_);
v_val_4663_ = lean_ctor_get(v_fst_4657_, 0);
lean_inc(v_val_4663_);
lean_dec_ref_known(v_fst_4657_, 1);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v_val_4663_);
v___x_4665_ = v___x_4655_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_val_4663_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
v_a_4668_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4652_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4652_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
else
{
lean_object* v_vs_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; size_t v_sz_4679_; size_t v___x_4680_; lean_object* v___x_4681_; 
v_vs_4676_ = lean_ctor_get(v_n_4640_, 0);
v___x_4677_ = lean_box(0);
v___x_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
lean_ctor_set(v___x_4678_, 1, v_b_4641_);
v_sz_4679_ = lean_array_size(v_vs_4676_);
v___x_4680_ = ((size_t)0ULL);
v___x_4681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4638_, v_mvarId_4639_, v_vs_4676_, v_sz_4679_, v___x_4680_, v___x_4678_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4696_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4684_ = v___x_4681_;
v_isShared_4685_ = v_isSharedCheck_4696_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4696_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v_fst_4686_; 
v_fst_4686_ = lean_ctor_get(v_a_4682_, 0);
if (lean_obj_tag(v_fst_4686_) == 0)
{
lean_object* v_snd_4687_; lean_object* v___x_4688_; lean_object* v___x_4690_; 
v_snd_4687_ = lean_ctor_get(v_a_4682_, 1);
lean_inc(v_snd_4687_);
lean_dec(v_a_4682_);
v___x_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4688_, 0, v_snd_4687_);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v___x_4688_);
v___x_4690_ = v___x_4684_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4688_);
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
lean_inc_ref(v_fst_4686_);
lean_dec(v_a_4682_);
v_val_4692_ = lean_ctor_get(v_fst_4686_, 0);
lean_inc(v_val_4692_);
lean_dec_ref_known(v_fst_4686_, 1);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v_val_4692_);
v___x_4694_ = v___x_4684_;
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
v_a_4697_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4681_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4681_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4705_, lean_object* v_config_4706_, lean_object* v_mvarId_4707_, lean_object* v_as_4708_, size_t v_sz_4709_, size_t v_i_4710_, lean_object* v_b_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
uint8_t v___x_4717_; 
v___x_4717_ = lean_usize_dec_lt(v_i_4710_, v_sz_4709_);
if (v___x_4717_ == 0)
{
lean_object* v___x_4718_; 
lean_dec(v_mvarId_4707_);
lean_dec_ref(v_config_4706_);
v___x_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4718_, 0, v_b_4711_);
return v___x_4718_;
}
else
{
lean_object* v_snd_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4753_; 
v_snd_4719_ = lean_ctor_get(v_b_4711_, 1);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_b_4711_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; 
v_unused_4754_ = lean_ctor_get(v_b_4711_, 0);
lean_dec(v_unused_4754_);
v___x_4721_ = v_b_4711_;
v_isShared_4722_ = v_isSharedCheck_4753_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_snd_4719_);
lean_dec(v_b_4711_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4753_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v_a_4723_; lean_object* v___x_4724_; 
v_a_4723_ = lean_array_uget_borrowed(v_as_4708_, v_i_4710_);
lean_inc(v_snd_4719_);
lean_inc(v_mvarId_4707_);
lean_inc_ref(v_config_4706_);
v___x_4724_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4705_, v_config_4706_, v_mvarId_4707_, v_a_4723_, v_snd_4719_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4744_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4727_ = v___x_4724_;
v_isShared_4728_ = v_isSharedCheck_4744_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4744_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
if (lean_obj_tag(v_a_4725_) == 0)
{
lean_object* v___x_4729_; lean_object* v___x_4731_; 
lean_dec(v_mvarId_4707_);
lean_dec_ref(v_config_4706_);
v___x_4729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4729_, 0, v_a_4725_);
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 0, v___x_4729_);
v___x_4731_ = v___x_4721_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v___x_4729_);
lean_ctor_set(v_reuseFailAlloc_4735_, 1, v_snd_4719_);
v___x_4731_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
lean_object* v___x_4733_; 
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 0, v___x_4731_);
v___x_4733_ = v___x_4727_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4731_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4737_; lean_object* v___x_4739_; 
lean_del_object(v___x_4727_);
lean_dec(v_snd_4719_);
v_a_4736_ = lean_ctor_get(v_a_4725_, 0);
lean_inc(v_a_4736_);
lean_dec_ref_known(v_a_4725_, 1);
v___x_4737_ = lean_box(0);
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 1, v_a_4736_);
lean_ctor_set(v___x_4721_, 0, v___x_4737_);
v___x_4739_ = v___x_4721_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4737_);
lean_ctor_set(v_reuseFailAlloc_4743_, 1, v_a_4736_);
v___x_4739_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
size_t v___x_4740_; size_t v___x_4741_; 
v___x_4740_ = ((size_t)1ULL);
v___x_4741_ = lean_usize_add(v_i_4710_, v___x_4740_);
v_i_4710_ = v___x_4741_;
v_b_4711_ = v___x_4739_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
lean_del_object(v___x_4721_);
lean_dec(v_snd_4719_);
lean_dec(v_mvarId_4707_);
lean_dec_ref(v_config_4706_);
v_a_4745_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4724_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4724_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4755_, lean_object* v_config_4756_, lean_object* v_mvarId_4757_, lean_object* v_as_4758_, lean_object* v_sz_4759_, lean_object* v_i_4760_, lean_object* v_b_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
size_t v_sz_boxed_4767_; size_t v_i_boxed_4768_; lean_object* v_res_4769_; 
v_sz_boxed_4767_ = lean_unbox_usize(v_sz_4759_);
lean_dec(v_sz_4759_);
v_i_boxed_4768_ = lean_unbox_usize(v_i_4760_);
lean_dec(v_i_4760_);
v_res_4769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4755_, v_config_4756_, v_mvarId_4757_, v_as_4758_, v_sz_boxed_4767_, v_i_boxed_4768_, v_b_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec_ref(v_as_4758_);
lean_dec_ref(v_init_4755_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4770_, lean_object* v_config_4771_, lean_object* v_mvarId_4772_, lean_object* v_n_4773_, lean_object* v_b_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4770_, v_config_4771_, v_mvarId_4772_, v_n_4773_, v_b_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec_ref(v_n_4773_);
lean_dec_ref(v_init_4770_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4781_, lean_object* v_mvarId_4782_, lean_object* v_t_4783_, lean_object* v_init_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v_root_4790_; lean_object* v_tail_4791_; lean_object* v___x_4792_; 
v_root_4790_ = lean_ctor_get(v_t_4783_, 0);
v_tail_4791_ = lean_ctor_get(v_t_4783_, 1);
lean_inc(v_mvarId_4782_);
lean_inc_ref(v_config_4781_);
lean_inc_ref(v_init_4784_);
v___x_4792_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4784_, v_config_4781_, v_mvarId_4782_, v_root_4790_, v_init_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
lean_dec_ref(v_init_4784_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4829_; 
v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4795_ = v___x_4792_;
v_isShared_4796_ = v_isSharedCheck_4829_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4792_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4829_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
if (lean_obj_tag(v_a_4793_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4799_; 
lean_dec(v_mvarId_4782_);
lean_dec_ref(v_config_4781_);
v_a_4797_ = lean_ctor_get(v_a_4793_, 0);
lean_inc(v_a_4797_);
lean_dec_ref_known(v_a_4793_, 1);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 0, v_a_4797_);
v___x_4799_ = v___x_4795_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4797_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; size_t v_sz_4804_; size_t v___x_4805_; lean_object* v___x_4806_; 
lean_del_object(v___x_4795_);
v_a_4801_ = lean_ctor_get(v_a_4793_, 0);
lean_inc(v_a_4801_);
lean_dec_ref_known(v_a_4793_, 1);
v___x_4802_ = lean_box(0);
v___x_4803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4802_);
lean_ctor_set(v___x_4803_, 1, v_a_4801_);
v_sz_4804_ = lean_array_size(v_tail_4791_);
v___x_4805_ = ((size_t)0ULL);
v___x_4806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4781_, v_mvarId_4782_, v_tail_4791_, v_sz_4804_, v___x_4805_, v___x_4803_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4820_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4820_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4820_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v_fst_4811_; 
v_fst_4811_ = lean_ctor_get(v_a_4807_, 0);
if (lean_obj_tag(v_fst_4811_) == 0)
{
lean_object* v_snd_4812_; lean_object* v___x_4814_; 
v_snd_4812_ = lean_ctor_get(v_a_4807_, 1);
lean_inc(v_snd_4812_);
lean_dec(v_a_4807_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v_snd_4812_);
v___x_4814_ = v___x_4809_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_snd_4812_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
else
{
lean_object* v_val_4816_; lean_object* v___x_4818_; 
lean_inc_ref(v_fst_4811_);
lean_dec(v_a_4807_);
v_val_4816_ = lean_ctor_get(v_fst_4811_, 0);
lean_inc(v_val_4816_);
lean_dec_ref_known(v_fst_4811_, 1);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v_val_4816_);
v___x_4818_ = v___x_4809_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_val_4816_);
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
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
v_a_4821_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4806_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4806_);
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
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
lean_dec(v_mvarId_4782_);
lean_dec_ref(v_config_4781_);
v_a_4830_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4792_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4792_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4838_, lean_object* v_mvarId_4839_, lean_object* v_t_4840_, lean_object* v_init_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4838_, v_mvarId_4839_, v_t_4840_, v_init_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec_ref(v_t_4840_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4848_, lean_object* v___x_4849_, lean_object* v_config_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v___x_4856_; 
lean_inc(v_mvarId_4848_);
v___x_4856_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4848_, v___x_4849_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v___x_4857_; 
lean_dec_ref_known(v___x_4856_, 1);
lean_inc(v_mvarId_4848_);
v___x_4857_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4848_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4891_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4860_ = v___x_4857_;
v_isShared_4861_ = v_isSharedCheck_4891_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4857_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4891_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
uint8_t v___x_4862_; 
v___x_4862_ = lean_unbox(v_a_4858_);
if (v___x_4862_ == 0)
{
lean_object* v_lctx_4863_; lean_object* v_decls_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
lean_del_object(v___x_4860_);
v_lctx_4863_ = lean_ctor_get(v___y_4851_, 2);
v_decls_4864_ = lean_ctor_get(v_lctx_4863_, 1);
v___x_4865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4866_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4850_, v_mvarId_4848_, v_decls_4864_, v___x_4865_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
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
lean_object* v_fst_4871_; 
v_fst_4871_ = lean_ctor_get(v_a_4867_, 0);
lean_inc(v_fst_4871_);
lean_dec(v_a_4867_);
if (lean_obj_tag(v_fst_4871_) == 0)
{
lean_object* v___x_4873_; 
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v_a_4858_);
v___x_4873_ = v___x_4869_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4858_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
else
{
lean_object* v_val_4875_; lean_object* v___x_4877_; 
lean_dec(v_a_4858_);
v_val_4875_ = lean_ctor_get(v_fst_4871_, 0);
lean_inc(v_val_4875_);
lean_dec_ref_known(v_fst_4871_, 1);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v_val_4875_);
v___x_4877_ = v___x_4869_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_val_4875_);
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
lean_dec(v_a_4858_);
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
else
{
lean_object* v___x_4889_; 
lean_dec_ref(v_config_4850_);
lean_dec(v_mvarId_4848_);
if (v_isShared_4861_ == 0)
{
v___x_4889_ = v___x_4860_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4858_);
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
else
{
lean_dec_ref(v_config_4850_);
lean_dec(v_mvarId_4848_);
return v___x_4857_;
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec_ref(v_config_4850_);
lean_dec(v_mvarId_4848_);
v_a_4892_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4856_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4856_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4900_, lean_object* v___x_4901_, lean_object* v_config_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4900_, v___x_4901_, v_config_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
lean_dec(v___y_4906_);
lean_dec_ref(v___y_4905_);
lean_dec(v___y_4904_);
lean_dec_ref(v___y_4903_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4911_, lean_object* v_config_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_){
_start:
{
lean_object* v___x_4918_; lean_object* v___f_4919_; lean_object* v___x_4920_; 
v___x_4918_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4911_);
v___f_4919_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4919_, 0, v_mvarId_4911_);
lean_closure_set(v___f_4919_, 1, v___x_4918_);
lean_closure_set(v___f_4919_, 2, v_config_4912_);
v___x_4920_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4911_, v___f_4919_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4921_, lean_object* v_config_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
lean_object* v_res_4928_; 
v_res_4928_ = l_Lean_MVarId_contradictionCore(v_mvarId_4921_, v_config_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4929_, lean_object* v_config_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v___x_4936_; 
lean_inc(v_mvarId_4929_);
v___x_4936_ = l_Lean_MVarId_contradictionCore(v_mvarId_4929_, v_config_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4949_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4939_ = v___x_4936_;
v_isShared_4940_ = v_isSharedCheck_4949_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4936_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4949_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
uint8_t v___x_4941_; 
v___x_4941_ = lean_unbox(v_a_4937_);
lean_dec(v_a_4937_);
if (v___x_4941_ == 0)
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
lean_del_object(v___x_4939_);
v___x_4942_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4943_ = lean_box(0);
v___x_4944_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4942_, v_mvarId_4929_, v___x_4943_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
return v___x_4944_;
}
else
{
lean_object* v___x_4945_; lean_object* v___x_4947_; 
lean_dec(v_mvarId_4929_);
v___x_4945_ = lean_box(0);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 0, v___x_4945_);
v___x_4947_ = v___x_4939_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4945_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
}
else
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
lean_dec(v_mvarId_4929_);
v_a_4950_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4936_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4936_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4958_, lean_object* v_config_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_Lean_MVarId_contradiction(v_mvarId_4958_, v_config_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
return v_res_4965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5028_; uint8_t v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5028_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_5029_ = 0;
v___x_5030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_5031_ = l_Lean_registerTraceClass(v___x_5028_, v___x_5029_, v___x_5030_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_5033_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
