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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_10_; uint8_t v___x_11_; uint8_t v___x_12_; 
v___x_10_ = l_Lean_Expr_appArg_x21(v_e_6_);
v___x_11_ = l_Lean_Expr_hasLooseBVars(v___x_10_);
lean_dec_ref(v___x_10_);
v___x_12_ = lean_bool_not(v___x_11_);
return v___x_12_;
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
size_t v_x_1104__boxed_157_; size_t v_x_1105__boxed_158_; lean_object* v_res_159_; 
v_x_1104__boxed_157_ = lean_unbox_usize(v_x_153_);
lean_dec(v_x_153_);
v_x_1105__boxed_158_ = lean_unbox_usize(v_x_154_);
lean_dec(v_x_154_);
v_res_159_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_152_, v_x_1104__boxed_157_, v_x_1105__boxed_158_, v_x_155_, v_x_156_);
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
size_t v_x_1459__boxed_312_; size_t v_x_1460__boxed_313_; lean_object* v_res_314_; 
v_x_1459__boxed_312_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_x_1460__boxed_313_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_res_314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_306_, v_x_307_, v_x_1459__boxed_312_, v_x_1460__boxed_313_, v_x_310_, v_x_311_);
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
size_t v_sz_boxed_674_; size_t v___x_18284__boxed_675_; uint8_t v___x_18286__boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v___x_18284__boxed_675_ = lean_unbox_usize(v___x_665_);
lean_dec(v___x_665_);
v___x_18286__boxed_676_ = lean_unbox(v___x_667_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_661_, v_mvarId_662_, v_fields_663_, v_sz_boxed_674_, v___x_18284__boxed_675_, v___x_666_, v___x_18286__boxed_676_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
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
uint8_t v___x_18406__boxed_877_; uint8_t v___x_18409__boxed_878_; lean_object* v_res_879_; 
v___x_18406__boxed_877_ = lean_unbox(v___x_867_);
v___x_18409__boxed_878_ = lean_unbox(v___x_870_);
v_res_879_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_864_, v_fvarId_865_, v___x_866_, v___x_18406__boxed_877_, v___x_868_, v_val_869_, v___x_18409__boxed_878_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
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
lean_object* v_binderType_1278_; lean_object* v_body_1279_; uint8_t v___y_1281_; lean_object* v___x_1285_; uint8_t v___x_1286_; uint8_t v___x_1287_; 
v_binderType_1278_ = lean_ctor_get(v_e_1276_, 1);
v_body_1279_ = lean_ctor_get(v_e_1276_, 2);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_expr_has_loose_bvar(v_body_1279_, v___x_1285_);
v___x_1287_ = lean_bool_not(v___x_1286_);
if (v___x_1287_ == 0)
{
v___y_1281_ = v___x_1287_;
goto v___jp_1280_;
}
else
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Lean_Expr_isEq(v_binderType_1278_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_Expr_isHEq(v_binderType_1278_);
v___y_1281_ = v___x_1289_;
goto v___jp_1280_;
}
else
{
v___y_1281_ = v___x_1288_;
goto v___jp_1280_;
}
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
uint8_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = l_Lean_Expr_hasMVar(v_e_1317_);
v___x_1321_ = lean_bool_not(v___x_1320_);
if (v___x_1321_ == 0)
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
else
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_e_1317_);
return v___x_1342_;
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
uint8_t v___x_7194__boxed_1726_; lean_object* v_res_1727_; 
v___x_7194__boxed_1726_ = lean_unbox(v___x_1718_);
v_res_1727_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1717_, v___x_7194__boxed_1726_, v_localDecl_1719_, v_mvarId_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
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
v___x_1733_ = lean_unsigned_to_nat(120u);
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
lean_inc_ref(v___x_1744_);
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
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1(void){
_start:
{
uint8_t v___x_1792_; uint64_t v___x_1793_; 
v___x_1792_ = 1;
v___x_1793_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(0);
v___x_1803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6));
v___x_1804_ = l_Lean_mkConst(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8(void){
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
lean_object* v_snd_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_2471_; 
v_snd_1820_ = lean_ctor_get(v_b_1812_, 1);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_b_1812_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; 
v_unused_2472_ = lean_ctor_get(v_b_1812_, 0);
lean_dec(v_unused_2472_);
v___x_1822_ = v_b_1812_;
v_isShared_1823_ = v_isSharedCheck_2471_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_snd_1820_);
lean_dec(v_b_1812_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_2471_;
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
lean_object* v_val_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_2470_; 
v_val_1839_ = lean_ctor_get(v_a_1838_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_a_1838_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_1841_ = v_a_1838_;
v_isShared_1842_ = v_isSharedCheck_2470_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_val_1839_);
lean_dec(v_a_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_2470_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; uint8_t v___y_1850_; uint8_t v___x_1869_; lean_object* v___y_1871_; lean_object* v___y_1872_; uint8_t v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; uint8_t v___y_1876_; uint8_t v___y_1879_; uint8_t v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1888_; uint8_t v___y_1889_; uint8_t v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; uint8_t v___y_1894_; 
v___x_1843_ = lean_box(0);
v___x_1844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1869_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1839_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1909_; uint8_t v___y_1911_; uint8_t v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; uint8_t v___y_1924_; uint8_t v___y_1925_; lean_object* v___y_1926_; uint8_t v___y_1927_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; uint8_t v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1935_; lean_object* v_a_1936_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; uint8_t v___y_1943_; uint8_t v___y_1944_; lean_object* v___y_1945_; uint8_t v___y_1946_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; uint8_t v___y_2035_; uint8_t v___y_2036_; lean_object* v___y_2037_; uint8_t v___y_2038_; uint8_t v___y_2054_; uint8_t v_isHEq_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; uint8_t v_isEq_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___x_2407_; 
v___x_1909_ = l_Lean_LocalDecl_type(v_val_1839_);
lean_inc_ref(v___x_1909_);
v___x_2407_ = l_Lean_Meta_matchNot_x3f(v___x_1909_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
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
v___x_2410_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2409_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
if (lean_obj_tag(v_a_2411_) == 1)
{
lean_object* v_val_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec_ref(v_config_1807_);
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
lean_inc(v_mvarId_1808_);
v___x_2416_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v___x_2418_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2419_ = l_Lean_mkFVar(v_val_2412_);
v___x_2420_ = l_Lean_Expr_app___override(v___x_2418_, v___x_2419_);
v___x_2421_ = l_Lean_Meta_mkFalseElim(v_a_2417_, v___x_2420_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2423_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2423_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2422_, v___y_1814_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
lean_dec_ref_known(v___x_2423_, 1);
v___x_2424_ = lean_box(v___x_1818_);
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
lean_ctor_set(v___x_2427_, 1, v___x_1843_);
v_a_1825_ = v___x_2427_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_del_object(v___x_2414_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
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
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
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
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
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
v___y_2273_ = v___y_1813_;
v___y_2274_ = v___y_1814_;
v___y_2275_ = v___y_1815_;
v___y_2276_ = v___y_1816_;
goto v___jp_2272_;
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
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
v___y_2273_ = v___y_1813_;
v___y_2274_ = v___y_1814_;
v___y_2275_ = v___y_1815_;
v___y_2276_ = v___y_1816_;
goto v___jp_2272_;
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
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
v___jp_1910_:
{
uint8_t v_genDiseq_1917_; 
v_genDiseq_1917_ = lean_ctor_get_uint8(v_config_1807_, sizeof(void*)*1 + 2);
if (v_genDiseq_1917_ == 0)
{
lean_dec_ref(v___x_1909_);
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___y_1911_;
v___y_1890_ = v___y_1912_;
v___y_1891_ = v___y_1915_;
v___y_1892_ = v___y_1914_;
v___y_1893_ = v___y_1916_;
v___y_1894_ = v___x_1869_;
goto v___jp_1887_;
}
else
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1909_);
v___y_1888_ = v___y_1913_;
v___y_1889_ = v___y_1911_;
v___y_1890_ = v___y_1912_;
v___y_1891_ = v___y_1915_;
v___y_1892_ = v___y_1914_;
v___y_1893_ = v___y_1916_;
v___y_1894_ = v___x_1918_;
goto v___jp_1887_;
}
}
v___jp_1919_:
{
if (v___y_1927_ == 0)
{
lean_dec_ref(v___y_1920_);
v___y_1911_ = v___y_1924_;
v___y_1912_ = v___y_1925_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___y_1923_;
v___y_1915_ = v___y_1922_;
v___y_1916_ = v___y_1926_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1928_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v___x_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___y_1920_);
return v___x_1928_;
}
}
v___jp_1929_:
{
uint8_t v___x_1937_; 
v___x_1937_ = l_Lean_Exception_isInterrupt(v_a_1936_);
if (v___x_1937_ == 0)
{
uint8_t v___x_1938_; 
lean_inc_ref(v_a_1936_);
v___x_1938_ = l_Lean_Exception_isRuntime(v_a_1936_);
v___y_1920_ = v_a_1936_;
v___y_1921_ = v___y_1930_;
v___y_1922_ = v___y_1932_;
v___y_1923_ = v___y_1931_;
v___y_1924_ = v___y_1933_;
v___y_1925_ = v___y_1935_;
v___y_1926_ = v___y_1934_;
v___y_1927_ = v___x_1938_;
goto v___jp_1919_;
}
else
{
v___y_1920_ = v_a_1936_;
v___y_1921_ = v___y_1930_;
v___y_1922_ = v___y_1932_;
v___y_1923_ = v___y_1931_;
v___y_1924_ = v___y_1933_;
v___y_1925_ = v___y_1935_;
v___y_1926_ = v___y_1934_;
v___y_1927_ = v___x_1937_;
goto v___jp_1919_;
}
}
v___jp_1939_:
{
if (v___y_1946_ == 0)
{
v___y_1911_ = v___y_1943_;
v___y_1912_ = v___y_1944_;
v___y_1913_ = v___y_1940_;
v___y_1914_ = v___y_1942_;
v___y_1915_ = v___y_1941_;
v___y_1916_ = v___y_1945_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1947_; 
lean_inc_ref(v___x_1909_);
v___x_1947_ = l_Lean_Meta_mkDecide(v___x_1909_, v___y_1940_, v___y_1942_, v___y_1941_, v___y_1945_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; uint8_t v_foApprox_1950_; uint8_t v_ctxApprox_1951_; uint8_t v_quasiPatternApprox_1952_; uint8_t v_constApprox_1953_; uint8_t v_isDefEqStuckEx_1954_; uint8_t v_unificationHints_1955_; uint8_t v_proofIrrelevance_1956_; uint8_t v_assignSyntheticOpaque_1957_; uint8_t v_offsetCnstrs_1958_; uint8_t v_etaStruct_1959_; uint8_t v_univApprox_1960_; uint8_t v_iota_1961_; uint8_t v_beta_1962_; uint8_t v_proj_1963_; uint8_t v_zeta_1964_; uint8_t v_zetaDelta_1965_; uint8_t v_zetaUnused_1966_; uint8_t v_zetaHave_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2029_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1949_ = l_Lean_Meta_Context_config(v___y_1940_);
v_foApprox_1950_ = lean_ctor_get_uint8(v___x_1949_, 0);
v_ctxApprox_1951_ = lean_ctor_get_uint8(v___x_1949_, 1);
v_quasiPatternApprox_1952_ = lean_ctor_get_uint8(v___x_1949_, 2);
v_constApprox_1953_ = lean_ctor_get_uint8(v___x_1949_, 3);
v_isDefEqStuckEx_1954_ = lean_ctor_get_uint8(v___x_1949_, 4);
v_unificationHints_1955_ = lean_ctor_get_uint8(v___x_1949_, 5);
v_proofIrrelevance_1956_ = lean_ctor_get_uint8(v___x_1949_, 6);
v_assignSyntheticOpaque_1957_ = lean_ctor_get_uint8(v___x_1949_, 7);
v_offsetCnstrs_1958_ = lean_ctor_get_uint8(v___x_1949_, 8);
v_etaStruct_1959_ = lean_ctor_get_uint8(v___x_1949_, 10);
v_univApprox_1960_ = lean_ctor_get_uint8(v___x_1949_, 11);
v_iota_1961_ = lean_ctor_get_uint8(v___x_1949_, 12);
v_beta_1962_ = lean_ctor_get_uint8(v___x_1949_, 13);
v_proj_1963_ = lean_ctor_get_uint8(v___x_1949_, 14);
v_zeta_1964_ = lean_ctor_get_uint8(v___x_1949_, 15);
v_zetaDelta_1965_ = lean_ctor_get_uint8(v___x_1949_, 16);
v_zetaUnused_1966_ = lean_ctor_get_uint8(v___x_1949_, 17);
v_zetaHave_1967_ = lean_ctor_get_uint8(v___x_1949_, 18);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_1969_ = v___x_1949_;
v_isShared_1970_ = v_isSharedCheck_2029_;
goto v_resetjp_1968_;
}
else
{
lean_dec(v___x_1949_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2029_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
uint8_t v_trackZetaDelta_1971_; lean_object* v_zetaDeltaSet_1972_; lean_object* v_lctx_1973_; lean_object* v_localInstances_1974_; lean_object* v_defEqCtx_x3f_1975_; lean_object* v_synthPendingDepth_1976_; lean_object* v_canUnfold_x3f_1977_; uint8_t v_univApprox_1978_; uint8_t v_inTypeClassResolution_1979_; uint8_t v_cacheInferType_1980_; uint8_t v___x_1981_; lean_object* v_config_1983_; 
v_trackZetaDelta_1971_ = lean_ctor_get_uint8(v___y_1940_, sizeof(void*)*7);
v_zetaDeltaSet_1972_ = lean_ctor_get(v___y_1940_, 1);
v_lctx_1973_ = lean_ctor_get(v___y_1940_, 2);
v_localInstances_1974_ = lean_ctor_get(v___y_1940_, 3);
v_defEqCtx_x3f_1975_ = lean_ctor_get(v___y_1940_, 4);
v_synthPendingDepth_1976_ = lean_ctor_get(v___y_1940_, 5);
v_canUnfold_x3f_1977_ = lean_ctor_get(v___y_1940_, 6);
v_univApprox_1978_ = lean_ctor_get_uint8(v___y_1940_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1979_ = lean_ctor_get_uint8(v___y_1940_, sizeof(void*)*7 + 2);
v_cacheInferType_1980_ = lean_ctor_get_uint8(v___y_1940_, sizeof(void*)*7 + 3);
v___x_1981_ = 1;
if (v_isShared_1970_ == 0)
{
v_config_1983_ = v___x_1969_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 0, v_foApprox_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 1, v_ctxApprox_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 2, v_quasiPatternApprox_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 3, v_constApprox_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 4, v_isDefEqStuckEx_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 5, v_unificationHints_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 6, v_proofIrrelevance_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 7, v_assignSyntheticOpaque_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 8, v_offsetCnstrs_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 10, v_etaStruct_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 11, v_univApprox_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 12, v_iota_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 13, v_beta_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 14, v_proj_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 15, v_zeta_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 16, v_zetaDelta_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 17, v_zetaUnused_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, 18, v_zetaHave_1967_);
v_config_1983_ = v_reuseFailAlloc_2028_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
uint64_t v___x_1984_; uint64_t v___x_1985_; uint64_t v___x_1986_; uint64_t v___x_1987_; uint64_t v___x_1988_; uint64_t v_key_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_ctor_set_uint8(v_config_1983_, 9, v___x_1981_);
v___x_1984_ = l_Lean_Meta_Context_configKey(v___y_1940_);
v___x_1985_ = 3ULL;
v___x_1986_ = lean_uint64_shift_right(v___x_1984_, v___x_1985_);
v___x_1987_ = lean_uint64_shift_left(v___x_1986_, v___x_1985_);
v___x_1988_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_1989_ = lean_uint64_lor(v___x_1987_, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1990_, 0, v_config_1983_);
lean_ctor_set_uint64(v___x_1990_, sizeof(void*)*1, v_key_1989_);
lean_inc(v_canUnfold_x3f_1977_);
lean_inc(v_synthPendingDepth_1976_);
lean_inc(v_defEqCtx_x3f_1975_);
lean_inc_ref(v_localInstances_1974_);
lean_inc_ref(v_lctx_1973_);
lean_inc(v_zetaDeltaSet_1972_);
v___x_1991_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v_zetaDeltaSet_1972_);
lean_ctor_set(v___x_1991_, 2, v_lctx_1973_);
lean_ctor_set(v___x_1991_, 3, v_localInstances_1974_);
lean_ctor_set(v___x_1991_, 4, v_defEqCtx_x3f_1975_);
lean_ctor_set(v___x_1991_, 5, v_synthPendingDepth_1976_);
lean_ctor_set(v___x_1991_, 6, v_canUnfold_x3f_1977_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*7, v_trackZetaDelta_1971_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*7 + 1, v_univApprox_1978_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1979_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*7 + 3, v_cacheInferType_1980_);
lean_inc(v___y_1945_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1942_);
lean_inc(v_a_1948_);
v___x_1992_ = lean_whnf(v_a_1948_, v___x_1991_, v___y_1942_, v___y_1941_, v___y_1945_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_1995_ = l_Lean_Expr_isConstOf(v_a_1993_, v___x_1994_);
lean_dec(v_a_1993_);
if (v___x_1995_ == 0)
{
lean_dec(v_a_1948_);
v___y_1911_ = v___y_1943_;
v___y_1912_ = v___y_1944_;
v___y_1913_ = v___y_1940_;
v___y_1914_ = v___y_1942_;
v___y_1915_ = v___y_1941_;
v___y_1916_ = v___y_1945_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1996_; 
lean_inc(v_a_1948_);
v___x_1996_ = l_Lean_Meta_mkEqRefl(v_a_1948_, v___y_1940_, v___y_1942_, v___y_1941_, v___y_1945_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
lean_inc(v_mvarId_1808_);
v___x_1998_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_1940_, v___y_1942_, v___y_1941_, v___y_1945_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v_nargs_2000_; lean_object* v___x_2001_; lean_object* v_dummy_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v_nargs_2000_ = l_Lean_Expr_getAppNumArgs(v_a_1948_);
v___x_2001_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2002_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2000_);
v___x_2003_ = lean_mk_array(v_nargs_2000_, v_dummy_2002_);
v___x_2004_ = lean_unsigned_to_nat(1u);
v___x_2005_ = lean_nat_sub(v_nargs_2000_, v___x_2004_);
lean_dec(v_nargs_2000_);
v___x_2006_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1948_, v___x_2003_, v___x_2005_);
v___x_2007_ = lean_array_push(v___x_2006_, v_a_1997_);
v___x_2008_ = l_Lean_mkAppN(v___x_2001_, v___x_2007_);
lean_dec_ref(v___x_2007_);
lean_inc(v_val_1839_);
v___x_2009_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2010_ = l_Lean_Meta_mkAbsurd(v_a_1999_, v___x_2009_, v___x_2008_, v___y_1940_, v___y_1942_, v___y_1941_, v___y_1945_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
lean_inc(v_mvarId_1808_);
v___x_2012_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2011_, v___y_1942_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; 
v_unused_2022_ = lean_ctor_get(v___x_2012_, 0);
lean_dec(v_unused_2022_);
v___x_2014_ = v___x_2012_;
v_isShared_2015_ = v_isSharedCheck_2021_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v___x_2012_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2021_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_box(v___x_1818_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v___x_1843_);
v_a_1825_ = v___x_2019_;
goto v___jp_1824_;
}
}
}
else
{
lean_object* v_a_2023_; 
v_a_2023_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2012_, 1);
v___y_1930_ = v___y_1940_;
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1943_;
v___y_1934_ = v___y_1945_;
v___y_1935_ = v___y_1944_;
v_a_1936_ = v_a_2023_;
goto v___jp_1929_;
}
}
else
{
lean_object* v_a_2024_; 
v_a_2024_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2010_, 1);
v___y_1930_ = v___y_1940_;
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1943_;
v___y_1934_ = v___y_1945_;
v___y_1935_ = v___y_1944_;
v_a_1936_ = v_a_2024_;
goto v___jp_1929_;
}
}
else
{
lean_object* v_a_2025_; 
lean_dec(v_a_1997_);
lean_dec(v_a_1948_);
v_a_2025_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_1998_, 1);
v___y_1930_ = v___y_1940_;
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1943_;
v___y_1934_ = v___y_1945_;
v___y_1935_ = v___y_1944_;
v_a_1936_ = v_a_2025_;
goto v___jp_1929_;
}
}
else
{
lean_object* v_a_2026_; 
lean_dec(v_a_1948_);
v_a_2026_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_1996_, 1);
v___y_1930_ = v___y_1940_;
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1943_;
v___y_1934_ = v___y_1945_;
v___y_1935_ = v___y_1944_;
v_a_1936_ = v_a_2026_;
goto v___jp_1929_;
}
}
}
else
{
lean_object* v_a_2027_; 
lean_dec(v_a_1948_);
v_a_2027_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_1992_, 1);
v___y_1930_ = v___y_1940_;
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1943_;
v___y_1934_ = v___y_1945_;
v___y_1935_ = v___y_1944_;
v_a_1936_ = v_a_2027_;
goto v___jp_1929_;
}
}
}
}
else
{
lean_object* v_a_2030_; 
v_a_2030_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_1947_, 1);
v___y_1930_ = v___y_1940_;
v___y_1931_ = v___y_1942_;
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1943_;
v___y_1934_ = v___y_1945_;
v___y_1935_ = v___y_1944_;
v_a_1936_ = v_a_2030_;
goto v___jp_1929_;
}
}
}
v___jp_2031_:
{
if (v___y_2038_ == 0)
{
v___y_1911_ = v___y_2035_;
v___y_1912_ = v___y_2036_;
v___y_1913_ = v___y_2032_;
v___y_1914_ = v___y_2034_;
v___y_1915_ = v___y_2033_;
v___y_1916_ = v___y_2037_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_2039_; 
lean_inc_ref(v___x_1909_);
v___x_2039_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1909_, v___y_2034_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; uint8_t v___x_2041_; uint8_t v___x_2042_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_Expr_hasMVar(v_a_2040_);
v___x_2042_ = lean_bool_not(v___x_2041_);
if (v___x_2042_ == 0)
{
lean_dec(v_a_2040_);
v___y_1940_ = v___y_2032_;
v___y_1941_ = v___y_2033_;
v___y_1942_ = v___y_2034_;
v___y_1943_ = v___y_2035_;
v___y_1944_ = v___y_2036_;
v___y_1945_ = v___y_2037_;
v___y_1946_ = v___x_1869_;
goto v___jp_1939_;
}
else
{
uint8_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = l_Lean_Expr_hasFVar(v_a_2040_);
lean_dec(v_a_2040_);
v___x_2044_ = lean_bool_not(v___x_2043_);
v___y_1940_ = v___y_2032_;
v___y_1941_ = v___y_2033_;
v___y_1942_ = v___y_2034_;
v___y_1943_ = v___y_2035_;
v___y_1944_ = v___y_2036_;
v___y_1945_ = v___y_2037_;
v___y_1946_ = v___x_2044_;
goto v___jp_1939_;
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2045_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2039_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2039_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
v___jp_2053_:
{
uint8_t v_useDecide_2060_; 
v_useDecide_2060_ = lean_ctor_get_uint8(v_config_1807_, sizeof(void*)*1);
if (v_useDecide_2060_ == 0)
{
v___y_2032_ = v___y_2056_;
v___y_2033_ = v___y_2058_;
v___y_2034_ = v___y_2057_;
v___y_2035_ = v_isHEq_2055_;
v___y_2036_ = v___y_2054_;
v___y_2037_ = v___y_2059_;
v___y_2038_ = v___x_1869_;
goto v___jp_2031_;
}
else
{
uint8_t v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = l_Lean_Expr_hasFVar(v___x_1909_);
v___x_2062_ = lean_bool_not(v___x_2061_);
v___y_2032_ = v___y_2056_;
v___y_2033_ = v___y_2058_;
v___y_2034_ = v___y_2057_;
v___y_2035_ = v_isHEq_2055_;
v___y_2036_ = v___y_2054_;
v___y_2037_ = v___y_2059_;
v___y_2038_ = v___x_2062_;
goto v___jp_2031_;
}
}
v___jp_2063_:
{
lean_object* v___x_2069_; 
lean_inc_ref(v___x_1909_);
v___x_2069_ = l_Lean_Meta_matchHEq_x3f(v___x_1909_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
if (lean_obj_tag(v_a_2070_) == 1)
{
lean_object* v_val_2071_; lean_object* v_snd_2072_; lean_object* v_snd_2073_; lean_object* v_fst_2074_; lean_object* v_fst_2075_; lean_object* v_fst_2076_; lean_object* v_snd_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2171_; 
v_val_2071_ = lean_ctor_get(v_a_2070_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v_a_2070_, 1);
v_snd_2072_ = lean_ctor_get(v_val_2071_, 1);
lean_inc(v_snd_2072_);
v_snd_2073_ = lean_ctor_get(v_snd_2072_, 1);
lean_inc(v_snd_2073_);
v_fst_2074_ = lean_ctor_get(v_val_2071_, 0);
lean_inc(v_fst_2074_);
lean_dec(v_val_2071_);
v_fst_2075_ = lean_ctor_get(v_snd_2072_, 0);
lean_inc(v_fst_2075_);
lean_dec(v_snd_2072_);
v_fst_2076_ = lean_ctor_get(v_snd_2073_, 0);
v_snd_2077_ = lean_ctor_get(v_snd_2073_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_snd_2073_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2079_ = v_snd_2073_;
v_isShared_2080_ = v_isSharedCheck_2171_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_snd_2077_);
lean_inc(v_fst_2076_);
lean_dec(v_snd_2073_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2171_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2075_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
if (lean_obj_tag(v_a_2082_) == 1)
{
lean_object* v_val_2083_; lean_object* v___x_2084_; 
v_val_2083_ = lean_ctor_get(v_a_2082_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v_a_2082_, 1);
v___x_2084_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2077_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
if (lean_obj_tag(v_a_2085_) == 1)
{
lean_object* v_toConstantVal_2086_; lean_object* v_val_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2154_; 
v_toConstantVal_2086_ = lean_ctor_get(v_val_2083_, 0);
lean_inc_ref(v_toConstantVal_2086_);
lean_dec(v_val_2083_);
v_val_2087_ = lean_ctor_get(v_a_2085_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2089_ = v_a_2085_;
v_isShared_2090_ = v_isSharedCheck_2154_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_val_2087_);
lean_dec(v_a_2085_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2154_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_toConstantVal_2091_; lean_object* v_name_2092_; lean_object* v_name_2093_; uint8_t v___x_2094_; uint8_t v___x_2095_; 
v_toConstantVal_2091_ = lean_ctor_get(v_val_2087_, 0);
lean_inc_ref(v_toConstantVal_2091_);
lean_dec(v_val_2087_);
v_name_2092_ = lean_ctor_get(v_toConstantVal_2086_, 0);
lean_inc(v_name_2092_);
lean_dec_ref(v_toConstantVal_2086_);
v_name_2093_ = lean_ctor_get(v_toConstantVal_2091_, 0);
lean_inc(v_name_2093_);
lean_dec_ref(v_toConstantVal_2091_);
v___x_2094_ = lean_name_eq(v_name_2092_, v_name_2093_);
lean_dec(v_name_2093_);
lean_dec(v_name_2092_);
v___x_2095_ = lean_bool_not(v___x_2094_);
if (v___x_2095_ == 0)
{
lean_del_object(v___x_2089_);
lean_del_object(v___x_2079_);
lean_dec(v_fst_2076_);
lean_dec(v_fst_2074_);
v___y_2054_ = v_isEq_2064_;
v_isHEq_2055_ = v___x_1818_;
v___y_2056_ = v___y_2065_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
v___y_2059_ = v___y_2068_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Meta_isExprDefEq(v_fst_2074_, v_fst_2076_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; uint8_t v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = lean_unbox(v_a_2097_);
lean_dec(v_a_2097_);
if (v___x_2098_ == 0)
{
lean_del_object(v___x_2089_);
lean_del_object(v___x_2079_);
v___y_2054_ = v_isEq_2064_;
v_isHEq_2055_ = v___x_1818_;
v___y_2056_ = v___y_2065_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
v___y_2059_ = v___y_2068_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2099_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec_ref(v_config_1807_);
lean_inc(v_mvarId_1808_);
v___x_2099_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2102_ = l_Lean_Meta_mkEqOfHEq(v___x_2101_, v___x_1818_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = l_Lean_Meta_mkNoConfusion(v_a_2100_, v_a_2103_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2105_, v___y_2066_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec_ref_known(v___x_2106_, 1);
v___x_2107_ = lean_box(v___x_1818_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2107_);
v___x_2109_ = v___x_2089_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v___x_1843_);
lean_ctor_set(v___x_2079_, 0, v___x_2109_);
v___x_2111_ = v___x_2079_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_1843_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
v_a_1825_ = v___x_2111_;
goto v___jp_1824_;
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_del_object(v___x_2089_);
lean_del_object(v___x_2079_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_2114_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2106_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2106_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_del_object(v___x_2089_);
lean_del_object(v___x_2079_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2122_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2104_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2104_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_a_2100_);
lean_del_object(v___x_2089_);
lean_del_object(v___x_2079_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2130_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2102_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2102_);
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
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_del_object(v___x_2089_);
lean_del_object(v___x_2079_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2138_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2099_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2099_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_del_object(v___x_2089_);
lean_del_object(v___x_2079_);
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2146_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2096_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2096_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2085_);
lean_dec(v_val_2083_);
lean_del_object(v___x_2079_);
lean_dec(v_fst_2076_);
lean_dec(v_fst_2074_);
v___y_2054_ = v_isEq_2064_;
v_isHEq_2055_ = v___x_1818_;
v___y_2056_ = v___y_2065_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
v___y_2059_ = v___y_2068_;
goto v___jp_2053_;
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_val_2083_);
lean_del_object(v___x_2079_);
lean_dec(v_fst_2076_);
lean_dec(v_fst_2074_);
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2155_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2084_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2084_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_dec(v_a_2082_);
lean_del_object(v___x_2079_);
lean_dec(v_snd_2077_);
lean_dec(v_fst_2076_);
lean_dec(v_fst_2074_);
v___y_2054_ = v_isEq_2064_;
v_isHEq_2055_ = v___x_1818_;
v___y_2056_ = v___y_2065_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
v___y_2059_ = v___y_2068_;
goto v___jp_2053_;
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_del_object(v___x_2079_);
lean_dec(v_snd_2077_);
lean_dec(v_fst_2076_);
lean_dec(v_fst_2074_);
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2163_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2081_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2081_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
else
{
lean_dec(v_a_2070_);
v___y_2054_ = v_isEq_2064_;
v_isHEq_2055_ = v___x_1869_;
v___y_2056_ = v___y_2065_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
v___y_2059_ = v___y_2068_;
goto v___jp_2053_;
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2172_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2069_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2069_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
v___jp_2180_:
{
lean_object* v___x_2185_; 
lean_inc_ref(v___x_1909_);
v___x_2185_ = l_Lean_Meta_matchEq_x3f(v___x_1909_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
if (lean_obj_tag(v_a_2186_) == 1)
{
lean_object* v_val_2187_; lean_object* v_snd_2188_; lean_object* v_fst_2189_; lean_object* v_snd_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2263_; 
v_val_2187_ = lean_ctor_get(v_a_2186_, 0);
lean_inc(v_val_2187_);
lean_dec_ref_known(v_a_2186_, 1);
v_snd_2188_ = lean_ctor_get(v_val_2187_, 1);
lean_inc(v_snd_2188_);
lean_dec(v_val_2187_);
v_fst_2189_ = lean_ctor_get(v_snd_2188_, 0);
v_snd_2190_ = lean_ctor_get(v_snd_2188_, 1);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_snd_2188_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2192_ = v_snd_2188_;
v_isShared_2193_ = v_isSharedCheck_2263_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_snd_2190_);
lean_inc(v_fst_2189_);
lean_dec(v_snd_2188_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2263_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2189_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
if (lean_obj_tag(v_a_2195_) == 1)
{
lean_object* v_val_2196_; lean_object* v___x_2197_; 
v_val_2196_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_val_2196_);
lean_dec_ref_known(v_a_2195_, 1);
v___x_2197_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2190_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
if (lean_obj_tag(v_a_2198_) == 1)
{
lean_object* v_toConstantVal_2199_; lean_object* v_val_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2246_; 
v_toConstantVal_2199_ = lean_ctor_get(v_val_2196_, 0);
lean_inc_ref(v_toConstantVal_2199_);
lean_dec(v_val_2196_);
v_val_2200_ = lean_ctor_get(v_a_2198_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_a_2198_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2202_ = v_a_2198_;
v_isShared_2203_ = v_isSharedCheck_2246_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_val_2200_);
lean_dec(v_a_2198_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2246_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_toConstantVal_2204_; lean_object* v_name_2205_; lean_object* v_name_2206_; uint8_t v___x_2207_; uint8_t v___x_2208_; 
v_toConstantVal_2204_ = lean_ctor_get(v_val_2200_, 0);
lean_inc_ref(v_toConstantVal_2204_);
lean_dec(v_val_2200_);
v_name_2205_ = lean_ctor_get(v_toConstantVal_2199_, 0);
lean_inc(v_name_2205_);
lean_dec_ref(v_toConstantVal_2199_);
v_name_2206_ = lean_ctor_get(v_toConstantVal_2204_, 0);
lean_inc(v_name_2206_);
lean_dec_ref(v_toConstantVal_2204_);
v___x_2207_ = lean_name_eq(v_name_2205_, v_name_2206_);
lean_dec(v_name_2206_);
lean_dec(v_name_2205_);
v___x_2208_ = lean_bool_not(v___x_2207_);
if (v___x_2208_ == 0)
{
lean_del_object(v___x_2202_);
lean_del_object(v___x_2192_);
v_isEq_2064_ = v___x_1818_;
v___y_2065_ = v___y_2181_;
v___y_2066_ = v___y_2182_;
v___y_2067_ = v___y_2183_;
v___y_2068_ = v___y_2184_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2209_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec_ref(v_config_1807_);
lean_inc(v_mvarId_1808_);
v___x_2209_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2212_ = l_Lean_Meta_mkNoConfusion(v_a_2210_, v___x_2211_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2213_, v___y_2182_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_dec_ref_known(v___x_2214_, 1);
v___x_2215_ = lean_box(v___x_1818_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2215_);
v___x_2217_ = v___x_2202_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2219_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v___x_1843_);
lean_ctor_set(v___x_2192_, 0, v___x_2217_);
v___x_2219_ = v___x_2192_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_1843_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
v_a_1825_ = v___x_2219_;
goto v___jp_1824_;
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_del_object(v___x_2202_);
lean_del_object(v___x_2192_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_2222_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2214_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2214_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_del_object(v___x_2202_);
lean_del_object(v___x_2192_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2230_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2212_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2212_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_del_object(v___x_2202_);
lean_del_object(v___x_2192_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
v_a_2238_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2209_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2209_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2198_);
lean_dec(v_val_2196_);
lean_del_object(v___x_2192_);
v_isEq_2064_ = v___x_1818_;
v___y_2065_ = v___y_2181_;
v___y_2066_ = v___y_2182_;
v___y_2067_ = v___y_2183_;
v___y_2068_ = v___y_2184_;
goto v___jp_2063_;
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_val_2196_);
lean_del_object(v___x_2192_);
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2247_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2197_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2197_);
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
lean_dec(v_a_2195_);
lean_del_object(v___x_2192_);
lean_dec(v_snd_2190_);
v_isEq_2064_ = v___x_1818_;
v___y_2065_ = v___y_2181_;
v___y_2066_ = v___y_2182_;
v___y_2067_ = v___y_2183_;
v___y_2068_ = v___y_2184_;
goto v___jp_2063_;
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_del_object(v___x_2192_);
lean_dec(v_snd_2190_);
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2255_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2194_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2194_);
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
}
else
{
lean_dec(v_a_2186_);
v_isEq_2064_ = v___x_1869_;
v___y_2065_ = v___y_2181_;
v___y_2066_ = v___y_2182_;
v___y_2067_ = v___y_2183_;
v___y_2068_ = v___y_2184_;
goto v___jp_2063_;
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_2264_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2185_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2185_);
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
lean_inc_ref(v___x_1909_);
v___x_2277_ = l_Lean_refutableHasNotBit_x3f(v___x_1909_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
if (lean_obj_tag(v_a_2278_) == 1)
{
lean_object* v_val_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec_ref(v_config_1807_);
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
lean_inc(v_mvarId_1808_);
v___x_2283_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v___x_2285_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2286_ = l_Lean_Meta_mkAbsurd(v_a_2284_, v_val_2279_, v___x_2285_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2287_, v___y_2274_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
lean_dec_ref_known(v___x_2288_, 1);
v___x_2289_ = lean_box(v___x_1818_);
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
lean_ctor_set(v___x_2292_, 1, v___x_1843_);
v_a_1825_ = v___x_2292_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_del_object(v___x_2281_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
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
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
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
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
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
lean_inc_ref(v___x_1909_);
v___x_2319_ = l_Lean_Meta_matchNe_x3f(v___x_1909_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
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
v___y_2181_ = v___y_2273_;
v___y_2182_ = v___y_2274_;
v___y_2183_ = v___y_2275_;
v___y_2184_ = v___y_2276_;
goto v___jp_2180_;
}
else
{
lean_object* v___x_2334_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec_ref(v_config_1807_);
lean_inc(v_mvarId_1808_);
v___x_2334_ = l_Lean_MVarId_getType(v_mvarId_1808_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
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
v___x_2338_ = l_Lean_LocalDecl_toExpr(v_val_1839_);
v___x_2339_ = l_Lean_Meta_mkAbsurd(v_a_2335_, v_a_2337_, v___x_2338_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1808_, v_a_2340_, v___y_2274_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_dec_ref_known(v___x_2341_, 1);
v___x_2342_ = lean_box(v___x_1818_);
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
lean_ctor_set(v___x_2329_, 1, v___x_1843_);
lean_ctor_set(v___x_2329_, 0, v___x_2344_);
v___x_2346_ = v___x_2329_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v___x_1843_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
v_a_1825_ = v___x_2346_;
goto v___jp_1824_;
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_del_object(v___x_2329_);
lean_del_object(v___x_2323_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
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
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
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
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
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
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
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
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
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
v___y_2181_ = v___y_2273_;
v___y_2182_ = v___y_2274_;
v___y_2183_ = v___y_2275_;
v___y_2184_ = v___y_2276_;
goto v___jp_2180_;
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
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
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
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
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_1833_ = v___x_1844_;
goto v___jp_1832_;
}
v___jp_1845_:
{
if (v___y_1850_ == 0)
{
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_1833_ = v___x_1844_;
goto v___jp_1832_;
}
else
{
lean_object* v_searchFuel_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_searchFuel_1851_ = lean_ctor_get(v_config_1807_, 0);
v___x_1852_ = l_Lean_LocalDecl_fvarId(v_val_1839_);
lean_dec(v_val_1839_);
lean_inc(v_searchFuel_1851_);
lean_inc(v_mvarId_1808_);
v___x_1853_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1808_, v___x_1852_, v_searchFuel_1851_, v___y_1849_, v___y_1847_, v___y_1846_, v___y_1848_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; uint8_t v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = lean_unbox(v_a_1854_);
lean_dec(v_a_1854_);
if (v___x_1855_ == 0)
{
lean_del_object(v___x_1841_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
v_a_1833_ = v___x_1844_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v___x_1856_ = lean_box(v___x_1818_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1856_);
v___x_1858_ = v___x_1841_;
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
lean_ctor_set(v___x_1859_, 1, v___x_1843_);
v_a_1825_ = v___x_1859_;
goto v___jp_1824_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_del_object(v___x_1841_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_1861_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1853_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1853_);
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
}
v___jp_1870_:
{
if (v___y_1876_ == 0)
{
v___y_1846_ = v___y_1871_;
v___y_1847_ = v___y_1872_;
v___y_1848_ = v___y_1874_;
v___y_1849_ = v___y_1875_;
v___y_1850_ = v___x_1869_;
goto v___jp_1845_;
}
else
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_bool_not(v___y_1873_);
v___y_1846_ = v___y_1871_;
v___y_1847_ = v___y_1872_;
v___y_1848_ = v___y_1874_;
v___y_1849_ = v___y_1875_;
v___y_1850_ = v___x_1877_;
goto v___jp_1845_;
}
}
v___jp_1878_:
{
uint8_t v_emptyType_1885_; 
v_emptyType_1885_ = lean_ctor_get_uint8(v_config_1807_, sizeof(void*)*1 + 1);
if (v_emptyType_1885_ == 0)
{
v___y_1871_ = v___y_1883_;
v___y_1872_ = v___y_1882_;
v___y_1873_ = v___y_1879_;
v___y_1874_ = v___y_1884_;
v___y_1875_ = v___y_1881_;
v___y_1876_ = v___x_1869_;
goto v___jp_1870_;
}
else
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_bool_not(v___y_1880_);
v___y_1871_ = v___y_1883_;
v___y_1872_ = v___y_1882_;
v___y_1873_ = v___y_1879_;
v___y_1874_ = v___y_1884_;
v___y_1875_ = v___y_1881_;
v___y_1876_ = v___x_1886_;
goto v___jp_1870_;
}
}
v___jp_1887_:
{
if (v___y_1894_ == 0)
{
v___y_1879_ = v___y_1889_;
v___y_1880_ = v___y_1890_;
v___y_1881_ = v___y_1888_;
v___y_1882_ = v___y_1892_;
v___y_1883_ = v___y_1891_;
v___y_1884_ = v___y_1893_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1895_; 
lean_inc(v_val_1839_);
lean_inc(v_mvarId_1808_);
v___x_1895_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1808_, v_val_1839_, v___y_1888_, v___y_1892_, v___y_1891_, v___y_1893_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; uint8_t v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = lean_unbox(v_a_1896_);
lean_dec(v_a_1896_);
if (v___x_1897_ == 0)
{
v___y_1879_ = v___y_1889_;
v___y_1880_ = v___y_1890_;
v___y_1881_ = v___y_1888_;
v___y_1882_ = v___y_1892_;
v___y_1883_ = v___y_1891_;
v___y_1884_ = v___y_1893_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v___x_1898_ = lean_box(v___x_1818_);
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1843_);
v_a_1825_ = v___x_1900_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
lean_del_object(v___x_1822_);
lean_dec(v_snd_1820_);
lean_dec(v_mvarId_1808_);
lean_dec_ref(v_config_1807_);
v_a_1901_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1895_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1895_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
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
lean_object* v_snd_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_3151_; 
v_snd_2500_ = lean_ctor_get(v_b_2492_, 1);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_b_2492_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_b_2492_, 0);
lean_dec(v_unused_3152_);
v___x_2502_ = v_b_2492_;
v_isShared_2503_ = v_isSharedCheck_3151_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_snd_2500_);
lean_dec(v_b_2492_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_3151_;
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
lean_object* v_val_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_3150_; 
v_val_2519_ = lean_ctor_get(v_a_2518_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_a_2518_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_2521_ = v_a_2518_;
v_isShared_2522_ = v_isSharedCheck_3150_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_val_2519_);
lean_dec(v_a_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_3150_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; uint8_t v___y_2530_; uint8_t v___x_2549_; uint8_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2556_; uint8_t v___y_2559_; uint8_t v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2568_; uint8_t v___y_2569_; uint8_t v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; uint8_t v___y_2574_; 
v___x_2523_ = lean_box(0);
v___x_2524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2549_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2519_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2589_; uint8_t v___y_2591_; uint8_t v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; uint8_t v___y_2603_; uint8_t v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; uint8_t v___y_2607_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; uint8_t v___y_2613_; uint8_t v___y_2614_; lean_object* v___y_2615_; lean_object* v_a_2616_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; uint8_t v___y_2623_; uint8_t v___y_2624_; lean_object* v___y_2625_; uint8_t v___y_2626_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; uint8_t v___y_2715_; uint8_t v___y_2716_; lean_object* v___y_2717_; uint8_t v___y_2718_; uint8_t v___y_2734_; uint8_t v_isHEq_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; uint8_t v_isEq_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___x_3087_; 
v___x_2589_ = l_Lean_LocalDecl_type(v_val_2519_);
lean_inc_ref(v___x_2589_);
v___x_3087_ = l_Lean_Meta_matchNot_x3f(v___x_2589_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
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
v___x_3090_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3089_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3090_, 1);
if (lean_obj_tag(v_a_3091_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec_ref(v_config_2487_);
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
lean_inc(v_mvarId_2488_);
v___x_3096_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3098_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_3099_ = l_Lean_mkFVar(v_val_3092_);
v___x_3100_ = l_Lean_Expr_app___override(v___x_3098_, v___x_3099_);
v___x_3101_ = l_Lean_Meta_mkFalseElim(v_a_3097_, v___x_3100_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v___x_3103_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_3102_, v___y_2494_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_dec_ref_known(v___x_3103_, 1);
v___x_3104_ = lean_box(v___x_2498_);
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
lean_ctor_set(v___x_3107_, 1, v___x_2523_);
v_a_2505_ = v___x_3107_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_del_object(v___x_3094_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
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
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
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
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
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
v___y_2953_ = v___y_2493_;
v___y_2954_ = v___y_2494_;
v___y_2955_ = v___y_2495_;
v___y_2956_ = v___y_2496_;
goto v___jp_2952_;
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
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
v___y_2953_ = v___y_2493_;
v___y_2954_ = v___y_2494_;
v___y_2955_ = v___y_2495_;
v___y_2956_ = v___y_2496_;
goto v___jp_2952_;
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
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
v___jp_2590_:
{
uint8_t v_genDiseq_2597_; 
v_genDiseq_2597_ = lean_ctor_get_uint8(v_config_2487_, sizeof(void*)*1 + 2);
if (v_genDiseq_2597_ == 0)
{
lean_dec_ref(v___x_2589_);
v___y_2568_ = v___y_2596_;
v___y_2569_ = v___y_2591_;
v___y_2570_ = v___y_2592_;
v___y_2571_ = v___y_2595_;
v___y_2572_ = v___y_2593_;
v___y_2573_ = v___y_2594_;
v___y_2574_ = v___x_2549_;
goto v___jp_2567_;
}
else
{
uint8_t v___x_2598_; 
v___x_2598_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2589_);
v___y_2568_ = v___y_2596_;
v___y_2569_ = v___y_2591_;
v___y_2570_ = v___y_2592_;
v___y_2571_ = v___y_2595_;
v___y_2572_ = v___y_2593_;
v___y_2573_ = v___y_2594_;
v___y_2574_ = v___x_2598_;
goto v___jp_2567_;
}
}
v___jp_2599_:
{
if (v___y_2607_ == 0)
{
lean_dec_ref(v___y_2605_);
v___y_2591_ = v___y_2603_;
v___y_2592_ = v___y_2604_;
v___y_2593_ = v___y_2602_;
v___y_2594_ = v___y_2601_;
v___y_2595_ = v___y_2600_;
v___y_2596_ = v___y_2606_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2608_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___y_2605_);
return v___x_2608_;
}
}
v___jp_2609_:
{
uint8_t v___x_2617_; 
v___x_2617_ = l_Lean_Exception_isInterrupt(v_a_2616_);
if (v___x_2617_ == 0)
{
uint8_t v___x_2618_; 
lean_inc_ref(v_a_2616_);
v___x_2618_ = l_Lean_Exception_isRuntime(v_a_2616_);
v___y_2600_ = v___y_2612_;
v___y_2601_ = v___y_2611_;
v___y_2602_ = v___y_2610_;
v___y_2603_ = v___y_2613_;
v___y_2604_ = v___y_2614_;
v___y_2605_ = v_a_2616_;
v___y_2606_ = v___y_2615_;
v___y_2607_ = v___x_2618_;
goto v___jp_2599_;
}
else
{
v___y_2600_ = v___y_2612_;
v___y_2601_ = v___y_2611_;
v___y_2602_ = v___y_2610_;
v___y_2603_ = v___y_2613_;
v___y_2604_ = v___y_2614_;
v___y_2605_ = v_a_2616_;
v___y_2606_ = v___y_2615_;
v___y_2607_ = v___x_2617_;
goto v___jp_2599_;
}
}
v___jp_2619_:
{
if (v___y_2626_ == 0)
{
v___y_2591_ = v___y_2623_;
v___y_2592_ = v___y_2624_;
v___y_2593_ = v___y_2622_;
v___y_2594_ = v___y_2621_;
v___y_2595_ = v___y_2620_;
v___y_2596_ = v___y_2625_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2627_; 
lean_inc_ref(v___x_2589_);
v___x_2627_ = l_Lean_Meta_mkDecide(v___x_2589_, v___y_2622_, v___y_2621_, v___y_2620_, v___y_2625_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; uint8_t v_foApprox_2630_; uint8_t v_ctxApprox_2631_; uint8_t v_quasiPatternApprox_2632_; uint8_t v_constApprox_2633_; uint8_t v_isDefEqStuckEx_2634_; uint8_t v_unificationHints_2635_; uint8_t v_proofIrrelevance_2636_; uint8_t v_assignSyntheticOpaque_2637_; uint8_t v_offsetCnstrs_2638_; uint8_t v_etaStruct_2639_; uint8_t v_univApprox_2640_; uint8_t v_iota_2641_; uint8_t v_beta_2642_; uint8_t v_proj_2643_; uint8_t v_zeta_2644_; uint8_t v_zetaDelta_2645_; uint8_t v_zetaUnused_2646_; uint8_t v_zetaHave_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2709_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = l_Lean_Meta_Context_config(v___y_2622_);
v_foApprox_2630_ = lean_ctor_get_uint8(v___x_2629_, 0);
v_ctxApprox_2631_ = lean_ctor_get_uint8(v___x_2629_, 1);
v_quasiPatternApprox_2632_ = lean_ctor_get_uint8(v___x_2629_, 2);
v_constApprox_2633_ = lean_ctor_get_uint8(v___x_2629_, 3);
v_isDefEqStuckEx_2634_ = lean_ctor_get_uint8(v___x_2629_, 4);
v_unificationHints_2635_ = lean_ctor_get_uint8(v___x_2629_, 5);
v_proofIrrelevance_2636_ = lean_ctor_get_uint8(v___x_2629_, 6);
v_assignSyntheticOpaque_2637_ = lean_ctor_get_uint8(v___x_2629_, 7);
v_offsetCnstrs_2638_ = lean_ctor_get_uint8(v___x_2629_, 8);
v_etaStruct_2639_ = lean_ctor_get_uint8(v___x_2629_, 10);
v_univApprox_2640_ = lean_ctor_get_uint8(v___x_2629_, 11);
v_iota_2641_ = lean_ctor_get_uint8(v___x_2629_, 12);
v_beta_2642_ = lean_ctor_get_uint8(v___x_2629_, 13);
v_proj_2643_ = lean_ctor_get_uint8(v___x_2629_, 14);
v_zeta_2644_ = lean_ctor_get_uint8(v___x_2629_, 15);
v_zetaDelta_2645_ = lean_ctor_get_uint8(v___x_2629_, 16);
v_zetaUnused_2646_ = lean_ctor_get_uint8(v___x_2629_, 17);
v_zetaHave_2647_ = lean_ctor_get_uint8(v___x_2629_, 18);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2649_ = v___x_2629_;
v_isShared_2650_ = v_isSharedCheck_2709_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v___x_2629_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2709_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
uint8_t v_trackZetaDelta_2651_; lean_object* v_zetaDeltaSet_2652_; lean_object* v_lctx_2653_; lean_object* v_localInstances_2654_; lean_object* v_defEqCtx_x3f_2655_; lean_object* v_synthPendingDepth_2656_; lean_object* v_canUnfold_x3f_2657_; uint8_t v_univApprox_2658_; uint8_t v_inTypeClassResolution_2659_; uint8_t v_cacheInferType_2660_; uint8_t v___x_2661_; lean_object* v_config_2663_; 
v_trackZetaDelta_2651_ = lean_ctor_get_uint8(v___y_2622_, sizeof(void*)*7);
v_zetaDeltaSet_2652_ = lean_ctor_get(v___y_2622_, 1);
v_lctx_2653_ = lean_ctor_get(v___y_2622_, 2);
v_localInstances_2654_ = lean_ctor_get(v___y_2622_, 3);
v_defEqCtx_x3f_2655_ = lean_ctor_get(v___y_2622_, 4);
v_synthPendingDepth_2656_ = lean_ctor_get(v___y_2622_, 5);
v_canUnfold_x3f_2657_ = lean_ctor_get(v___y_2622_, 6);
v_univApprox_2658_ = lean_ctor_get_uint8(v___y_2622_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2659_ = lean_ctor_get_uint8(v___y_2622_, sizeof(void*)*7 + 2);
v_cacheInferType_2660_ = lean_ctor_get_uint8(v___y_2622_, sizeof(void*)*7 + 3);
v___x_2661_ = 1;
if (v_isShared_2650_ == 0)
{
v_config_2663_ = v___x_2649_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 0, v_foApprox_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 1, v_ctxApprox_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 2, v_quasiPatternApprox_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 3, v_constApprox_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 4, v_isDefEqStuckEx_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 5, v_unificationHints_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 6, v_proofIrrelevance_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 7, v_assignSyntheticOpaque_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 8, v_offsetCnstrs_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 10, v_etaStruct_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 11, v_univApprox_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 12, v_iota_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 13, v_beta_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 14, v_proj_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 15, v_zeta_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 16, v_zetaDelta_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 17, v_zetaUnused_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2708_, 18, v_zetaHave_2647_);
v_config_2663_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
uint64_t v___x_2664_; uint64_t v___x_2665_; uint64_t v___x_2666_; uint64_t v___x_2667_; uint64_t v___x_2668_; uint64_t v_key_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_ctor_set_uint8(v_config_2663_, 9, v___x_2661_);
v___x_2664_ = l_Lean_Meta_Context_configKey(v___y_2622_);
v___x_2665_ = 3ULL;
v___x_2666_ = lean_uint64_shift_right(v___x_2664_, v___x_2665_);
v___x_2667_ = lean_uint64_shift_left(v___x_2666_, v___x_2665_);
v___x_2668_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_2669_ = lean_uint64_lor(v___x_2667_, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2670_, 0, v_config_2663_);
lean_ctor_set_uint64(v___x_2670_, sizeof(void*)*1, v_key_2669_);
lean_inc(v_canUnfold_x3f_2657_);
lean_inc(v_synthPendingDepth_2656_);
lean_inc(v_defEqCtx_x3f_2655_);
lean_inc_ref(v_localInstances_2654_);
lean_inc_ref(v_lctx_2653_);
lean_inc(v_zetaDeltaSet_2652_);
v___x_2671_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v_zetaDeltaSet_2652_);
lean_ctor_set(v___x_2671_, 2, v_lctx_2653_);
lean_ctor_set(v___x_2671_, 3, v_localInstances_2654_);
lean_ctor_set(v___x_2671_, 4, v_defEqCtx_x3f_2655_);
lean_ctor_set(v___x_2671_, 5, v_synthPendingDepth_2656_);
lean_ctor_set(v___x_2671_, 6, v_canUnfold_x3f_2657_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7, v_trackZetaDelta_2651_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 1, v_univApprox_2658_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2659_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 3, v_cacheInferType_2660_);
lean_inc(v___y_2625_);
lean_inc_ref(v___y_2620_);
lean_inc(v___y_2621_);
lean_inc(v_a_2628_);
v___x_2672_ = lean_whnf(v_a_2628_, v___x_2671_, v___y_2621_, v___y_2620_, v___y_2625_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_2675_ = l_Lean_Expr_isConstOf(v_a_2673_, v___x_2674_);
lean_dec(v_a_2673_);
if (v___x_2675_ == 0)
{
lean_dec(v_a_2628_);
v___y_2591_ = v___y_2623_;
v___y_2592_ = v___y_2624_;
v___y_2593_ = v___y_2622_;
v___y_2594_ = v___y_2621_;
v___y_2595_ = v___y_2620_;
v___y_2596_ = v___y_2625_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2676_; 
lean_inc(v_a_2628_);
v___x_2676_ = l_Lean_Meta_mkEqRefl(v_a_2628_, v___y_2622_, v___y_2621_, v___y_2620_, v___y_2625_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
lean_inc(v_mvarId_2488_);
v___x_2678_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2622_, v___y_2621_, v___y_2620_, v___y_2625_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v_nargs_2680_; lean_object* v___x_2681_; lean_object* v_dummy_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v_nargs_2680_ = l_Lean_Expr_getAppNumArgs(v_a_2628_);
v___x_2681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2682_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2680_);
v___x_2683_ = lean_mk_array(v_nargs_2680_, v_dummy_2682_);
v___x_2684_ = lean_unsigned_to_nat(1u);
v___x_2685_ = lean_nat_sub(v_nargs_2680_, v___x_2684_);
lean_dec(v_nargs_2680_);
v___x_2686_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2628_, v___x_2683_, v___x_2685_);
v___x_2687_ = lean_array_push(v___x_2686_, v_a_2677_);
v___x_2688_ = l_Lean_mkAppN(v___x_2681_, v___x_2687_);
lean_dec_ref(v___x_2687_);
lean_inc(v_val_2519_);
v___x_2689_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_2690_ = l_Lean_Meta_mkAbsurd(v_a_2679_, v___x_2689_, v___x_2688_, v___y_2622_, v___y_2621_, v___y_2620_, v___y_2625_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
lean_inc(v_mvarId_2488_);
v___x_2692_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_2691_, v___y_2621_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
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
v___x_2696_ = lean_box(v___x_2498_);
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
lean_ctor_set(v___x_2699_, 1, v___x_2523_);
v_a_2505_ = v___x_2699_;
goto v___jp_2504_;
}
}
}
else
{
lean_object* v_a_2703_; 
v_a_2703_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2692_, 1);
v___y_2610_ = v___y_2622_;
v___y_2611_ = v___y_2621_;
v___y_2612_ = v___y_2620_;
v___y_2613_ = v___y_2623_;
v___y_2614_ = v___y_2624_;
v___y_2615_ = v___y_2625_;
v_a_2616_ = v_a_2703_;
goto v___jp_2609_;
}
}
else
{
lean_object* v_a_2704_; 
v_a_2704_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2690_, 1);
v___y_2610_ = v___y_2622_;
v___y_2611_ = v___y_2621_;
v___y_2612_ = v___y_2620_;
v___y_2613_ = v___y_2623_;
v___y_2614_ = v___y_2624_;
v___y_2615_ = v___y_2625_;
v_a_2616_ = v_a_2704_;
goto v___jp_2609_;
}
}
else
{
lean_object* v_a_2705_; 
lean_dec(v_a_2677_);
lean_dec(v_a_2628_);
v_a_2705_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2678_, 1);
v___y_2610_ = v___y_2622_;
v___y_2611_ = v___y_2621_;
v___y_2612_ = v___y_2620_;
v___y_2613_ = v___y_2623_;
v___y_2614_ = v___y_2624_;
v___y_2615_ = v___y_2625_;
v_a_2616_ = v_a_2705_;
goto v___jp_2609_;
}
}
else
{
lean_object* v_a_2706_; 
lean_dec(v_a_2628_);
v_a_2706_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2676_, 1);
v___y_2610_ = v___y_2622_;
v___y_2611_ = v___y_2621_;
v___y_2612_ = v___y_2620_;
v___y_2613_ = v___y_2623_;
v___y_2614_ = v___y_2624_;
v___y_2615_ = v___y_2625_;
v_a_2616_ = v_a_2706_;
goto v___jp_2609_;
}
}
}
else
{
lean_object* v_a_2707_; 
lean_dec(v_a_2628_);
v_a_2707_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2672_, 1);
v___y_2610_ = v___y_2622_;
v___y_2611_ = v___y_2621_;
v___y_2612_ = v___y_2620_;
v___y_2613_ = v___y_2623_;
v___y_2614_ = v___y_2624_;
v___y_2615_ = v___y_2625_;
v_a_2616_ = v_a_2707_;
goto v___jp_2609_;
}
}
}
}
else
{
lean_object* v_a_2710_; 
v_a_2710_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2627_, 1);
v___y_2610_ = v___y_2622_;
v___y_2611_ = v___y_2621_;
v___y_2612_ = v___y_2620_;
v___y_2613_ = v___y_2623_;
v___y_2614_ = v___y_2624_;
v___y_2615_ = v___y_2625_;
v_a_2616_ = v_a_2710_;
goto v___jp_2609_;
}
}
}
v___jp_2711_:
{
if (v___y_2718_ == 0)
{
v___y_2591_ = v___y_2715_;
v___y_2592_ = v___y_2716_;
v___y_2593_ = v___y_2714_;
v___y_2594_ = v___y_2713_;
v___y_2595_ = v___y_2712_;
v___y_2596_ = v___y_2717_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2719_; 
lean_inc_ref(v___x_2589_);
v___x_2719_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2589_, v___y_2713_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; uint8_t v___x_2721_; uint8_t v___x_2722_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___x_2721_ = l_Lean_Expr_hasMVar(v_a_2720_);
v___x_2722_ = lean_bool_not(v___x_2721_);
if (v___x_2722_ == 0)
{
lean_dec(v_a_2720_);
v___y_2620_ = v___y_2712_;
v___y_2621_ = v___y_2713_;
v___y_2622_ = v___y_2714_;
v___y_2623_ = v___y_2715_;
v___y_2624_ = v___y_2716_;
v___y_2625_ = v___y_2717_;
v___y_2626_ = v___x_2549_;
goto v___jp_2619_;
}
else
{
uint8_t v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = l_Lean_Expr_hasFVar(v_a_2720_);
lean_dec(v_a_2720_);
v___x_2724_ = lean_bool_not(v___x_2723_);
v___y_2620_ = v___y_2712_;
v___y_2621_ = v___y_2713_;
v___y_2622_ = v___y_2714_;
v___y_2623_ = v___y_2715_;
v___y_2624_ = v___y_2716_;
v___y_2625_ = v___y_2717_;
v___y_2626_ = v___x_2724_;
goto v___jp_2619_;
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2725_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2719_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2719_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
v___jp_2733_:
{
uint8_t v_useDecide_2740_; 
v_useDecide_2740_ = lean_ctor_get_uint8(v_config_2487_, sizeof(void*)*1);
if (v_useDecide_2740_ == 0)
{
v___y_2712_ = v___y_2738_;
v___y_2713_ = v___y_2737_;
v___y_2714_ = v___y_2736_;
v___y_2715_ = v_isHEq_2735_;
v___y_2716_ = v___y_2734_;
v___y_2717_ = v___y_2739_;
v___y_2718_ = v___x_2549_;
goto v___jp_2711_;
}
else
{
uint8_t v___x_2741_; uint8_t v___x_2742_; 
v___x_2741_ = l_Lean_Expr_hasFVar(v___x_2589_);
v___x_2742_ = lean_bool_not(v___x_2741_);
v___y_2712_ = v___y_2738_;
v___y_2713_ = v___y_2737_;
v___y_2714_ = v___y_2736_;
v___y_2715_ = v_isHEq_2735_;
v___y_2716_ = v___y_2734_;
v___y_2717_ = v___y_2739_;
v___y_2718_ = v___x_2742_;
goto v___jp_2711_;
}
}
v___jp_2743_:
{
lean_object* v___x_2749_; 
lean_inc_ref(v___x_2589_);
v___x_2749_ = l_Lean_Meta_matchHEq_x3f(v___x_2589_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
if (lean_obj_tag(v_a_2750_) == 1)
{
lean_object* v_val_2751_; lean_object* v_snd_2752_; lean_object* v_snd_2753_; lean_object* v_fst_2754_; lean_object* v_fst_2755_; lean_object* v_fst_2756_; lean_object* v_snd_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2851_; 
v_val_2751_ = lean_ctor_get(v_a_2750_, 0);
lean_inc(v_val_2751_);
lean_dec_ref_known(v_a_2750_, 1);
v_snd_2752_ = lean_ctor_get(v_val_2751_, 1);
lean_inc(v_snd_2752_);
v_snd_2753_ = lean_ctor_get(v_snd_2752_, 1);
lean_inc(v_snd_2753_);
v_fst_2754_ = lean_ctor_get(v_val_2751_, 0);
lean_inc(v_fst_2754_);
lean_dec(v_val_2751_);
v_fst_2755_ = lean_ctor_get(v_snd_2752_, 0);
lean_inc(v_fst_2755_);
lean_dec(v_snd_2752_);
v_fst_2756_ = lean_ctor_get(v_snd_2753_, 0);
v_snd_2757_ = lean_ctor_get(v_snd_2753_, 1);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_snd_2753_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2759_ = v_snd_2753_;
v_isShared_2760_ = v_isSharedCheck_2851_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_snd_2757_);
lean_inc(v_fst_2756_);
lean_dec(v_snd_2753_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2851_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2755_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
if (lean_obj_tag(v_a_2762_) == 1)
{
lean_object* v_val_2763_; lean_object* v___x_2764_; 
v_val_2763_ = lean_ctor_get(v_a_2762_, 0);
lean_inc(v_val_2763_);
lean_dec_ref_known(v_a_2762_, 1);
v___x_2764_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2757_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
if (lean_obj_tag(v_a_2765_) == 1)
{
lean_object* v_toConstantVal_2766_; lean_object* v_val_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2834_; 
v_toConstantVal_2766_ = lean_ctor_get(v_val_2763_, 0);
lean_inc_ref(v_toConstantVal_2766_);
lean_dec(v_val_2763_);
v_val_2767_ = lean_ctor_get(v_a_2765_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_a_2765_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2769_ = v_a_2765_;
v_isShared_2770_ = v_isSharedCheck_2834_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_val_2767_);
lean_dec(v_a_2765_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2834_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v_toConstantVal_2771_; lean_object* v_name_2772_; lean_object* v_name_2773_; uint8_t v___x_2774_; uint8_t v___x_2775_; 
v_toConstantVal_2771_ = lean_ctor_get(v_val_2767_, 0);
lean_inc_ref(v_toConstantVal_2771_);
lean_dec(v_val_2767_);
v_name_2772_ = lean_ctor_get(v_toConstantVal_2766_, 0);
lean_inc(v_name_2772_);
lean_dec_ref(v_toConstantVal_2766_);
v_name_2773_ = lean_ctor_get(v_toConstantVal_2771_, 0);
lean_inc(v_name_2773_);
lean_dec_ref(v_toConstantVal_2771_);
v___x_2774_ = lean_name_eq(v_name_2772_, v_name_2773_);
lean_dec(v_name_2773_);
lean_dec(v_name_2772_);
v___x_2775_ = lean_bool_not(v___x_2774_);
if (v___x_2775_ == 0)
{
lean_del_object(v___x_2769_);
lean_del_object(v___x_2759_);
lean_dec(v_fst_2756_);
lean_dec(v_fst_2754_);
v___y_2734_ = v_isEq_2744_;
v_isHEq_2735_ = v___x_2498_;
v___y_2736_ = v___y_2745_;
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2748_;
goto v___jp_2733_;
}
else
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Meta_isExprDefEq(v_fst_2754_, v_fst_2756_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; uint8_t v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = lean_unbox(v_a_2777_);
lean_dec(v_a_2777_);
if (v___x_2778_ == 0)
{
lean_del_object(v___x_2769_);
lean_del_object(v___x_2759_);
v___y_2734_ = v_isEq_2744_;
v_isHEq_2735_ = v___x_2498_;
v___y_2736_ = v___y_2745_;
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2748_;
goto v___jp_2733_;
}
else
{
lean_object* v___x_2779_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec_ref(v_config_2487_);
lean_inc(v_mvarId_2488_);
v___x_2779_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2781_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_2782_ = l_Lean_Meta_mkEqOfHEq(v___x_2781_, v___x_2498_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = l_Lean_Meta_mkNoConfusion(v_a_2780_, v_a_2783_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2786_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2786_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_2785_, v___y_2746_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
lean_dec_ref_known(v___x_2786_, 1);
v___x_2787_ = lean_box(v___x_2498_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2787_);
v___x_2789_ = v___x_2769_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2791_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v___x_2523_);
lean_ctor_set(v___x_2759_, 0, v___x_2789_);
v___x_2791_ = v___x_2759_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v___x_2523_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
v_a_2505_ = v___x_2791_;
goto v___jp_2504_;
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_del_object(v___x_2769_);
lean_del_object(v___x_2759_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2794_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2786_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2786_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_del_object(v___x_2769_);
lean_del_object(v___x_2759_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2802_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2784_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2784_);
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
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2780_);
lean_del_object(v___x_2769_);
lean_del_object(v___x_2759_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2810_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2782_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2782_);
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
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_del_object(v___x_2769_);
lean_del_object(v___x_2759_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
v_a_2818_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2779_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2779_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_del_object(v___x_2769_);
lean_del_object(v___x_2759_);
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2826_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2776_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2776_);
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
}
}
else
{
lean_dec(v_a_2765_);
lean_dec(v_val_2763_);
lean_del_object(v___x_2759_);
lean_dec(v_fst_2756_);
lean_dec(v_fst_2754_);
v___y_2734_ = v_isEq_2744_;
v_isHEq_2735_ = v___x_2498_;
v___y_2736_ = v___y_2745_;
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2748_;
goto v___jp_2733_;
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_val_2763_);
lean_del_object(v___x_2759_);
lean_dec(v_fst_2756_);
lean_dec(v_fst_2754_);
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2835_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2764_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2764_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_dec(v_a_2762_);
lean_del_object(v___x_2759_);
lean_dec(v_snd_2757_);
lean_dec(v_fst_2756_);
lean_dec(v_fst_2754_);
v___y_2734_ = v_isEq_2744_;
v_isHEq_2735_ = v___x_2498_;
v___y_2736_ = v___y_2745_;
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2748_;
goto v___jp_2733_;
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_del_object(v___x_2759_);
lean_dec(v_snd_2757_);
lean_dec(v_fst_2756_);
lean_dec(v_fst_2754_);
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2843_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2761_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2761_);
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
}
else
{
lean_dec(v_a_2750_);
v___y_2734_ = v_isEq_2744_;
v_isHEq_2735_ = v___x_2549_;
v___y_2736_ = v___y_2745_;
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2748_;
goto v___jp_2733_;
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2852_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2749_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2749_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
v___jp_2860_:
{
lean_object* v___x_2865_; 
lean_inc_ref(v___x_2589_);
v___x_2865_ = l_Lean_Meta_matchEq_x3f(v___x_2589_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
if (lean_obj_tag(v_a_2866_) == 1)
{
lean_object* v_val_2867_; lean_object* v_snd_2868_; lean_object* v_fst_2869_; lean_object* v_snd_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2943_; 
v_val_2867_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v_a_2866_, 1);
v_snd_2868_ = lean_ctor_get(v_val_2867_, 1);
lean_inc(v_snd_2868_);
lean_dec(v_val_2867_);
v_fst_2869_ = lean_ctor_get(v_snd_2868_, 0);
v_snd_2870_ = lean_ctor_get(v_snd_2868_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_snd_2868_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2872_ = v_snd_2868_;
v_isShared_2873_ = v_isSharedCheck_2943_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_snd_2870_);
lean_inc(v_fst_2869_);
lean_dec(v_snd_2868_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2943_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2869_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
if (lean_obj_tag(v_a_2875_) == 1)
{
lean_object* v_val_2876_; lean_object* v___x_2877_; 
v_val_2876_ = lean_ctor_get(v_a_2875_, 0);
lean_inc(v_val_2876_);
lean_dec_ref_known(v_a_2875_, 1);
v___x_2877_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2870_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
if (lean_obj_tag(v_a_2878_) == 1)
{
lean_object* v_toConstantVal_2879_; lean_object* v_val_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2926_; 
v_toConstantVal_2879_ = lean_ctor_get(v_val_2876_, 0);
lean_inc_ref(v_toConstantVal_2879_);
lean_dec(v_val_2876_);
v_val_2880_ = lean_ctor_get(v_a_2878_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2878_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2882_ = v_a_2878_;
v_isShared_2883_ = v_isSharedCheck_2926_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_val_2880_);
lean_dec(v_a_2878_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2926_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v_toConstantVal_2884_; lean_object* v_name_2885_; lean_object* v_name_2886_; uint8_t v___x_2887_; uint8_t v___x_2888_; 
v_toConstantVal_2884_ = lean_ctor_get(v_val_2880_, 0);
lean_inc_ref(v_toConstantVal_2884_);
lean_dec(v_val_2880_);
v_name_2885_ = lean_ctor_get(v_toConstantVal_2879_, 0);
lean_inc(v_name_2885_);
lean_dec_ref(v_toConstantVal_2879_);
v_name_2886_ = lean_ctor_get(v_toConstantVal_2884_, 0);
lean_inc(v_name_2886_);
lean_dec_ref(v_toConstantVal_2884_);
v___x_2887_ = lean_name_eq(v_name_2885_, v_name_2886_);
lean_dec(v_name_2886_);
lean_dec(v_name_2885_);
v___x_2888_ = lean_bool_not(v___x_2887_);
if (v___x_2888_ == 0)
{
lean_del_object(v___x_2882_);
lean_del_object(v___x_2872_);
v_isEq_2744_ = v___x_2498_;
v___y_2745_ = v___y_2861_;
v___y_2746_ = v___y_2862_;
v___y_2747_ = v___y_2863_;
v___y_2748_ = v___y_2864_;
goto v___jp_2743_;
}
else
{
lean_object* v___x_2889_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec_ref(v_config_2487_);
lean_inc(v_mvarId_2488_);
v___x_2889_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_2892_ = l_Lean_Meta_mkNoConfusion(v_a_2890_, v___x_2891_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_2893_, v___y_2862_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
lean_dec_ref_known(v___x_2894_, 1);
v___x_2895_ = lean_box(v___x_2498_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2895_);
v___x_2897_ = v___x_2882_;
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
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 1, v___x_2523_);
lean_ctor_set(v___x_2872_, 0, v___x_2897_);
v___x_2899_ = v___x_2872_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2523_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
v_a_2505_ = v___x_2899_;
goto v___jp_2504_;
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_del_object(v___x_2882_);
lean_del_object(v___x_2872_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
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
lean_del_object(v___x_2882_);
lean_del_object(v___x_2872_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
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
lean_del_object(v___x_2882_);
lean_del_object(v___x_2872_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
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
}
}
else
{
lean_dec(v_a_2878_);
lean_dec(v_val_2876_);
lean_del_object(v___x_2872_);
v_isEq_2744_ = v___x_2498_;
v___y_2745_ = v___y_2861_;
v___y_2746_ = v___y_2862_;
v___y_2747_ = v___y_2863_;
v___y_2748_ = v___y_2864_;
goto v___jp_2743_;
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v_val_2876_);
lean_del_object(v___x_2872_);
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2927_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2877_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2877_);
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
lean_dec(v_a_2875_);
lean_del_object(v___x_2872_);
lean_dec(v_snd_2870_);
v_isEq_2744_ = v___x_2498_;
v___y_2745_ = v___y_2861_;
v___y_2746_ = v___y_2862_;
v___y_2747_ = v___y_2863_;
v___y_2748_ = v___y_2864_;
goto v___jp_2743_;
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_del_object(v___x_2872_);
lean_dec(v_snd_2870_);
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2935_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2874_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2874_);
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
lean_dec(v_a_2866_);
v_isEq_2744_ = v___x_2549_;
v___y_2745_ = v___y_2861_;
v___y_2746_ = v___y_2862_;
v___y_2747_ = v___y_2863_;
v___y_2748_ = v___y_2864_;
goto v___jp_2743_;
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2944_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2865_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2865_);
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
lean_inc_ref(v___x_2589_);
v___x_2957_ = l_Lean_refutableHasNotBit_x3f(v___x_2589_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
if (lean_obj_tag(v_a_2958_) == 1)
{
lean_object* v_val_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec_ref(v_config_2487_);
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
lean_inc(v_mvarId_2488_);
v___x_2963_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_2966_ = l_Lean_Meta_mkAbsurd(v_a_2964_, v_val_2959_, v___x_2965_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2968_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_2967_, v___y_2954_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
lean_dec_ref_known(v___x_2968_, 1);
v___x_2969_ = lean_box(v___x_2498_);
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
lean_ctor_set(v___x_2972_, 1, v___x_2523_);
v_a_2505_ = v___x_2972_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_del_object(v___x_2961_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
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
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
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
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
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
lean_inc_ref(v___x_2589_);
v___x_2999_ = l_Lean_Meta_matchNe_x3f(v___x_2589_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
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
v___y_2861_ = v___y_2953_;
v___y_2862_ = v___y_2954_;
v___y_2863_ = v___y_2955_;
v___y_2864_ = v___y_2956_;
goto v___jp_2860_;
}
else
{
lean_object* v___x_3014_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec_ref(v_config_2487_);
lean_inc(v_mvarId_2488_);
v___x_3014_ = l_Lean_MVarId_getType(v_mvarId_2488_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
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
v___x_3018_ = l_Lean_LocalDecl_toExpr(v_val_2519_);
v___x_3019_ = l_Lean_Meta_mkAbsurd(v_a_3015_, v_a_3017_, v___x_3018_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2488_, v_a_3020_, v___y_2954_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_dec_ref_known(v___x_3021_, 1);
v___x_3022_ = lean_box(v___x_2498_);
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
lean_ctor_set(v___x_3009_, 1, v___x_2523_);
lean_ctor_set(v___x_3009_, 0, v___x_3024_);
v___x_3026_ = v___x_3009_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_2523_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
v_a_2505_ = v___x_3026_;
goto v___jp_2504_;
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_del_object(v___x_3009_);
lean_del_object(v___x_3003_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
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
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
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
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
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
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
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
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
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
v___y_2861_ = v___y_2953_;
v___y_2862_ = v___y_2954_;
v___y_2863_ = v___y_2955_;
v___y_2864_ = v___y_2956_;
goto v___jp_2860_;
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
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
lean_dec_ref(v___x_2589_);
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
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
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2513_ = v___x_2524_;
goto v___jp_2512_;
}
v___jp_2525_:
{
if (v___y_2530_ == 0)
{
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2513_ = v___x_2524_;
goto v___jp_2512_;
}
else
{
lean_object* v_searchFuel_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_searchFuel_2531_ = lean_ctor_get(v_config_2487_, 0);
v___x_2532_ = l_Lean_LocalDecl_fvarId(v_val_2519_);
lean_dec(v_val_2519_);
lean_inc(v_searchFuel_2531_);
lean_inc(v_mvarId_2488_);
v___x_2533_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2488_, v___x_2532_, v_searchFuel_2531_, v___y_2529_, v___y_2526_, v___y_2528_, v___y_2527_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; uint8_t v___x_2535_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = lean_unbox(v_a_2534_);
lean_dec(v_a_2534_);
if (v___x_2535_ == 0)
{
lean_del_object(v___x_2521_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
v_a_2513_ = v___x_2524_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v___x_2536_ = lean_box(v___x_2498_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2536_);
v___x_2538_ = v___x_2521_;
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
lean_ctor_set(v___x_2539_, 1, v___x_2523_);
v_a_2505_ = v___x_2539_;
goto v___jp_2504_;
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_del_object(v___x_2521_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2541_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2533_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2533_);
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
}
v___jp_2550_:
{
if (v___y_2556_ == 0)
{
v___y_2526_ = v___y_2552_;
v___y_2527_ = v___y_2554_;
v___y_2528_ = v___y_2553_;
v___y_2529_ = v___y_2555_;
v___y_2530_ = v___x_2549_;
goto v___jp_2525_;
}
else
{
uint8_t v___x_2557_; 
v___x_2557_ = lean_bool_not(v___y_2551_);
v___y_2526_ = v___y_2552_;
v___y_2527_ = v___y_2554_;
v___y_2528_ = v___y_2553_;
v___y_2529_ = v___y_2555_;
v___y_2530_ = v___x_2557_;
goto v___jp_2525_;
}
}
v___jp_2558_:
{
uint8_t v_emptyType_2565_; 
v_emptyType_2565_ = lean_ctor_get_uint8(v_config_2487_, sizeof(void*)*1 + 1);
if (v_emptyType_2565_ == 0)
{
v___y_2551_ = v___y_2559_;
v___y_2552_ = v___y_2562_;
v___y_2553_ = v___y_2563_;
v___y_2554_ = v___y_2564_;
v___y_2555_ = v___y_2561_;
v___y_2556_ = v___x_2549_;
goto v___jp_2550_;
}
else
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_bool_not(v___y_2560_);
v___y_2551_ = v___y_2559_;
v___y_2552_ = v___y_2562_;
v___y_2553_ = v___y_2563_;
v___y_2554_ = v___y_2564_;
v___y_2555_ = v___y_2561_;
v___y_2556_ = v___x_2566_;
goto v___jp_2550_;
}
}
v___jp_2567_:
{
if (v___y_2574_ == 0)
{
v___y_2559_ = v___y_2569_;
v___y_2560_ = v___y_2570_;
v___y_2561_ = v___y_2572_;
v___y_2562_ = v___y_2573_;
v___y_2563_ = v___y_2571_;
v___y_2564_ = v___y_2568_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2575_; 
lean_inc(v_val_2519_);
lean_inc(v_mvarId_2488_);
v___x_2575_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2488_, v_val_2519_, v___y_2572_, v___y_2573_, v___y_2571_, v___y_2568_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; uint8_t v___x_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = lean_unbox(v_a_2576_);
lean_dec(v_a_2576_);
if (v___x_2577_ == 0)
{
v___y_2559_ = v___y_2569_;
v___y_2560_ = v___y_2570_;
v___y_2561_ = v___y_2572_;
v___y_2562_ = v___y_2573_;
v___y_2563_ = v___y_2571_;
v___y_2564_ = v___y_2568_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v___x_2578_ = lean_box(v___x_2498_);
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2523_);
v_a_2505_ = v___x_2580_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_del_object(v___x_2521_);
lean_dec(v_val_2519_);
lean_del_object(v___x_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_mvarId_2488_);
lean_dec_ref(v_config_2487_);
v_a_2581_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2575_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2575_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
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
lean_object* v_snd_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3866_; 
v_snd_3183_ = lean_ctor_get(v_b_3175_, 1);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_b_3175_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; 
v_unused_3867_ = lean_ctor_get(v_b_3175_, 0);
lean_dec(v_unused_3867_);
v___x_3185_ = v_b_3175_;
v_isShared_3186_ = v_isSharedCheck_3866_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_snd_3183_);
lean_dec(v_b_3175_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3866_;
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
lean_object* v_val_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3865_; 
v_val_3202_ = lean_ctor_get(v_a_3201_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_a_3201_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3204_ = v_a_3201_;
v_isShared_3205_ = v_isSharedCheck_3865_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_val_3202_);
lean_dec(v_a_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3865_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; uint8_t v___y_3213_; uint8_t v___x_3233_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; uint8_t v___y_3239_; uint8_t v___y_3240_; uint8_t v___y_3243_; uint8_t v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3252_; lean_object* v___y_3253_; uint8_t v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; uint8_t v___y_3258_; 
v___x_3206_ = lean_box(0);
v___x_3207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3233_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3202_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3274_; uint8_t v___y_3276_; uint8_t v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3285_; uint8_t v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; uint8_t v___y_3290_; lean_object* v___y_3291_; uint8_t v___y_3292_; uint8_t v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; uint8_t v___y_3299_; lean_object* v___y_3300_; lean_object* v_a_3301_; uint8_t v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; uint8_t v___y_3309_; lean_object* v___y_3310_; uint8_t v___y_3311_; uint8_t v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; uint8_t v___y_3408_; lean_object* v___y_3409_; uint8_t v___y_3410_; uint8_t v___y_3426_; uint8_t v_isHEq_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; uint8_t v_isEq_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___x_3795_; 
v___x_3274_ = l_Lean_LocalDecl_type(v_val_3202_);
lean_inc_ref(v___x_3274_);
v___x_3795_ = l_Lean_Meta_matchNot_x3f(v___x_3274_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
if (lean_obj_tag(v_a_3796_) == 1)
{
lean_object* v_val_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3856_; 
v_val_3797_ = lean_ctor_get(v_a_3796_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_a_3796_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3799_ = v_a_3796_;
v_isShared_3800_ = v_isSharedCheck_3856_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_val_3797_);
lean_dec(v_a_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3856_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3797_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
if (lean_obj_tag(v_a_3802_) == 1)
{
lean_object* v_val_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3847_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
v_val_3803_ = lean_ctor_get(v_a_3802_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_a_3802_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3805_ = v_a_3802_;
v_isShared_3806_ = v_isSharedCheck_3847_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_val_3803_);
lean_dec(v_a_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3847_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; 
lean_inc(v_mvarId_3171_);
v___x_3807_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
lean_dec_ref_known(v___x_3807_, 1);
v___x_3809_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3810_ = l_Lean_mkFVar(v_val_3803_);
v___x_3811_ = l_Lean_Expr_app___override(v___x_3809_, v___x_3810_);
v___x_3812_ = l_Lean_Meta_mkFalseElim(v_a_3808_, v___x_3811_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3814_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3812_, 1);
v___x_3814_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3813_, v___y_3177_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v___x_3815_; lean_object* v___x_3817_; 
lean_dec_ref_known(v___x_3814_, 1);
v___x_3815_ = lean_box(v___x_3181_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3815_);
v___x_3817_ = v___x_3805_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; lean_object* v___x_3820_; 
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
lean_ctor_set(v___x_3818_, 1, v___x_3206_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set_tag(v___x_3799_, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3818_);
v___x_3820_ = v___x_3799_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
v_a_3188_ = v___x_3820_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_del_object(v___x_3805_);
lean_del_object(v___x_3799_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3823_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3814_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3814_);
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
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_del_object(v___x_3805_);
lean_del_object(v___x_3799_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3831_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3812_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3812_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_del_object(v___x_3805_);
lean_dec(v_val_3803_);
lean_del_object(v___x_3799_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3839_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3807_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3807_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
else
{
lean_dec(v_a_3802_);
lean_del_object(v___x_3799_);
v___y_3659_ = v___y_3176_;
v___y_3660_ = v___y_3177_;
v___y_3661_ = v___y_3178_;
v___y_3662_ = v___y_3179_;
goto v___jp_3658_;
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_del_object(v___x_3799_);
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3848_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3801_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3801_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
}
else
{
lean_dec(v_a_3796_);
v___y_3659_ = v___y_3176_;
v___y_3660_ = v___y_3177_;
v___y_3661_ = v___y_3178_;
v___y_3662_ = v___y_3179_;
goto v___jp_3658_;
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3857_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3795_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3795_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
v___jp_3275_:
{
uint8_t v_genDiseq_3282_; 
v_genDiseq_3282_ = lean_ctor_get_uint8(v_config_3170_, sizeof(void*)*1 + 2);
if (v_genDiseq_3282_ == 0)
{
lean_dec_ref(v___x_3274_);
v___y_3252_ = v___y_3279_;
v___y_3253_ = v___y_3280_;
v___y_3254_ = v___y_3276_;
v___y_3255_ = v___y_3278_;
v___y_3256_ = v___y_3281_;
v___y_3257_ = v___y_3277_;
v___y_3258_ = v___x_3233_;
goto v___jp_3251_;
}
else
{
uint8_t v___x_3283_; 
v___x_3283_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3274_);
v___y_3252_ = v___y_3279_;
v___y_3253_ = v___y_3280_;
v___y_3254_ = v___y_3276_;
v___y_3255_ = v___y_3278_;
v___y_3256_ = v___y_3281_;
v___y_3257_ = v___y_3277_;
v___y_3258_ = v___x_3283_;
goto v___jp_3251_;
}
}
v___jp_3284_:
{
if (v___y_3292_ == 0)
{
lean_dec_ref(v___y_3285_);
v___y_3276_ = v___y_3286_;
v___y_3277_ = v___y_3290_;
v___y_3278_ = v___y_3287_;
v___y_3279_ = v___y_3289_;
v___y_3280_ = v___y_3291_;
v___y_3281_ = v___y_3288_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3293_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___y_3285_);
return v___x_3293_;
}
}
v___jp_3294_:
{
uint8_t v___x_3302_; 
v___x_3302_ = l_Lean_Exception_isInterrupt(v_a_3301_);
if (v___x_3302_ == 0)
{
uint8_t v___x_3303_; 
lean_inc_ref(v_a_3301_);
v___x_3303_ = l_Lean_Exception_isRuntime(v_a_3301_);
v___y_3285_ = v_a_3301_;
v___y_3286_ = v___y_3295_;
v___y_3287_ = v___y_3296_;
v___y_3288_ = v___y_3298_;
v___y_3289_ = v___y_3297_;
v___y_3290_ = v___y_3299_;
v___y_3291_ = v___y_3300_;
v___y_3292_ = v___x_3303_;
goto v___jp_3284_;
}
else
{
v___y_3285_ = v_a_3301_;
v___y_3286_ = v___y_3295_;
v___y_3287_ = v___y_3296_;
v___y_3288_ = v___y_3298_;
v___y_3289_ = v___y_3297_;
v___y_3290_ = v___y_3299_;
v___y_3291_ = v___y_3300_;
v___y_3292_ = v___x_3302_;
goto v___jp_3284_;
}
}
v___jp_3304_:
{
if (v___y_3311_ == 0)
{
v___y_3276_ = v___y_3305_;
v___y_3277_ = v___y_3309_;
v___y_3278_ = v___y_3306_;
v___y_3279_ = v___y_3308_;
v___y_3280_ = v___y_3310_;
v___y_3281_ = v___y_3307_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3312_; 
lean_inc_ref(v___x_3274_);
v___x_3312_ = l_Lean_Meta_mkDecide(v___x_3274_, v___y_3306_, v___y_3308_, v___y_3310_, v___y_3307_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3314_; uint8_t v_foApprox_3315_; uint8_t v_ctxApprox_3316_; uint8_t v_quasiPatternApprox_3317_; uint8_t v_constApprox_3318_; uint8_t v_isDefEqStuckEx_3319_; uint8_t v_unificationHints_3320_; uint8_t v_proofIrrelevance_3321_; uint8_t v_assignSyntheticOpaque_3322_; uint8_t v_offsetCnstrs_3323_; uint8_t v_etaStruct_3324_; uint8_t v_univApprox_3325_; uint8_t v_iota_3326_; uint8_t v_beta_3327_; uint8_t v_proj_3328_; uint8_t v_zeta_3329_; uint8_t v_zetaDelta_3330_; uint8_t v_zetaUnused_3331_; uint8_t v_zetaHave_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3401_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3312_, 1);
v___x_3314_ = l_Lean_Meta_Context_config(v___y_3306_);
v_foApprox_3315_ = lean_ctor_get_uint8(v___x_3314_, 0);
v_ctxApprox_3316_ = lean_ctor_get_uint8(v___x_3314_, 1);
v_quasiPatternApprox_3317_ = lean_ctor_get_uint8(v___x_3314_, 2);
v_constApprox_3318_ = lean_ctor_get_uint8(v___x_3314_, 3);
v_isDefEqStuckEx_3319_ = lean_ctor_get_uint8(v___x_3314_, 4);
v_unificationHints_3320_ = lean_ctor_get_uint8(v___x_3314_, 5);
v_proofIrrelevance_3321_ = lean_ctor_get_uint8(v___x_3314_, 6);
v_assignSyntheticOpaque_3322_ = lean_ctor_get_uint8(v___x_3314_, 7);
v_offsetCnstrs_3323_ = lean_ctor_get_uint8(v___x_3314_, 8);
v_etaStruct_3324_ = lean_ctor_get_uint8(v___x_3314_, 10);
v_univApprox_3325_ = lean_ctor_get_uint8(v___x_3314_, 11);
v_iota_3326_ = lean_ctor_get_uint8(v___x_3314_, 12);
v_beta_3327_ = lean_ctor_get_uint8(v___x_3314_, 13);
v_proj_3328_ = lean_ctor_get_uint8(v___x_3314_, 14);
v_zeta_3329_ = lean_ctor_get_uint8(v___x_3314_, 15);
v_zetaDelta_3330_ = lean_ctor_get_uint8(v___x_3314_, 16);
v_zetaUnused_3331_ = lean_ctor_get_uint8(v___x_3314_, 17);
v_zetaHave_3332_ = lean_ctor_get_uint8(v___x_3314_, 18);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3334_ = v___x_3314_;
v_isShared_3335_ = v_isSharedCheck_3401_;
goto v_resetjp_3333_;
}
else
{
lean_dec(v___x_3314_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3401_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
uint8_t v_trackZetaDelta_3336_; lean_object* v_zetaDeltaSet_3337_; lean_object* v_lctx_3338_; lean_object* v_localInstances_3339_; lean_object* v_defEqCtx_x3f_3340_; lean_object* v_synthPendingDepth_3341_; lean_object* v_canUnfold_x3f_3342_; uint8_t v_univApprox_3343_; uint8_t v_inTypeClassResolution_3344_; uint8_t v_cacheInferType_3345_; uint8_t v___x_3346_; lean_object* v_config_3348_; 
v_trackZetaDelta_3336_ = lean_ctor_get_uint8(v___y_3306_, sizeof(void*)*7);
v_zetaDeltaSet_3337_ = lean_ctor_get(v___y_3306_, 1);
v_lctx_3338_ = lean_ctor_get(v___y_3306_, 2);
v_localInstances_3339_ = lean_ctor_get(v___y_3306_, 3);
v_defEqCtx_x3f_3340_ = lean_ctor_get(v___y_3306_, 4);
v_synthPendingDepth_3341_ = lean_ctor_get(v___y_3306_, 5);
v_canUnfold_x3f_3342_ = lean_ctor_get(v___y_3306_, 6);
v_univApprox_3343_ = lean_ctor_get_uint8(v___y_3306_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3344_ = lean_ctor_get_uint8(v___y_3306_, sizeof(void*)*7 + 2);
v_cacheInferType_3345_ = lean_ctor_get_uint8(v___y_3306_, sizeof(void*)*7 + 3);
v___x_3346_ = 1;
if (v_isShared_3335_ == 0)
{
v_config_3348_ = v___x_3334_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 0, v_foApprox_3315_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 1, v_ctxApprox_3316_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 2, v_quasiPatternApprox_3317_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 3, v_constApprox_3318_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 4, v_isDefEqStuckEx_3319_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 5, v_unificationHints_3320_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 6, v_proofIrrelevance_3321_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 7, v_assignSyntheticOpaque_3322_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 8, v_offsetCnstrs_3323_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 10, v_etaStruct_3324_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 11, v_univApprox_3325_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 12, v_iota_3326_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 13, v_beta_3327_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 14, v_proj_3328_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 15, v_zeta_3329_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 16, v_zetaDelta_3330_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 17, v_zetaUnused_3331_);
lean_ctor_set_uint8(v_reuseFailAlloc_3400_, 18, v_zetaHave_3332_);
v_config_3348_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
uint64_t v___x_3349_; uint64_t v___x_3350_; uint64_t v___x_3351_; uint64_t v___x_3352_; uint64_t v___x_3353_; uint64_t v_key_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_ctor_set_uint8(v_config_3348_, 9, v___x_3346_);
v___x_3349_ = l_Lean_Meta_Context_configKey(v___y_3306_);
v___x_3350_ = 3ULL;
v___x_3351_ = lean_uint64_shift_right(v___x_3349_, v___x_3350_);
v___x_3352_ = lean_uint64_shift_left(v___x_3351_, v___x_3350_);
v___x_3353_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_3354_ = lean_uint64_lor(v___x_3352_, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3355_, 0, v_config_3348_);
lean_ctor_set_uint64(v___x_3355_, sizeof(void*)*1, v_key_3354_);
lean_inc(v_canUnfold_x3f_3342_);
lean_inc(v_synthPendingDepth_3341_);
lean_inc(v_defEqCtx_x3f_3340_);
lean_inc_ref(v_localInstances_3339_);
lean_inc_ref(v_lctx_3338_);
lean_inc(v_zetaDeltaSet_3337_);
v___x_3356_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v_zetaDeltaSet_3337_);
lean_ctor_set(v___x_3356_, 2, v_lctx_3338_);
lean_ctor_set(v___x_3356_, 3, v_localInstances_3339_);
lean_ctor_set(v___x_3356_, 4, v_defEqCtx_x3f_3340_);
lean_ctor_set(v___x_3356_, 5, v_synthPendingDepth_3341_);
lean_ctor_set(v___x_3356_, 6, v_canUnfold_x3f_3342_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7, v_trackZetaDelta_3336_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7 + 1, v_univApprox_3343_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3344_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*7 + 3, v_cacheInferType_3345_);
lean_inc(v___y_3307_);
lean_inc_ref(v___y_3310_);
lean_inc(v___y_3308_);
lean_inc(v_a_3313_);
v___x_3357_ = lean_whnf(v_a_3313_, v___x_3356_, v___y_3308_, v___y_3310_, v___y_3307_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
v___x_3359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_3360_ = l_Lean_Expr_isConstOf(v_a_3358_, v___x_3359_);
lean_dec(v_a_3358_);
if (v___x_3360_ == 0)
{
lean_dec(v_a_3313_);
v___y_3276_ = v___y_3305_;
v___y_3277_ = v___y_3309_;
v___y_3278_ = v___y_3306_;
v___y_3279_ = v___y_3308_;
v___y_3280_ = v___y_3310_;
v___y_3281_ = v___y_3307_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3361_; 
lean_inc(v_a_3313_);
v___x_3361_ = l_Lean_Meta_mkEqRefl(v_a_3313_, v___y_3306_, v___y_3308_, v___y_3310_, v___y_3307_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
lean_inc(v_mvarId_3171_);
v___x_3363_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3306_, v___y_3308_, v___y_3310_, v___y_3307_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v_nargs_3365_; lean_object* v___x_3366_; lean_object* v_dummy_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v_nargs_3365_ = l_Lean_Expr_getAppNumArgs(v_a_3313_);
v___x_3366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_3367_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_3365_);
v___x_3368_ = lean_mk_array(v_nargs_3365_, v_dummy_3367_);
v___x_3369_ = lean_unsigned_to_nat(1u);
v___x_3370_ = lean_nat_sub(v_nargs_3365_, v___x_3369_);
lean_dec(v_nargs_3365_);
v___x_3371_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3313_, v___x_3368_, v___x_3370_);
v___x_3372_ = lean_array_push(v___x_3371_, v_a_3362_);
v___x_3373_ = l_Lean_mkAppN(v___x_3366_, v___x_3372_);
lean_dec_ref(v___x_3372_);
lean_inc(v_val_3202_);
v___x_3374_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3375_ = l_Lean_Meta_mkAbsurd(v_a_3364_, v___x_3374_, v___x_3373_, v___y_3306_, v___y_3308_, v___y_3310_, v___y_3307_);
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
lean_inc(v_mvarId_3171_);
v___x_3380_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3376_, v___y_3308_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
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
v___x_3384_ = lean_box(v___x_3181_);
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
lean_ctor_set(v___x_3387_, 1, v___x_3206_);
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
v_a_3188_ = v___x_3389_;
goto v___jp_3187_;
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
v___y_3295_ = v___y_3305_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3308_;
v___y_3298_ = v___y_3307_;
v___y_3299_ = v___y_3309_;
v___y_3300_ = v___y_3310_;
v_a_3301_ = v_a_3394_;
goto v___jp_3294_;
}
}
}
else
{
lean_object* v_a_3396_; 
v_a_3396_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3375_, 1);
v___y_3295_ = v___y_3305_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3308_;
v___y_3298_ = v___y_3307_;
v___y_3299_ = v___y_3309_;
v___y_3300_ = v___y_3310_;
v_a_3301_ = v_a_3396_;
goto v___jp_3294_;
}
}
else
{
lean_object* v_a_3397_; 
lean_dec(v_a_3362_);
lean_dec(v_a_3313_);
v_a_3397_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3363_, 1);
v___y_3295_ = v___y_3305_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3308_;
v___y_3298_ = v___y_3307_;
v___y_3299_ = v___y_3309_;
v___y_3300_ = v___y_3310_;
v_a_3301_ = v_a_3397_;
goto v___jp_3294_;
}
}
else
{
lean_object* v_a_3398_; 
lean_dec(v_a_3313_);
v_a_3398_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3361_, 1);
v___y_3295_ = v___y_3305_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3308_;
v___y_3298_ = v___y_3307_;
v___y_3299_ = v___y_3309_;
v___y_3300_ = v___y_3310_;
v_a_3301_ = v_a_3398_;
goto v___jp_3294_;
}
}
}
else
{
lean_object* v_a_3399_; 
lean_dec(v_a_3313_);
v_a_3399_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3357_, 1);
v___y_3295_ = v___y_3305_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3308_;
v___y_3298_ = v___y_3307_;
v___y_3299_ = v___y_3309_;
v___y_3300_ = v___y_3310_;
v_a_3301_ = v_a_3399_;
goto v___jp_3294_;
}
}
}
}
else
{
lean_object* v_a_3402_; 
v_a_3402_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3312_, 1);
v___y_3295_ = v___y_3305_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3308_;
v___y_3298_ = v___y_3307_;
v___y_3299_ = v___y_3309_;
v___y_3300_ = v___y_3310_;
v_a_3301_ = v_a_3402_;
goto v___jp_3294_;
}
}
}
v___jp_3403_:
{
if (v___y_3410_ == 0)
{
v___y_3276_ = v___y_3404_;
v___y_3277_ = v___y_3408_;
v___y_3278_ = v___y_3405_;
v___y_3279_ = v___y_3407_;
v___y_3280_ = v___y_3409_;
v___y_3281_ = v___y_3406_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3411_; 
lean_inc_ref(v___x_3274_);
v___x_3411_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3274_, v___y_3407_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; uint8_t v___x_3413_; uint8_t v___x_3414_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v___x_3413_ = l_Lean_Expr_hasMVar(v_a_3412_);
v___x_3414_ = lean_bool_not(v___x_3413_);
if (v___x_3414_ == 0)
{
lean_dec(v_a_3412_);
v___y_3305_ = v___y_3404_;
v___y_3306_ = v___y_3405_;
v___y_3307_ = v___y_3406_;
v___y_3308_ = v___y_3407_;
v___y_3309_ = v___y_3408_;
v___y_3310_ = v___y_3409_;
v___y_3311_ = v___x_3233_;
goto v___jp_3304_;
}
else
{
uint8_t v___x_3415_; uint8_t v___x_3416_; 
v___x_3415_ = l_Lean_Expr_hasFVar(v_a_3412_);
lean_dec(v_a_3412_);
v___x_3416_ = lean_bool_not(v___x_3415_);
v___y_3305_ = v___y_3404_;
v___y_3306_ = v___y_3405_;
v___y_3307_ = v___y_3406_;
v___y_3308_ = v___y_3407_;
v___y_3309_ = v___y_3408_;
v___y_3310_ = v___y_3409_;
v___y_3311_ = v___x_3416_;
goto v___jp_3304_;
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3417_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3411_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3411_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
v___jp_3425_:
{
uint8_t v_useDecide_3432_; 
v_useDecide_3432_ = lean_ctor_get_uint8(v_config_3170_, sizeof(void*)*1);
if (v_useDecide_3432_ == 0)
{
v___y_3404_ = v___y_3426_;
v___y_3405_ = v___y_3428_;
v___y_3406_ = v___y_3431_;
v___y_3407_ = v___y_3429_;
v___y_3408_ = v_isHEq_3427_;
v___y_3409_ = v___y_3430_;
v___y_3410_ = v___x_3233_;
goto v___jp_3403_;
}
else
{
uint8_t v___x_3433_; uint8_t v___x_3434_; 
v___x_3433_ = l_Lean_Expr_hasFVar(v___x_3274_);
v___x_3434_ = lean_bool_not(v___x_3433_);
v___y_3404_ = v___y_3426_;
v___y_3405_ = v___y_3428_;
v___y_3406_ = v___y_3431_;
v___y_3407_ = v___y_3429_;
v___y_3408_ = v_isHEq_3427_;
v___y_3409_ = v___y_3430_;
v___y_3410_ = v___x_3434_;
goto v___jp_3403_;
}
}
v___jp_3435_:
{
lean_object* v___x_3441_; 
lean_inc_ref(v___x_3274_);
v___x_3441_ = l_Lean_Meta_matchHEq_x3f(v___x_3274_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3441_, 1);
if (lean_obj_tag(v_a_3442_) == 1)
{
lean_object* v_val_3443_; lean_object* v_snd_3444_; lean_object* v_snd_3445_; lean_object* v_fst_3446_; lean_object* v_fst_3447_; lean_object* v_fst_3448_; lean_object* v_snd_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3550_; 
v_val_3443_ = lean_ctor_get(v_a_3442_, 0);
lean_inc(v_val_3443_);
lean_dec_ref_known(v_a_3442_, 1);
v_snd_3444_ = lean_ctor_get(v_val_3443_, 1);
lean_inc(v_snd_3444_);
v_snd_3445_ = lean_ctor_get(v_snd_3444_, 1);
lean_inc(v_snd_3445_);
v_fst_3446_ = lean_ctor_get(v_val_3443_, 0);
lean_inc(v_fst_3446_);
lean_dec(v_val_3443_);
v_fst_3447_ = lean_ctor_get(v_snd_3444_, 0);
lean_inc(v_fst_3447_);
lean_dec(v_snd_3444_);
v_fst_3448_ = lean_ctor_get(v_snd_3445_, 0);
v_snd_3449_ = lean_ctor_get(v_snd_3445_, 1);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_snd_3445_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3451_ = v_snd_3445_;
v_isShared_3452_ = v_isSharedCheck_3550_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_snd_3449_);
lean_inc(v_fst_3448_);
lean_dec(v_snd_3445_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3550_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3447_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
if (lean_obj_tag(v_a_3454_) == 1)
{
lean_object* v_val_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3541_; 
v_val_3455_ = lean_ctor_get(v_a_3454_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_a_3454_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3457_ = v_a_3454_;
v_isShared_3458_ = v_isSharedCheck_3541_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_val_3455_);
lean_dec(v_a_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3541_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; 
v___x_3459_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3449_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
if (lean_obj_tag(v_a_3460_) == 1)
{
lean_object* v_toConstantVal_3461_; lean_object* v_val_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3532_; 
v_toConstantVal_3461_ = lean_ctor_get(v_val_3455_, 0);
lean_inc_ref(v_toConstantVal_3461_);
lean_dec(v_val_3455_);
v_val_3462_ = lean_ctor_get(v_a_3460_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_a_3460_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3464_ = v_a_3460_;
v_isShared_3465_ = v_isSharedCheck_3532_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_val_3462_);
lean_dec(v_a_3460_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3532_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_toConstantVal_3466_; lean_object* v_name_3467_; lean_object* v_name_3468_; uint8_t v___x_3469_; uint8_t v___x_3470_; 
v_toConstantVal_3466_ = lean_ctor_get(v_val_3462_, 0);
lean_inc_ref(v_toConstantVal_3466_);
lean_dec(v_val_3462_);
v_name_3467_ = lean_ctor_get(v_toConstantVal_3461_, 0);
lean_inc(v_name_3467_);
lean_dec_ref(v_toConstantVal_3461_);
v_name_3468_ = lean_ctor_get(v_toConstantVal_3466_, 0);
lean_inc(v_name_3468_);
lean_dec_ref(v_toConstantVal_3466_);
v___x_3469_ = lean_name_eq(v_name_3467_, v_name_3468_);
lean_dec(v_name_3468_);
lean_dec(v_name_3467_);
v___x_3470_ = lean_bool_not(v___x_3469_);
if (v___x_3470_ == 0)
{
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
lean_del_object(v___x_3451_);
lean_dec(v_fst_3448_);
lean_dec(v_fst_3446_);
v___y_3426_ = v_isEq_3436_;
v_isHEq_3427_ = v___x_3181_;
v___y_3428_ = v___y_3437_;
v___y_3429_ = v___y_3438_;
v___y_3430_ = v___y_3439_;
v___y_3431_ = v___y_3440_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_Meta_isExprDefEq(v_fst_3446_, v_fst_3448_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; uint8_t v___x_3473_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___x_3473_ = lean_unbox(v_a_3472_);
lean_dec(v_a_3472_);
if (v___x_3473_ == 0)
{
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
lean_del_object(v___x_3451_);
v___y_3426_ = v_isEq_3436_;
v_isHEq_3427_ = v___x_3181_;
v___y_3428_ = v___y_3437_;
v___y_3429_ = v___y_3438_;
v___y_3430_ = v___y_3439_;
v___y_3431_ = v___y_3440_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3474_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
lean_inc(v_mvarId_3171_);
v___x_3474_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v___x_3476_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3477_ = l_Lean_Meta_mkEqOfHEq(v___x_3476_, v___x_3181_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v___x_3479_ = l_Lean_Meta_mkNoConfusion(v_a_3475_, v_a_3478_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v___x_3481_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3480_, v___y_3438_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3484_; 
lean_dec_ref_known(v___x_3481_, 1);
v___x_3482_ = lean_box(v___x_3181_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3482_);
v___x_3484_ = v___x_3464_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3486_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 1, v___x_3206_);
lean_ctor_set(v___x_3451_, 0, v___x_3484_);
v___x_3486_ = v___x_3451_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v___x_3206_);
v___x_3486_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3488_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set_tag(v___x_3457_, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3486_);
v___x_3488_ = v___x_3457_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
v_a_3188_ = v___x_3488_;
goto v___jp_3187_;
}
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
lean_del_object(v___x_3451_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3492_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3481_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3481_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
lean_del_object(v___x_3451_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3500_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3479_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3479_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec(v_a_3475_);
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
lean_del_object(v___x_3451_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3508_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3477_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3477_);
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
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
lean_del_object(v___x_3451_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3516_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3474_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3474_);
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
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_del_object(v___x_3464_);
lean_del_object(v___x_3457_);
lean_del_object(v___x_3451_);
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3524_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3471_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3471_);
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
}
}
else
{
lean_dec(v_a_3460_);
lean_del_object(v___x_3457_);
lean_dec(v_val_3455_);
lean_del_object(v___x_3451_);
lean_dec(v_fst_3448_);
lean_dec(v_fst_3446_);
v___y_3426_ = v_isEq_3436_;
v_isHEq_3427_ = v___x_3181_;
v___y_3428_ = v___y_3437_;
v___y_3429_ = v___y_3438_;
v___y_3430_ = v___y_3439_;
v___y_3431_ = v___y_3440_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_del_object(v___x_3457_);
lean_dec(v_val_3455_);
lean_del_object(v___x_3451_);
lean_dec(v_fst_3448_);
lean_dec(v_fst_3446_);
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3533_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3459_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3459_);
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
lean_dec(v_a_3454_);
lean_del_object(v___x_3451_);
lean_dec(v_snd_3449_);
lean_dec(v_fst_3448_);
lean_dec(v_fst_3446_);
v___y_3426_ = v_isEq_3436_;
v_isHEq_3427_ = v___x_3181_;
v___y_3428_ = v___y_3437_;
v___y_3429_ = v___y_3438_;
v___y_3430_ = v___y_3439_;
v___y_3431_ = v___y_3440_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_del_object(v___x_3451_);
lean_dec(v_snd_3449_);
lean_dec(v_fst_3448_);
lean_dec(v_fst_3446_);
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3542_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3453_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3453_);
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
}
else
{
lean_dec(v_a_3442_);
v___y_3426_ = v_isEq_3436_;
v_isHEq_3427_ = v___x_3233_;
v___y_3428_ = v___y_3437_;
v___y_3429_ = v___y_3438_;
v___y_3430_ = v___y_3439_;
v___y_3431_ = v___y_3440_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3551_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3441_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3441_);
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
v___jp_3559_:
{
lean_object* v___x_3564_; 
lean_inc_ref(v___x_3274_);
v___x_3564_ = l_Lean_Meta_matchEq_x3f(v___x_3274_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
if (lean_obj_tag(v_a_3565_) == 1)
{
lean_object* v_val_3566_; lean_object* v_snd_3567_; lean_object* v_fst_3568_; lean_object* v_snd_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3649_; 
v_val_3566_ = lean_ctor_get(v_a_3565_, 0);
lean_inc(v_val_3566_);
lean_dec_ref_known(v_a_3565_, 1);
v_snd_3567_ = lean_ctor_get(v_val_3566_, 1);
lean_inc(v_snd_3567_);
lean_dec(v_val_3566_);
v_fst_3568_ = lean_ctor_get(v_snd_3567_, 0);
v_snd_3569_ = lean_ctor_get(v_snd_3567_, 1);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_snd_3567_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3571_ = v_snd_3567_;
v_isShared_3572_ = v_isSharedCheck_3649_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_snd_3569_);
lean_inc(v_fst_3568_);
lean_dec(v_snd_3567_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3649_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3568_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v___x_3573_, 1);
if (lean_obj_tag(v_a_3574_) == 1)
{
lean_object* v_val_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3640_; 
v_val_3575_ = lean_ctor_get(v_a_3574_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_a_3574_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3577_ = v_a_3574_;
v_isShared_3578_ = v_isSharedCheck_3640_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_val_3575_);
lean_dec(v_a_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3640_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3569_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
if (lean_obj_tag(v_a_3580_) == 1)
{
lean_object* v_toConstantVal_3581_; lean_object* v_val_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3631_; 
v_toConstantVal_3581_ = lean_ctor_get(v_val_3575_, 0);
lean_inc_ref(v_toConstantVal_3581_);
lean_dec(v_val_3575_);
v_val_3582_ = lean_ctor_get(v_a_3580_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_a_3580_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3584_ = v_a_3580_;
v_isShared_3585_ = v_isSharedCheck_3631_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_val_3582_);
lean_dec(v_a_3580_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3631_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v_toConstantVal_3586_; lean_object* v_name_3587_; lean_object* v_name_3588_; uint8_t v___x_3589_; uint8_t v___x_3590_; 
v_toConstantVal_3586_ = lean_ctor_get(v_val_3582_, 0);
lean_inc_ref(v_toConstantVal_3586_);
lean_dec(v_val_3582_);
v_name_3587_ = lean_ctor_get(v_toConstantVal_3581_, 0);
lean_inc(v_name_3587_);
lean_dec_ref(v_toConstantVal_3581_);
v_name_3588_ = lean_ctor_get(v_toConstantVal_3586_, 0);
lean_inc(v_name_3588_);
lean_dec_ref(v_toConstantVal_3586_);
v___x_3589_ = lean_name_eq(v_name_3587_, v_name_3588_);
lean_dec(v_name_3588_);
lean_dec(v_name_3587_);
v___x_3590_ = lean_bool_not(v___x_3589_);
if (v___x_3590_ == 0)
{
lean_del_object(v___x_3584_);
lean_del_object(v___x_3577_);
lean_del_object(v___x_3571_);
v_isEq_3436_ = v___x_3181_;
v___y_3437_ = v___y_3560_;
v___y_3438_ = v___y_3561_;
v___y_3439_ = v___y_3562_;
v___y_3440_ = v___y_3563_;
goto v___jp_3435_;
}
else
{
lean_object* v___x_3591_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
lean_inc(v_mvarId_3171_);
v___x_3591_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v___x_3591_, 1);
v___x_3593_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3594_ = l_Lean_Meta_mkNoConfusion(v_a_3592_, v___x_3593_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v___x_3596_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3595_, v___y_3561_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3599_; 
lean_dec_ref_known(v___x_3596_, 1);
v___x_3597_ = lean_box(v___x_3181_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3597_);
v___x_3599_ = v___x_3584_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3601_; 
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 1, v___x_3206_);
lean_ctor_set(v___x_3571_, 0, v___x_3599_);
v___x_3601_ = v___x_3571_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3206_);
v___x_3601_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3603_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set_tag(v___x_3577_, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3601_);
v___x_3603_ = v___x_3577_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
v_a_3188_ = v___x_3603_;
goto v___jp_3187_;
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_del_object(v___x_3584_);
lean_del_object(v___x_3577_);
lean_del_object(v___x_3571_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3607_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3596_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3596_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_del_object(v___x_3584_);
lean_del_object(v___x_3577_);
lean_del_object(v___x_3571_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3615_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3594_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3594_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_del_object(v___x_3584_);
lean_del_object(v___x_3577_);
lean_del_object(v___x_3571_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3623_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3591_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3591_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3580_);
lean_del_object(v___x_3577_);
lean_dec(v_val_3575_);
lean_del_object(v___x_3571_);
v_isEq_3436_ = v___x_3181_;
v___y_3437_ = v___y_3560_;
v___y_3438_ = v___y_3561_;
v___y_3439_ = v___y_3562_;
v___y_3440_ = v___y_3563_;
goto v___jp_3435_;
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_del_object(v___x_3577_);
lean_dec(v_val_3575_);
lean_del_object(v___x_3571_);
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3632_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3579_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3579_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
}
else
{
lean_dec(v_a_3574_);
lean_del_object(v___x_3571_);
lean_dec(v_snd_3569_);
v_isEq_3436_ = v___x_3181_;
v___y_3437_ = v___y_3560_;
v___y_3438_ = v___y_3561_;
v___y_3439_ = v___y_3562_;
v___y_3440_ = v___y_3563_;
goto v___jp_3435_;
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_del_object(v___x_3571_);
lean_dec(v_snd_3569_);
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3641_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3573_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3573_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
else
{
lean_dec(v_a_3565_);
v_isEq_3436_ = v___x_3233_;
v___y_3437_ = v___y_3560_;
v___y_3438_ = v___y_3561_;
v___y_3439_ = v___y_3562_;
v___y_3440_ = v___y_3563_;
goto v___jp_3435_;
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3650_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3564_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3564_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
v___jp_3658_:
{
lean_object* v___x_3663_; 
lean_inc_ref(v___x_3274_);
v___x_3663_ = l_Lean_refutableHasNotBit_x3f(v___x_3274_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
if (lean_obj_tag(v_a_3664_) == 1)
{
lean_object* v_val_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3705_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
v_val_3665_ = lean_ctor_get(v_a_3664_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_a_3664_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3667_ = v_a_3664_;
v_isShared_3668_ = v_isSharedCheck_3705_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_val_3665_);
lean_dec(v_a_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3705_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; 
lean_inc(v_mvarId_3171_);
v___x_3669_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
v___x_3671_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3672_ = l_Lean_Meta_mkAbsurd(v_a_3670_, v_val_3665_, v___x_3671_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3674_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3672_, 1);
v___x_3674_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3673_, v___y_3660_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
lean_dec_ref_known(v___x_3674_, 1);
v___x_3675_ = lean_box(v___x_3181_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3675_);
v___x_3677_ = v___x_3667_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
lean_ctor_set(v___x_3678_, 1, v___x_3206_);
v___x_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
v_a_3188_ = v___x_3679_;
goto v___jp_3187_;
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3667_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3681_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3674_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3674_);
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
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_del_object(v___x_3667_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3689_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3672_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3672_);
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
else
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_del_object(v___x_3667_);
lean_dec(v_val_3665_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3697_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3669_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3669_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
else
{
lean_object* v___x_3706_; 
lean_dec(v_a_3664_);
lean_inc_ref(v___x_3274_);
v___x_3706_ = l_Lean_Meta_matchNe_x3f(v___x_3274_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
if (lean_obj_tag(v_a_3707_) == 1)
{
lean_object* v_val_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3778_; 
v_val_3708_ = lean_ctor_get(v_a_3707_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_a_3707_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3710_ = v_a_3707_;
v_isShared_3711_ = v_isSharedCheck_3778_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_val_3708_);
lean_dec(v_a_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3778_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v_snd_3712_; lean_object* v_fst_3713_; lean_object* v_snd_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3777_; 
v_snd_3712_ = lean_ctor_get(v_val_3708_, 1);
lean_inc(v_snd_3712_);
lean_dec(v_val_3708_);
v_fst_3713_ = lean_ctor_get(v_snd_3712_, 0);
v_snd_3714_ = lean_ctor_get(v_snd_3712_, 1);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_snd_3712_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3716_ = v_snd_3712_;
v_isShared_3717_ = v_isSharedCheck_3777_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_snd_3714_);
lean_inc(v_fst_3713_);
lean_dec(v_snd_3712_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3777_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3718_; 
lean_inc(v_fst_3713_);
v___x_3718_ = l_Lean_Meta_isExprDefEq(v_fst_3713_, v_snd_3714_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; uint8_t v___x_3720_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v___x_3720_ = lean_unbox(v_a_3719_);
lean_dec(v_a_3719_);
if (v___x_3720_ == 0)
{
lean_del_object(v___x_3716_);
lean_dec(v_fst_3713_);
lean_del_object(v___x_3710_);
v___y_3560_ = v___y_3659_;
v___y_3561_ = v___y_3660_;
v___y_3562_ = v___y_3661_;
v___y_3563_ = v___y_3662_;
goto v___jp_3559_;
}
else
{
lean_object* v___x_3721_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec_ref(v_config_3170_);
lean_inc(v_mvarId_3171_);
v___x_3721_ = l_Lean_MVarId_getType(v_mvarId_3171_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3723_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
v___x_3723_ = l_Lean_Meta_mkEqRefl(v_fst_3713_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref_known(v___x_3723_, 1);
v___x_3725_ = l_Lean_LocalDecl_toExpr(v_val_3202_);
v___x_3726_ = l_Lean_Meta_mkAbsurd(v_a_3722_, v_a_3724_, v___x_3725_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v___x_3728_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3171_, v_a_3727_, v___y_3660_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
lean_dec_ref_known(v___x_3728_, 1);
v___x_3729_ = lean_box(v___x_3181_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3729_);
v___x_3731_ = v___x_3710_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3733_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 1, v___x_3206_);
lean_ctor_set(v___x_3716_, 0, v___x_3731_);
v___x_3733_ = v___x_3716_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3206_);
v___x_3733_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
v_a_3188_ = v___x_3734_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_del_object(v___x_3716_);
lean_del_object(v___x_3710_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3737_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3728_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3728_);
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
lean_del_object(v___x_3716_);
lean_del_object(v___x_3710_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3745_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3726_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3726_);
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
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec(v_a_3722_);
lean_del_object(v___x_3716_);
lean_del_object(v___x_3710_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3753_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3723_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3723_);
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
lean_del_object(v___x_3716_);
lean_dec(v_fst_3713_);
lean_del_object(v___x_3710_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
v_a_3761_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3721_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3721_);
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
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_del_object(v___x_3716_);
lean_dec(v_fst_3713_);
lean_del_object(v___x_3710_);
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3769_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3718_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3718_);
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
}
else
{
lean_dec(v_a_3707_);
v___y_3560_ = v___y_3659_;
v___y_3561_ = v___y_3660_;
v___y_3562_ = v___y_3661_;
v___y_3563_ = v___y_3662_;
goto v___jp_3559_;
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3779_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3706_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3706_);
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
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v___x_3274_);
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3787_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3663_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3663_);
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
if (v___y_3213_ == 0)
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
lean_object* v_searchFuel_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_searchFuel_3214_ = lean_ctor_get(v_config_3170_, 0);
v___x_3215_ = l_Lean_LocalDecl_fvarId(v_val_3202_);
lean_dec(v_val_3202_);
lean_inc(v_searchFuel_3214_);
lean_inc(v_mvarId_3171_);
v___x_3216_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3171_, v___x_3215_, v_searchFuel_3214_, v___y_3209_, v___y_3212_, v___y_3211_, v___y_3210_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; uint8_t v___x_3218_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v___x_3216_, 1);
v___x_3218_ = lean_unbox(v_a_3217_);
lean_dec(v_a_3217_);
if (v___x_3218_ == 0)
{
lean_del_object(v___x_3204_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
v_a_3196_ = v___x_3207_;
goto v___jp_3195_;
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3219_ = lean_box(v___x_3181_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3219_);
v___x_3221_ = v___x_3204_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
lean_ctor_set(v___x_3222_, 1, v___x_3206_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
v_a_3188_ = v___x_3223_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_del_object(v___x_3204_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v_a_3225_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3216_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3216_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
v___jp_3234_:
{
if (v___y_3240_ == 0)
{
v___y_3209_ = v___y_3235_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v___y_3237_;
v___y_3212_ = v___y_3238_;
v___y_3213_ = v___x_3233_;
goto v___jp_3208_;
}
else
{
uint8_t v___x_3241_; 
v___x_3241_ = lean_bool_not(v___y_3239_);
v___y_3209_ = v___y_3235_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v___y_3237_;
v___y_3212_ = v___y_3238_;
v___y_3213_ = v___x_3241_;
goto v___jp_3208_;
}
}
v___jp_3242_:
{
uint8_t v_emptyType_3249_; 
v_emptyType_3249_ = lean_ctor_get_uint8(v_config_3170_, sizeof(void*)*1 + 1);
if (v_emptyType_3249_ == 0)
{
v___y_3235_ = v___y_3245_;
v___y_3236_ = v___y_3248_;
v___y_3237_ = v___y_3247_;
v___y_3238_ = v___y_3246_;
v___y_3239_ = v___y_3244_;
v___y_3240_ = v___x_3233_;
goto v___jp_3234_;
}
else
{
uint8_t v___x_3250_; 
v___x_3250_ = lean_bool_not(v___y_3243_);
v___y_3235_ = v___y_3245_;
v___y_3236_ = v___y_3248_;
v___y_3237_ = v___y_3247_;
v___y_3238_ = v___y_3246_;
v___y_3239_ = v___y_3244_;
v___y_3240_ = v___x_3250_;
goto v___jp_3234_;
}
}
v___jp_3251_:
{
if (v___y_3258_ == 0)
{
v___y_3243_ = v___y_3254_;
v___y_3244_ = v___y_3257_;
v___y_3245_ = v___y_3255_;
v___y_3246_ = v___y_3252_;
v___y_3247_ = v___y_3253_;
v___y_3248_ = v___y_3256_;
goto v___jp_3242_;
}
else
{
lean_object* v___x_3259_; 
lean_inc(v_val_3202_);
lean_inc(v_mvarId_3171_);
v___x_3259_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3171_, v_val_3202_, v___y_3255_, v___y_3252_, v___y_3253_, v___y_3256_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; uint8_t v___x_3261_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v___x_3261_ = lean_unbox(v_a_3260_);
lean_dec(v_a_3260_);
if (v___x_3261_ == 0)
{
v___y_3243_ = v___y_3254_;
v___y_3244_ = v___y_3257_;
v___y_3245_ = v___y_3255_;
v___y_3246_ = v___y_3252_;
v___y_3247_ = v___y_3253_;
v___y_3248_ = v___y_3256_;
goto v___jp_3242_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
v___x_3262_ = lean_box(v___x_3181_);
v___x_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
v___x_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
lean_ctor_set(v___x_3264_, 1, v___x_3206_);
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
v_a_3188_ = v___x_3265_;
goto v___jp_3187_;
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_del_object(v___x_3204_);
lean_dec(v_val_3202_);
lean_del_object(v___x_3185_);
lean_dec(v_snd_3183_);
lean_dec(v_mvarId_3171_);
lean_dec_ref(v_config_3170_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3868_, lean_object* v_mvarId_3869_, lean_object* v_as_3870_, lean_object* v_sz_3871_, lean_object* v_i_3872_, lean_object* v_b_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
size_t v_sz_boxed_3879_; size_t v_i_boxed_3880_; lean_object* v_res_3881_; 
v_sz_boxed_3879_ = lean_unbox_usize(v_sz_3871_);
lean_dec(v_sz_3871_);
v_i_boxed_3880_ = lean_unbox_usize(v_i_3872_);
lean_dec(v_i_3872_);
v_res_3881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3868_, v_mvarId_3869_, v_as_3870_, v_sz_boxed_3879_, v_i_boxed_3880_, v_b_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec_ref(v_as_3870_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3882_, lean_object* v_mvarId_3883_, lean_object* v_as_3884_, size_t v_sz_3885_, size_t v_i_3886_, lean_object* v_b_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
uint8_t v___x_3893_; 
v___x_3893_ = lean_usize_dec_lt(v_i_3886_, v_sz_3885_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; 
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v_b_3887_);
return v___x_3894_;
}
else
{
lean_object* v_snd_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_4578_; 
v_snd_3895_ = lean_ctor_get(v_b_3887_, 1);
v_isSharedCheck_4578_ = !lean_is_exclusive(v_b_3887_);
if (v_isSharedCheck_4578_ == 0)
{
lean_object* v_unused_4579_; 
v_unused_4579_ = lean_ctor_get(v_b_3887_, 0);
lean_dec(v_unused_4579_);
v___x_3897_ = v_b_3887_;
v_isShared_3898_ = v_isSharedCheck_4578_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_snd_3895_);
lean_dec(v_b_3887_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_4578_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v_a_3900_; lean_object* v___x_3906_; lean_object* v_a_3908_; lean_object* v_a_3913_; 
v___x_3906_ = lean_box(0);
v_a_3913_ = lean_array_uget(v_as_3884_, v_i_3886_);
if (lean_obj_tag(v_a_3913_) == 0)
{
lean_del_object(v___x_3897_);
v_a_3908_ = v_snd_3895_;
goto v___jp_3907_;
}
else
{
lean_object* v_val_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_4577_; 
v_val_3914_ = lean_ctor_get(v_a_3913_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_a_3913_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_3916_ = v_a_3913_;
v_isShared_3917_ = v_isSharedCheck_4577_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_val_3914_);
lean_dec(v_a_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_4577_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; uint8_t v___y_3925_; uint8_t v___x_3945_; lean_object* v___y_3947_; uint8_t v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; uint8_t v___y_3952_; uint8_t v___y_3955_; uint8_t v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; uint8_t v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; uint8_t v___y_3968_; lean_object* v___y_3969_; uint8_t v___y_3970_; 
v___x_3918_ = lean_box(0);
v___x_3919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3945_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3914_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3986_; uint8_t v___y_3988_; uint8_t v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; uint8_t v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; uint8_t v___y_4002_; lean_object* v___y_4003_; uint8_t v___y_4004_; uint8_t v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; uint8_t v___y_4012_; lean_object* v_a_4013_; uint8_t v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; uint8_t v___y_4021_; lean_object* v___y_4022_; uint8_t v___y_4023_; uint8_t v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; uint8_t v___y_4120_; lean_object* v___y_4121_; uint8_t v___y_4122_; uint8_t v___y_4138_; uint8_t v_isHEq_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; uint8_t v_isEq_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___x_4507_; 
v___x_3986_ = l_Lean_LocalDecl_type(v_val_3914_);
lean_inc_ref(v___x_3986_);
v___x_4507_ = l_Lean_Meta_matchNot_x3f(v___x_3986_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref_known(v___x_4507_, 1);
if (lean_obj_tag(v_a_4508_) == 1)
{
lean_object* v_val_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4568_; 
v_val_4509_ = lean_ctor_get(v_a_4508_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v_a_4508_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4511_ = v_a_4508_;
v_isShared_4512_ = v_isSharedCheck_4568_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_val_4509_);
lean_dec(v_a_4508_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4568_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4509_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4513_, 1);
if (lean_obj_tag(v_a_4514_) == 1)
{
lean_object* v_val_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4559_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec_ref(v_config_3882_);
v_val_4515_ = lean_ctor_get(v_a_4514_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_a_4514_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4517_ = v_a_4514_;
v_isShared_4518_ = v_isSharedCheck_4559_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_val_4515_);
lean_dec(v_a_4514_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4559_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4519_; 
lean_inc(v_mvarId_3883_);
v___x_4519_ = l_Lean_MVarId_getType(v_mvarId_3883_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
lean_dec_ref_known(v___x_4519_, 1);
v___x_4521_ = l_Lean_LocalDecl_toExpr(v_val_3914_);
v___x_4522_ = l_Lean_mkFVar(v_val_4515_);
v___x_4523_ = l_Lean_Expr_app___override(v___x_4521_, v___x_4522_);
v___x_4524_ = l_Lean_Meta_mkFalseElim(v_a_4520_, v___x_4523_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4526_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
lean_dec_ref_known(v___x_4524_, 1);
v___x_4526_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3883_, v_a_4525_, v___y_3889_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v___x_4527_; lean_object* v___x_4529_; 
lean_dec_ref_known(v___x_4526_, 1);
v___x_4527_ = lean_box(v___x_3893_);
if (v_isShared_4518_ == 0)
{
lean_ctor_set(v___x_4517_, 0, v___x_4527_);
v___x_4529_ = v___x_4517_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v___x_4527_);
v___x_4529_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
lean_object* v___x_4530_; lean_object* v___x_4532_; 
v___x_4530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
lean_ctor_set(v___x_4530_, 1, v___x_3918_);
if (v_isShared_4512_ == 0)
{
lean_ctor_set_tag(v___x_4511_, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4530_);
v___x_4532_ = v___x_4511_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
v_a_3900_ = v___x_4532_;
goto v___jp_3899_;
}
}
}
else
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
lean_del_object(v___x_4517_);
lean_del_object(v___x_4511_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
v_a_4535_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4526_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4526_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_del_object(v___x_4517_);
lean_del_object(v___x_4511_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4543_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4524_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4524_);
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
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_del_object(v___x_4517_);
lean_dec(v_val_4515_);
lean_del_object(v___x_4511_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4551_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4519_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4519_);
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
else
{
lean_dec(v_a_4514_);
lean_del_object(v___x_4511_);
v___y_4371_ = v___y_3888_;
v___y_4372_ = v___y_3889_;
v___y_4373_ = v___y_3890_;
v___y_4374_ = v___y_3891_;
goto v___jp_4370_;
}
}
else
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4567_; 
lean_del_object(v___x_4511_);
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4560_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4562_ = v___x_4513_;
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4513_);
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
}
else
{
lean_dec(v_a_4508_);
v___y_4371_ = v___y_3888_;
v___y_4372_ = v___y_3889_;
v___y_4373_ = v___y_3890_;
v___y_4374_ = v___y_3891_;
goto v___jp_4370_;
}
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4569_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4507_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4507_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
v___jp_3987_:
{
uint8_t v_genDiseq_3994_; 
v_genDiseq_3994_ = lean_ctor_get_uint8(v_config_3882_, sizeof(void*)*1 + 2);
if (v_genDiseq_3994_ == 0)
{
lean_dec_ref(v___x_3986_);
v___y_3964_ = v___y_3988_;
v___y_3965_ = v___y_3993_;
v___y_3966_ = v___y_3991_;
v___y_3967_ = v___y_3990_;
v___y_3968_ = v___y_3989_;
v___y_3969_ = v___y_3992_;
v___y_3970_ = v___x_3945_;
goto v___jp_3963_;
}
else
{
uint8_t v___x_3995_; 
v___x_3995_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3986_);
v___y_3964_ = v___y_3988_;
v___y_3965_ = v___y_3993_;
v___y_3966_ = v___y_3991_;
v___y_3967_ = v___y_3990_;
v___y_3968_ = v___y_3989_;
v___y_3969_ = v___y_3992_;
v___y_3970_ = v___x_3995_;
goto v___jp_3963_;
}
}
v___jp_3996_:
{
if (v___y_4004_ == 0)
{
lean_dec_ref(v___y_3998_);
v___y_3988_ = v___y_3997_;
v___y_3989_ = v___y_4002_;
v___y_3990_ = v___y_4001_;
v___y_3991_ = v___y_4000_;
v___y_3992_ = v___y_4003_;
v___y_3993_ = v___y_3999_;
goto v___jp_3987_;
}
else
{
lean_object* v___x_4005_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v___x_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___y_3998_);
return v___x_4005_;
}
}
v___jp_4006_:
{
uint8_t v___x_4014_; 
v___x_4014_ = l_Lean_Exception_isInterrupt(v_a_4013_);
if (v___x_4014_ == 0)
{
uint8_t v___x_4015_; 
lean_inc_ref(v_a_4013_);
v___x_4015_ = l_Lean_Exception_isRuntime(v_a_4013_);
v___y_3997_ = v___y_4007_;
v___y_3998_ = v_a_4013_;
v___y_3999_ = v___y_4008_;
v___y_4000_ = v___y_4009_;
v___y_4001_ = v___y_4010_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4011_;
v___y_4004_ = v___x_4015_;
goto v___jp_3996_;
}
else
{
v___y_3997_ = v___y_4007_;
v___y_3998_ = v_a_4013_;
v___y_3999_ = v___y_4008_;
v___y_4000_ = v___y_4009_;
v___y_4001_ = v___y_4010_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4011_;
v___y_4004_ = v___x_4014_;
goto v___jp_3996_;
}
}
v___jp_4016_:
{
if (v___y_4023_ == 0)
{
v___y_3988_ = v___y_4017_;
v___y_3989_ = v___y_4021_;
v___y_3990_ = v___y_4020_;
v___y_3991_ = v___y_4019_;
v___y_3992_ = v___y_4022_;
v___y_3993_ = v___y_4018_;
goto v___jp_3987_;
}
else
{
lean_object* v___x_4024_; 
lean_inc_ref(v___x_3986_);
v___x_4024_ = l_Lean_Meta_mkDecide(v___x_3986_, v___y_4020_, v___y_4019_, v___y_4022_, v___y_4018_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4026_; uint8_t v_foApprox_4027_; uint8_t v_ctxApprox_4028_; uint8_t v_quasiPatternApprox_4029_; uint8_t v_constApprox_4030_; uint8_t v_isDefEqStuckEx_4031_; uint8_t v_unificationHints_4032_; uint8_t v_proofIrrelevance_4033_; uint8_t v_assignSyntheticOpaque_4034_; uint8_t v_offsetCnstrs_4035_; uint8_t v_etaStruct_4036_; uint8_t v_univApprox_4037_; uint8_t v_iota_4038_; uint8_t v_beta_4039_; uint8_t v_proj_4040_; uint8_t v_zeta_4041_; uint8_t v_zetaDelta_4042_; uint8_t v_zetaUnused_4043_; uint8_t v_zetaHave_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4113_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref_known(v___x_4024_, 1);
v___x_4026_ = l_Lean_Meta_Context_config(v___y_4020_);
v_foApprox_4027_ = lean_ctor_get_uint8(v___x_4026_, 0);
v_ctxApprox_4028_ = lean_ctor_get_uint8(v___x_4026_, 1);
v_quasiPatternApprox_4029_ = lean_ctor_get_uint8(v___x_4026_, 2);
v_constApprox_4030_ = lean_ctor_get_uint8(v___x_4026_, 3);
v_isDefEqStuckEx_4031_ = lean_ctor_get_uint8(v___x_4026_, 4);
v_unificationHints_4032_ = lean_ctor_get_uint8(v___x_4026_, 5);
v_proofIrrelevance_4033_ = lean_ctor_get_uint8(v___x_4026_, 6);
v_assignSyntheticOpaque_4034_ = lean_ctor_get_uint8(v___x_4026_, 7);
v_offsetCnstrs_4035_ = lean_ctor_get_uint8(v___x_4026_, 8);
v_etaStruct_4036_ = lean_ctor_get_uint8(v___x_4026_, 10);
v_univApprox_4037_ = lean_ctor_get_uint8(v___x_4026_, 11);
v_iota_4038_ = lean_ctor_get_uint8(v___x_4026_, 12);
v_beta_4039_ = lean_ctor_get_uint8(v___x_4026_, 13);
v_proj_4040_ = lean_ctor_get_uint8(v___x_4026_, 14);
v_zeta_4041_ = lean_ctor_get_uint8(v___x_4026_, 15);
v_zetaDelta_4042_ = lean_ctor_get_uint8(v___x_4026_, 16);
v_zetaUnused_4043_ = lean_ctor_get_uint8(v___x_4026_, 17);
v_zetaHave_4044_ = lean_ctor_get_uint8(v___x_4026_, 18);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4046_ = v___x_4026_;
v_isShared_4047_ = v_isSharedCheck_4113_;
goto v_resetjp_4045_;
}
else
{
lean_dec(v___x_4026_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4113_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
uint8_t v_trackZetaDelta_4048_; lean_object* v_zetaDeltaSet_4049_; lean_object* v_lctx_4050_; lean_object* v_localInstances_4051_; lean_object* v_defEqCtx_x3f_4052_; lean_object* v_synthPendingDepth_4053_; lean_object* v_canUnfold_x3f_4054_; uint8_t v_univApprox_4055_; uint8_t v_inTypeClassResolution_4056_; uint8_t v_cacheInferType_4057_; uint8_t v___x_4058_; lean_object* v_config_4060_; 
v_trackZetaDelta_4048_ = lean_ctor_get_uint8(v___y_4020_, sizeof(void*)*7);
v_zetaDeltaSet_4049_ = lean_ctor_get(v___y_4020_, 1);
v_lctx_4050_ = lean_ctor_get(v___y_4020_, 2);
v_localInstances_4051_ = lean_ctor_get(v___y_4020_, 3);
v_defEqCtx_x3f_4052_ = lean_ctor_get(v___y_4020_, 4);
v_synthPendingDepth_4053_ = lean_ctor_get(v___y_4020_, 5);
v_canUnfold_x3f_4054_ = lean_ctor_get(v___y_4020_, 6);
v_univApprox_4055_ = lean_ctor_get_uint8(v___y_4020_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4056_ = lean_ctor_get_uint8(v___y_4020_, sizeof(void*)*7 + 2);
v_cacheInferType_4057_ = lean_ctor_get_uint8(v___y_4020_, sizeof(void*)*7 + 3);
v___x_4058_ = 1;
if (v_isShared_4047_ == 0)
{
v_config_4060_ = v___x_4046_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 0, v_foApprox_4027_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 1, v_ctxApprox_4028_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 2, v_quasiPatternApprox_4029_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 3, v_constApprox_4030_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 4, v_isDefEqStuckEx_4031_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 5, v_unificationHints_4032_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 6, v_proofIrrelevance_4033_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 7, v_assignSyntheticOpaque_4034_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 8, v_offsetCnstrs_4035_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 10, v_etaStruct_4036_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 11, v_univApprox_4037_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 12, v_iota_4038_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 13, v_beta_4039_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 14, v_proj_4040_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 15, v_zeta_4041_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 16, v_zetaDelta_4042_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 17, v_zetaUnused_4043_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 18, v_zetaHave_4044_);
v_config_4060_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
uint64_t v___x_4061_; uint64_t v___x_4062_; uint64_t v___x_4063_; uint64_t v___x_4064_; uint64_t v___x_4065_; uint64_t v_key_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
lean_ctor_set_uint8(v_config_4060_, 9, v___x_4058_);
v___x_4061_ = l_Lean_Meta_Context_configKey(v___y_4020_);
v___x_4062_ = 3ULL;
v___x_4063_ = lean_uint64_shift_right(v___x_4061_, v___x_4062_);
v___x_4064_ = lean_uint64_shift_left(v___x_4063_, v___x_4062_);
v___x_4065_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_4066_ = lean_uint64_lor(v___x_4064_, v___x_4065_);
v___x_4067_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4067_, 0, v_config_4060_);
lean_ctor_set_uint64(v___x_4067_, sizeof(void*)*1, v_key_4066_);
lean_inc(v_canUnfold_x3f_4054_);
lean_inc(v_synthPendingDepth_4053_);
lean_inc(v_defEqCtx_x3f_4052_);
lean_inc_ref(v_localInstances_4051_);
lean_inc_ref(v_lctx_4050_);
lean_inc(v_zetaDeltaSet_4049_);
v___x_4068_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
lean_ctor_set(v___x_4068_, 1, v_zetaDeltaSet_4049_);
lean_ctor_set(v___x_4068_, 2, v_lctx_4050_);
lean_ctor_set(v___x_4068_, 3, v_localInstances_4051_);
lean_ctor_set(v___x_4068_, 4, v_defEqCtx_x3f_4052_);
lean_ctor_set(v___x_4068_, 5, v_synthPendingDepth_4053_);
lean_ctor_set(v___x_4068_, 6, v_canUnfold_x3f_4054_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7, v_trackZetaDelta_4048_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7 + 1, v_univApprox_4055_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4056_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*7 + 3, v_cacheInferType_4057_);
lean_inc(v___y_4018_);
lean_inc_ref(v___y_4022_);
lean_inc(v___y_4019_);
lean_inc(v_a_4025_);
v___x_4069_ = lean_whnf(v_a_4025_, v___x_4068_, v___y_4019_, v___y_4022_, v___y_4018_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4071_; uint8_t v___x_4072_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v___x_4071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_4072_ = l_Lean_Expr_isConstOf(v_a_4070_, v___x_4071_);
lean_dec(v_a_4070_);
if (v___x_4072_ == 0)
{
lean_dec(v_a_4025_);
v___y_3988_ = v___y_4017_;
v___y_3989_ = v___y_4021_;
v___y_3990_ = v___y_4020_;
v___y_3991_ = v___y_4019_;
v___y_3992_ = v___y_4022_;
v___y_3993_ = v___y_4018_;
goto v___jp_3987_;
}
else
{
lean_object* v___x_4073_; 
lean_inc(v_a_4025_);
v___x_4073_ = l_Lean_Meta_mkEqRefl(v_a_4025_, v___y_4020_, v___y_4019_, v___y_4022_, v___y_4018_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4075_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
lean_inc(v_mvarId_3883_);
v___x_4075_ = l_Lean_MVarId_getType(v_mvarId_3883_, v___y_4020_, v___y_4019_, v___y_4022_, v___y_4018_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v_nargs_4077_; lean_object* v___x_4078_; lean_object* v_dummy_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4075_, 1);
v_nargs_4077_ = l_Lean_Expr_getAppNumArgs(v_a_4025_);
v___x_4078_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_4079_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_4077_);
v___x_4080_ = lean_mk_array(v_nargs_4077_, v_dummy_4079_);
v___x_4081_ = lean_unsigned_to_nat(1u);
v___x_4082_ = lean_nat_sub(v_nargs_4077_, v___x_4081_);
lean_dec(v_nargs_4077_);
v___x_4083_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4025_, v___x_4080_, v___x_4082_);
v___x_4084_ = lean_array_push(v___x_4083_, v_a_4074_);
v___x_4085_ = l_Lean_mkAppN(v___x_4078_, v___x_4084_);
lean_dec_ref(v___x_4084_);
lean_inc(v_val_3914_);
v___x_4086_ = l_Lean_LocalDecl_toExpr(v_val_3914_);
v___x_4087_ = l_Lean_Meta_mkAbsurd(v_a_4076_, v___x_4086_, v___x_4085_, v___y_4020_, v___y_4019_, v___y_4022_, v___y_4018_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4107_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4107_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4107_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4092_; 
lean_inc(v_mvarId_3883_);
v___x_4092_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3883_, v_a_4088_, v___y_4019_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4104_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4104_ == 0)
{
lean_object* v_unused_4105_; 
v_unused_4105_ = lean_ctor_get(v___x_4092_, 0);
lean_dec(v_unused_4105_);
v___x_4094_ = v___x_4092_;
v_isShared_4095_ = v_isSharedCheck_4104_;
goto v_resetjp_4093_;
}
else
{
lean_dec(v___x_4092_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4104_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4096_; lean_object* v___x_4098_; 
v___x_4096_ = lean_box(v___x_3893_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set_tag(v___x_4094_, 1);
lean_ctor_set(v___x_4094_, 0, v___x_4096_);
v___x_4098_ = v___x_4094_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4096_);
v___x_4098_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
lean_object* v___x_4099_; lean_object* v___x_4101_; 
v___x_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
lean_ctor_set(v___x_4099_, 1, v___x_3918_);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4099_);
v___x_4101_ = v___x_4090_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
v_a_3900_ = v___x_4101_;
goto v___jp_3899_;
}
}
}
}
else
{
lean_object* v_a_4106_; 
lean_del_object(v___x_4090_);
v_a_4106_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4106_);
lean_dec_ref_known(v___x_4092_, 1);
v___y_4007_ = v___y_4017_;
v___y_4008_ = v___y_4018_;
v___y_4009_ = v___y_4019_;
v___y_4010_ = v___y_4020_;
v___y_4011_ = v___y_4022_;
v___y_4012_ = v___y_4021_;
v_a_4013_ = v_a_4106_;
goto v___jp_4006_;
}
}
}
else
{
lean_object* v_a_4108_; 
v_a_4108_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_a_4108_);
lean_dec_ref_known(v___x_4087_, 1);
v___y_4007_ = v___y_4017_;
v___y_4008_ = v___y_4018_;
v___y_4009_ = v___y_4019_;
v___y_4010_ = v___y_4020_;
v___y_4011_ = v___y_4022_;
v___y_4012_ = v___y_4021_;
v_a_4013_ = v_a_4108_;
goto v___jp_4006_;
}
}
else
{
lean_object* v_a_4109_; 
lean_dec(v_a_4074_);
lean_dec(v_a_4025_);
v_a_4109_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___x_4075_, 1);
v___y_4007_ = v___y_4017_;
v___y_4008_ = v___y_4018_;
v___y_4009_ = v___y_4019_;
v___y_4010_ = v___y_4020_;
v___y_4011_ = v___y_4022_;
v___y_4012_ = v___y_4021_;
v_a_4013_ = v_a_4109_;
goto v___jp_4006_;
}
}
else
{
lean_object* v_a_4110_; 
lean_dec(v_a_4025_);
v_a_4110_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4073_, 1);
v___y_4007_ = v___y_4017_;
v___y_4008_ = v___y_4018_;
v___y_4009_ = v___y_4019_;
v___y_4010_ = v___y_4020_;
v___y_4011_ = v___y_4022_;
v___y_4012_ = v___y_4021_;
v_a_4013_ = v_a_4110_;
goto v___jp_4006_;
}
}
}
else
{
lean_object* v_a_4111_; 
lean_dec(v_a_4025_);
v_a_4111_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4111_);
lean_dec_ref_known(v___x_4069_, 1);
v___y_4007_ = v___y_4017_;
v___y_4008_ = v___y_4018_;
v___y_4009_ = v___y_4019_;
v___y_4010_ = v___y_4020_;
v___y_4011_ = v___y_4022_;
v___y_4012_ = v___y_4021_;
v_a_4013_ = v_a_4111_;
goto v___jp_4006_;
}
}
}
}
else
{
lean_object* v_a_4114_; 
v_a_4114_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4024_, 1);
v___y_4007_ = v___y_4017_;
v___y_4008_ = v___y_4018_;
v___y_4009_ = v___y_4019_;
v___y_4010_ = v___y_4020_;
v___y_4011_ = v___y_4022_;
v___y_4012_ = v___y_4021_;
v_a_4013_ = v_a_4114_;
goto v___jp_4006_;
}
}
}
v___jp_4115_:
{
if (v___y_4122_ == 0)
{
v___y_3988_ = v___y_4116_;
v___y_3989_ = v___y_4120_;
v___y_3990_ = v___y_4119_;
v___y_3991_ = v___y_4118_;
v___y_3992_ = v___y_4121_;
v___y_3993_ = v___y_4117_;
goto v___jp_3987_;
}
else
{
lean_object* v___x_4123_; 
lean_inc_ref(v___x_3986_);
v___x_4123_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3986_, v___y_4118_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; uint8_t v___x_4125_; uint8_t v___x_4126_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref_known(v___x_4123_, 1);
v___x_4125_ = l_Lean_Expr_hasMVar(v_a_4124_);
v___x_4126_ = lean_bool_not(v___x_4125_);
if (v___x_4126_ == 0)
{
lean_dec(v_a_4124_);
v___y_4017_ = v___y_4116_;
v___y_4018_ = v___y_4117_;
v___y_4019_ = v___y_4118_;
v___y_4020_ = v___y_4119_;
v___y_4021_ = v___y_4120_;
v___y_4022_ = v___y_4121_;
v___y_4023_ = v___x_3945_;
goto v___jp_4016_;
}
else
{
uint8_t v___x_4127_; uint8_t v___x_4128_; 
v___x_4127_ = l_Lean_Expr_hasFVar(v_a_4124_);
lean_dec(v_a_4124_);
v___x_4128_ = lean_bool_not(v___x_4127_);
v___y_4017_ = v___y_4116_;
v___y_4018_ = v___y_4117_;
v___y_4019_ = v___y_4118_;
v___y_4020_ = v___y_4119_;
v___y_4021_ = v___y_4120_;
v___y_4022_ = v___y_4121_;
v___y_4023_ = v___x_4128_;
goto v___jp_4016_;
}
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4129_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4123_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4123_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
}
v___jp_4137_:
{
uint8_t v_useDecide_4144_; 
v_useDecide_4144_ = lean_ctor_get_uint8(v_config_3882_, sizeof(void*)*1);
if (v_useDecide_4144_ == 0)
{
v___y_4116_ = v_isHEq_4139_;
v___y_4117_ = v___y_4143_;
v___y_4118_ = v___y_4141_;
v___y_4119_ = v___y_4140_;
v___y_4120_ = v___y_4138_;
v___y_4121_ = v___y_4142_;
v___y_4122_ = v___x_3945_;
goto v___jp_4115_;
}
else
{
uint8_t v___x_4145_; uint8_t v___x_4146_; 
v___x_4145_ = l_Lean_Expr_hasFVar(v___x_3986_);
v___x_4146_ = lean_bool_not(v___x_4145_);
v___y_4116_ = v_isHEq_4139_;
v___y_4117_ = v___y_4143_;
v___y_4118_ = v___y_4141_;
v___y_4119_ = v___y_4140_;
v___y_4120_ = v___y_4138_;
v___y_4121_ = v___y_4142_;
v___y_4122_ = v___x_4146_;
goto v___jp_4115_;
}
}
v___jp_4147_:
{
lean_object* v___x_4153_; 
lean_inc_ref(v___x_3986_);
v___x_4153_ = l_Lean_Meta_matchHEq_x3f(v___x_3986_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4153_, 1);
if (lean_obj_tag(v_a_4154_) == 1)
{
lean_object* v_val_4155_; lean_object* v_snd_4156_; lean_object* v_snd_4157_; lean_object* v_fst_4158_; lean_object* v_fst_4159_; lean_object* v_fst_4160_; lean_object* v_snd_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4262_; 
v_val_4155_ = lean_ctor_get(v_a_4154_, 0);
lean_inc(v_val_4155_);
lean_dec_ref_known(v_a_4154_, 1);
v_snd_4156_ = lean_ctor_get(v_val_4155_, 1);
lean_inc(v_snd_4156_);
v_snd_4157_ = lean_ctor_get(v_snd_4156_, 1);
lean_inc(v_snd_4157_);
v_fst_4158_ = lean_ctor_get(v_val_4155_, 0);
lean_inc(v_fst_4158_);
lean_dec(v_val_4155_);
v_fst_4159_ = lean_ctor_get(v_snd_4156_, 0);
lean_inc(v_fst_4159_);
lean_dec(v_snd_4156_);
v_fst_4160_ = lean_ctor_get(v_snd_4157_, 0);
v_snd_4161_ = lean_ctor_get(v_snd_4157_, 1);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_snd_4157_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4163_ = v_snd_4157_;
v_isShared_4164_ = v_isSharedCheck_4262_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_snd_4161_);
lean_inc(v_fst_4160_);
lean_dec(v_snd_4157_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4262_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; 
v___x_4165_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4159_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
if (lean_obj_tag(v_a_4166_) == 1)
{
lean_object* v_val_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4253_; 
v_val_4167_ = lean_ctor_get(v_a_4166_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_a_4166_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4169_ = v_a_4166_;
v_isShared_4170_ = v_isSharedCheck_4253_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_val_4167_);
lean_dec(v_a_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4253_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4161_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4171_, 1);
if (lean_obj_tag(v_a_4172_) == 1)
{
lean_object* v_toConstantVal_4173_; lean_object* v_val_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4244_; 
v_toConstantVal_4173_ = lean_ctor_get(v_val_4167_, 0);
lean_inc_ref(v_toConstantVal_4173_);
lean_dec(v_val_4167_);
v_val_4174_ = lean_ctor_get(v_a_4172_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v_a_4172_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4176_ = v_a_4172_;
v_isShared_4177_ = v_isSharedCheck_4244_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_val_4174_);
lean_dec(v_a_4172_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4244_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v_toConstantVal_4178_; lean_object* v_name_4179_; lean_object* v_name_4180_; uint8_t v___x_4181_; uint8_t v___x_4182_; 
v_toConstantVal_4178_ = lean_ctor_get(v_val_4174_, 0);
lean_inc_ref(v_toConstantVal_4178_);
lean_dec(v_val_4174_);
v_name_4179_ = lean_ctor_get(v_toConstantVal_4173_, 0);
lean_inc(v_name_4179_);
lean_dec_ref(v_toConstantVal_4173_);
v_name_4180_ = lean_ctor_get(v_toConstantVal_4178_, 0);
lean_inc(v_name_4180_);
lean_dec_ref(v_toConstantVal_4178_);
v___x_4181_ = lean_name_eq(v_name_4179_, v_name_4180_);
lean_dec(v_name_4180_);
lean_dec(v_name_4179_);
v___x_4182_ = lean_bool_not(v___x_4181_);
if (v___x_4182_ == 0)
{
lean_del_object(v___x_4176_);
lean_del_object(v___x_4169_);
lean_del_object(v___x_4163_);
lean_dec(v_fst_4160_);
lean_dec(v_fst_4158_);
v___y_4138_ = v_isEq_4148_;
v_isHEq_4139_ = v___x_3893_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___y_4150_;
v___y_4142_ = v___y_4151_;
v___y_4143_ = v___y_4152_;
goto v___jp_4137_;
}
else
{
lean_object* v___x_4183_; 
v___x_4183_ = l_Lean_Meta_isExprDefEq(v_fst_4158_, v_fst_4160_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; uint8_t v___x_4185_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = lean_unbox(v_a_4184_);
lean_dec(v_a_4184_);
if (v___x_4185_ == 0)
{
lean_del_object(v___x_4176_);
lean_del_object(v___x_4169_);
lean_del_object(v___x_4163_);
v___y_4138_ = v_isEq_4148_;
v_isHEq_4139_ = v___x_3893_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___y_4150_;
v___y_4142_ = v___y_4151_;
v___y_4143_ = v___y_4152_;
goto v___jp_4137_;
}
else
{
lean_object* v___x_4186_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec_ref(v_config_3882_);
lean_inc(v_mvarId_3883_);
v___x_4186_ = l_Lean_MVarId_getType(v_mvarId_3883_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4186_, 1);
v___x_4188_ = l_Lean_LocalDecl_toExpr(v_val_3914_);
v___x_4189_ = l_Lean_Meta_mkEqOfHEq(v___x_4188_, v___x_3893_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4191_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = l_Lean_Meta_mkNoConfusion(v_a_4187_, v_a_4190_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4193_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v___x_4191_, 1);
v___x_4193_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3883_, v_a_4192_, v___y_4150_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v___x_4194_; lean_object* v___x_4196_; 
lean_dec_ref_known(v___x_4193_, 1);
v___x_4194_ = lean_box(v___x_3893_);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4194_);
v___x_4196_ = v___x_4176_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4194_);
v___x_4196_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4198_; 
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 1, v___x_3918_);
lean_ctor_set(v___x_4163_, 0, v___x_4196_);
v___x_4198_ = v___x_4163_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4196_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v___x_3918_);
v___x_4198_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4200_; 
if (v_isShared_4170_ == 0)
{
lean_ctor_set_tag(v___x_4169_, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4198_);
v___x_4200_ = v___x_4169_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4198_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
v_a_3900_ = v___x_4200_;
goto v___jp_3899_;
}
}
}
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
lean_del_object(v___x_4176_);
lean_del_object(v___x_4169_);
lean_del_object(v___x_4163_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
v_a_4204_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4193_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4193_);
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
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_del_object(v___x_4176_);
lean_del_object(v___x_4169_);
lean_del_object(v___x_4163_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4212_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4191_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4191_);
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
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
lean_dec(v_a_4187_);
lean_del_object(v___x_4176_);
lean_del_object(v___x_4169_);
lean_del_object(v___x_4163_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4220_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4189_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4189_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_del_object(v___x_4176_);
lean_del_object(v___x_4169_);
lean_del_object(v___x_4163_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4228_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4186_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4186_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_del_object(v___x_4176_);
lean_del_object(v___x_4169_);
lean_del_object(v___x_4163_);
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4236_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4183_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4183_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4172_);
lean_del_object(v___x_4169_);
lean_dec(v_val_4167_);
lean_del_object(v___x_4163_);
lean_dec(v_fst_4160_);
lean_dec(v_fst_4158_);
v___y_4138_ = v_isEq_4148_;
v_isHEq_4139_ = v___x_3893_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___y_4150_;
v___y_4142_ = v___y_4151_;
v___y_4143_ = v___y_4152_;
goto v___jp_4137_;
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_del_object(v___x_4169_);
lean_dec(v_val_4167_);
lean_del_object(v___x_4163_);
lean_dec(v_fst_4160_);
lean_dec(v_fst_4158_);
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4245_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4171_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4171_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
else
{
lean_dec(v_a_4166_);
lean_del_object(v___x_4163_);
lean_dec(v_snd_4161_);
lean_dec(v_fst_4160_);
lean_dec(v_fst_4158_);
v___y_4138_ = v_isEq_4148_;
v_isHEq_4139_ = v___x_3893_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___y_4150_;
v___y_4142_ = v___y_4151_;
v___y_4143_ = v___y_4152_;
goto v___jp_4137_;
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_del_object(v___x_4163_);
lean_dec(v_snd_4161_);
lean_dec(v_fst_4160_);
lean_dec(v_fst_4158_);
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4254_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4165_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4165_);
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
}
else
{
lean_dec(v_a_4154_);
v___y_4138_ = v_isEq_4148_;
v_isHEq_4139_ = v___x_3945_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___y_4150_;
v___y_4142_ = v___y_4151_;
v___y_4143_ = v___y_4152_;
goto v___jp_4137_;
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4263_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4153_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4153_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
v___jp_4271_:
{
lean_object* v___x_4276_; 
lean_inc_ref(v___x_3986_);
v___x_4276_ = l_Lean_Meta_matchEq_x3f(v___x_3986_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref_known(v___x_4276_, 1);
if (lean_obj_tag(v_a_4277_) == 1)
{
lean_object* v_val_4278_; lean_object* v_snd_4279_; lean_object* v_fst_4280_; lean_object* v_snd_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4361_; 
v_val_4278_ = lean_ctor_get(v_a_4277_, 0);
lean_inc(v_val_4278_);
lean_dec_ref_known(v_a_4277_, 1);
v_snd_4279_ = lean_ctor_get(v_val_4278_, 1);
lean_inc(v_snd_4279_);
lean_dec(v_val_4278_);
v_fst_4280_ = lean_ctor_get(v_snd_4279_, 0);
v_snd_4281_ = lean_ctor_get(v_snd_4279_, 1);
v_isSharedCheck_4361_ = !lean_is_exclusive(v_snd_4279_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4283_ = v_snd_4279_;
v_isShared_4284_ = v_isSharedCheck_4361_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_snd_4281_);
lean_inc(v_fst_4280_);
lean_dec(v_snd_4279_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4361_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4280_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___x_4285_, 1);
if (lean_obj_tag(v_a_4286_) == 1)
{
lean_object* v_val_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4352_; 
v_val_4287_ = lean_ctor_get(v_a_4286_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v_a_4286_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4289_ = v_a_4286_;
v_isShared_4290_ = v_isSharedCheck_4352_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_val_4287_);
lean_dec(v_a_4286_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4352_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4281_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
if (lean_obj_tag(v_a_4292_) == 1)
{
lean_object* v_toConstantVal_4293_; lean_object* v_val_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4343_; 
v_toConstantVal_4293_ = lean_ctor_get(v_val_4287_, 0);
lean_inc_ref(v_toConstantVal_4293_);
lean_dec(v_val_4287_);
v_val_4294_ = lean_ctor_get(v_a_4292_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v_a_4292_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4296_ = v_a_4292_;
v_isShared_4297_ = v_isSharedCheck_4343_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_val_4294_);
lean_dec(v_a_4292_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4343_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v_toConstantVal_4298_; lean_object* v_name_4299_; lean_object* v_name_4300_; uint8_t v___x_4301_; uint8_t v___x_4302_; 
v_toConstantVal_4298_ = lean_ctor_get(v_val_4294_, 0);
lean_inc_ref(v_toConstantVal_4298_);
lean_dec(v_val_4294_);
v_name_4299_ = lean_ctor_get(v_toConstantVal_4293_, 0);
lean_inc(v_name_4299_);
lean_dec_ref(v_toConstantVal_4293_);
v_name_4300_ = lean_ctor_get(v_toConstantVal_4298_, 0);
lean_inc(v_name_4300_);
lean_dec_ref(v_toConstantVal_4298_);
v___x_4301_ = lean_name_eq(v_name_4299_, v_name_4300_);
lean_dec(v_name_4300_);
lean_dec(v_name_4299_);
v___x_4302_ = lean_bool_not(v___x_4301_);
if (v___x_4302_ == 0)
{
lean_del_object(v___x_4296_);
lean_del_object(v___x_4289_);
lean_del_object(v___x_4283_);
v_isEq_4148_ = v___x_3893_;
v___y_4149_ = v___y_4272_;
v___y_4150_ = v___y_4273_;
v___y_4151_ = v___y_4274_;
v___y_4152_ = v___y_4275_;
goto v___jp_4147_;
}
else
{
lean_object* v___x_4303_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec_ref(v_config_3882_);
lean_inc(v_mvarId_3883_);
v___x_4303_ = l_Lean_MVarId_getType(v_mvarId_3883_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___x_4303_, 1);
v___x_4305_ = l_Lean_LocalDecl_toExpr(v_val_3914_);
v___x_4306_ = l_Lean_Meta_mkNoConfusion(v_a_4304_, v___x_4305_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4308_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v___x_4308_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3883_, v_a_4307_, v___y_4273_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v___x_4309_; lean_object* v___x_4311_; 
lean_dec_ref_known(v___x_4308_, 1);
v___x_4309_ = lean_box(v___x_3893_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v___x_4309_);
v___x_4311_ = v___x_4296_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
lean_object* v___x_4313_; 
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 1, v___x_3918_);
lean_ctor_set(v___x_4283_, 0, v___x_4311_);
v___x_4313_ = v___x_4283_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4311_);
lean_ctor_set(v_reuseFailAlloc_4317_, 1, v___x_3918_);
v___x_4313_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
lean_object* v___x_4315_; 
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4313_);
v___x_4315_ = v___x_4289_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4313_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
v_a_3900_ = v___x_4315_;
goto v___jp_3899_;
}
}
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_del_object(v___x_4296_);
lean_del_object(v___x_4289_);
lean_del_object(v___x_4283_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
v_a_4319_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4308_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4308_);
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
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_del_object(v___x_4296_);
lean_del_object(v___x_4289_);
lean_del_object(v___x_4283_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4327_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4306_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4306_);
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
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_del_object(v___x_4296_);
lean_del_object(v___x_4289_);
lean_del_object(v___x_4283_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4335_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4303_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4303_);
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
}
}
else
{
lean_dec(v_a_4292_);
lean_del_object(v___x_4289_);
lean_dec(v_val_4287_);
lean_del_object(v___x_4283_);
v_isEq_4148_ = v___x_3893_;
v___y_4149_ = v___y_4272_;
v___y_4150_ = v___y_4273_;
v___y_4151_ = v___y_4274_;
v___y_4152_ = v___y_4275_;
goto v___jp_4147_;
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_del_object(v___x_4289_);
lean_dec(v_val_4287_);
lean_del_object(v___x_4283_);
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4344_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4291_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4291_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
else
{
lean_dec(v_a_4286_);
lean_del_object(v___x_4283_);
lean_dec(v_snd_4281_);
v_isEq_4148_ = v___x_3893_;
v___y_4149_ = v___y_4272_;
v___y_4150_ = v___y_4273_;
v___y_4151_ = v___y_4274_;
v___y_4152_ = v___y_4275_;
goto v___jp_4147_;
}
}
else
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
lean_del_object(v___x_4283_);
lean_dec(v_snd_4281_);
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4353_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4355_ = v___x_4285_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4285_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4353_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
}
else
{
lean_dec(v_a_4277_);
v_isEq_4148_ = v___x_3945_;
v___y_4149_ = v___y_4272_;
v___y_4150_ = v___y_4273_;
v___y_4151_ = v___y_4274_;
v___y_4152_ = v___y_4275_;
goto v___jp_4147_;
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4362_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4276_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4276_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
v___jp_4370_:
{
lean_object* v___x_4375_; 
lean_inc_ref(v___x_3986_);
v___x_4375_ = l_Lean_refutableHasNotBit_x3f(v___x_3986_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4375_, 1);
if (lean_obj_tag(v_a_4376_) == 1)
{
lean_object* v_val_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4417_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec_ref(v_config_3882_);
v_val_4377_ = lean_ctor_get(v_a_4376_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_a_4376_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4379_ = v_a_4376_;
v_isShared_4380_ = v_isSharedCheck_4417_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_val_4377_);
lean_dec(v_a_4376_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4417_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4381_; 
lean_inc(v_mvarId_3883_);
v___x_4381_ = l_Lean_MVarId_getType(v_mvarId_3883_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4381_, 1);
v___x_4383_ = l_Lean_LocalDecl_toExpr(v_val_3914_);
v___x_4384_ = l_Lean_Meta_mkAbsurd(v_a_4382_, v_val_4377_, v___x_4383_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3883_, v_a_4385_, v___y_4372_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v___x_4387_; lean_object* v___x_4389_; 
lean_dec_ref_known(v___x_4386_, 1);
v___x_4387_ = lean_box(v___x_3893_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 0, v___x_4387_);
v___x_4389_ = v___x_4379_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
lean_ctor_set(v___x_4390_, 1, v___x_3918_);
v___x_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
v_a_3900_ = v___x_4391_;
goto v___jp_3899_;
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_del_object(v___x_4379_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
v_a_4393_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4386_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4386_);
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
lean_del_object(v___x_4379_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4401_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4384_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4384_);
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
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_del_object(v___x_4379_);
lean_dec(v_val_4377_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4409_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4381_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4381_);
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
lean_object* v___x_4418_; 
lean_dec(v_a_4376_);
lean_inc_ref(v___x_3986_);
v___x_4418_ = l_Lean_Meta_matchNe_x3f(v___x_3986_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4419_);
lean_dec_ref_known(v___x_4418_, 1);
if (lean_obj_tag(v_a_4419_) == 1)
{
lean_object* v_val_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4490_; 
v_val_4420_ = lean_ctor_get(v_a_4419_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v_a_4419_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4422_ = v_a_4419_;
v_isShared_4423_ = v_isSharedCheck_4490_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_val_4420_);
lean_dec(v_a_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4490_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v_snd_4424_; lean_object* v_fst_4425_; lean_object* v_snd_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4489_; 
v_snd_4424_ = lean_ctor_get(v_val_4420_, 1);
lean_inc(v_snd_4424_);
lean_dec(v_val_4420_);
v_fst_4425_ = lean_ctor_get(v_snd_4424_, 0);
v_snd_4426_ = lean_ctor_get(v_snd_4424_, 1);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_snd_4424_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4428_ = v_snd_4424_;
v_isShared_4429_ = v_isSharedCheck_4489_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_snd_4426_);
lean_inc(v_fst_4425_);
lean_dec(v_snd_4424_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4489_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; 
lean_inc(v_fst_4425_);
v___x_4430_ = l_Lean_Meta_isExprDefEq(v_fst_4425_, v_snd_4426_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; uint8_t v___x_4432_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_a_4431_);
lean_dec_ref_known(v___x_4430_, 1);
v___x_4432_ = lean_unbox(v_a_4431_);
lean_dec(v_a_4431_);
if (v___x_4432_ == 0)
{
lean_del_object(v___x_4428_);
lean_dec(v_fst_4425_);
lean_del_object(v___x_4422_);
v___y_4272_ = v___y_4371_;
v___y_4273_ = v___y_4372_;
v___y_4274_ = v___y_4373_;
v___y_4275_ = v___y_4374_;
goto v___jp_4271_;
}
else
{
lean_object* v___x_4433_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec_ref(v_config_3882_);
lean_inc(v_mvarId_3883_);
v___x_4433_ = l_Lean_MVarId_getType(v_mvarId_3883_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4435_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref_known(v___x_4433_, 1);
v___x_4435_ = l_Lean_Meta_mkEqRefl(v_fst_4425_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v___x_4435_, 1);
v___x_4437_ = l_Lean_LocalDecl_toExpr(v_val_3914_);
v___x_4438_ = l_Lean_Meta_mkAbsurd(v_a_4434_, v_a_4436_, v___x_4437_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4440_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_a_4439_);
lean_dec_ref_known(v___x_4438_, 1);
v___x_4440_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3883_, v_a_4439_, v___y_4372_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v___x_4441_; lean_object* v___x_4443_; 
lean_dec_ref_known(v___x_4440_, 1);
v___x_4441_ = lean_box(v___x_3893_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v___x_4441_);
v___x_4443_ = v___x_4422_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
lean_object* v___x_4445_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 1, v___x_3918_);
lean_ctor_set(v___x_4428_, 0, v___x_4443_);
v___x_4445_ = v___x_4428_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4443_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v___x_3918_);
v___x_4445_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4446_; 
v___x_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4445_);
v_a_3900_ = v___x_4446_;
goto v___jp_3899_;
}
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_del_object(v___x_4428_);
lean_del_object(v___x_4422_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
v_a_4449_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4440_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4440_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_del_object(v___x_4428_);
lean_del_object(v___x_4422_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4457_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4438_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4438_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec(v_a_4434_);
lean_del_object(v___x_4428_);
lean_del_object(v___x_4422_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4465_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4435_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4435_);
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
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_del_object(v___x_4428_);
lean_dec(v_fst_4425_);
lean_del_object(v___x_4422_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
v_a_4473_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4433_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4433_);
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
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_del_object(v___x_4428_);
lean_dec(v_fst_4425_);
lean_del_object(v___x_4422_);
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4481_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4430_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4430_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4419_);
v___y_4272_ = v___y_4371_;
v___y_4273_ = v___y_4372_;
v___y_4274_ = v___y_4373_;
v___y_4275_ = v___y_4374_;
goto v___jp_4271_;
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4491_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4418_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4418_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_dec_ref(v___x_3986_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_4499_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4375_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4375_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
}
else
{
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
v_a_3908_ = v___x_3919_;
goto v___jp_3907_;
}
v___jp_3920_:
{
if (v___y_3925_ == 0)
{
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
v_a_3908_ = v___x_3919_;
goto v___jp_3907_;
}
else
{
lean_object* v_searchFuel_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v_searchFuel_3926_ = lean_ctor_get(v_config_3882_, 0);
v___x_3927_ = l_Lean_LocalDecl_fvarId(v_val_3914_);
lean_dec(v_val_3914_);
lean_inc(v_searchFuel_3926_);
lean_inc(v_mvarId_3883_);
v___x_3928_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3883_, v___x_3927_, v_searchFuel_3926_, v___y_3922_, v___y_3924_, v___y_3921_, v___y_3923_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; uint8_t v___x_3930_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3930_ = lean_unbox(v_a_3929_);
lean_dec(v_a_3929_);
if (v___x_3930_ == 0)
{
lean_del_object(v___x_3916_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
v_a_3908_ = v___x_3919_;
goto v___jp_3907_;
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3933_; 
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v___x_3931_ = lean_box(v___x_3893_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3931_);
v___x_3933_ = v___x_3916_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
lean_ctor_set(v___x_3934_, 1, v___x_3918_);
v___x_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
v_a_3900_ = v___x_3935_;
goto v___jp_3899_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_del_object(v___x_3916_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_3937_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3928_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3928_);
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
}
v___jp_3946_:
{
if (v___y_3952_ == 0)
{
v___y_3921_ = v___y_3947_;
v___y_3922_ = v___y_3949_;
v___y_3923_ = v___y_3951_;
v___y_3924_ = v___y_3950_;
v___y_3925_ = v___x_3945_;
goto v___jp_3920_;
}
else
{
uint8_t v___x_3953_; 
v___x_3953_ = lean_bool_not(v___y_3948_);
v___y_3921_ = v___y_3947_;
v___y_3922_ = v___y_3949_;
v___y_3923_ = v___y_3951_;
v___y_3924_ = v___y_3950_;
v___y_3925_ = v___x_3953_;
goto v___jp_3920_;
}
}
v___jp_3954_:
{
uint8_t v_emptyType_3961_; 
v_emptyType_3961_ = lean_ctor_get_uint8(v_config_3882_, sizeof(void*)*1 + 1);
if (v_emptyType_3961_ == 0)
{
v___y_3947_ = v___y_3959_;
v___y_3948_ = v___y_3955_;
v___y_3949_ = v___y_3957_;
v___y_3950_ = v___y_3958_;
v___y_3951_ = v___y_3960_;
v___y_3952_ = v___x_3945_;
goto v___jp_3946_;
}
else
{
uint8_t v___x_3962_; 
v___x_3962_ = lean_bool_not(v___y_3956_);
v___y_3947_ = v___y_3959_;
v___y_3948_ = v___y_3955_;
v___y_3949_ = v___y_3957_;
v___y_3950_ = v___y_3958_;
v___y_3951_ = v___y_3960_;
v___y_3952_ = v___x_3962_;
goto v___jp_3946_;
}
}
v___jp_3963_:
{
if (v___y_3970_ == 0)
{
v___y_3955_ = v___y_3964_;
v___y_3956_ = v___y_3968_;
v___y_3957_ = v___y_3967_;
v___y_3958_ = v___y_3966_;
v___y_3959_ = v___y_3969_;
v___y_3960_ = v___y_3965_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_3971_; 
lean_inc(v_val_3914_);
lean_inc(v_mvarId_3883_);
v___x_3971_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3883_, v_val_3914_, v___y_3967_, v___y_3966_, v___y_3969_, v___y_3965_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; uint8_t v___x_3973_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref_known(v___x_3971_, 1);
v___x_3973_ = lean_unbox(v_a_3972_);
lean_dec(v_a_3972_);
if (v___x_3973_ == 0)
{
v___y_3955_ = v___y_3964_;
v___y_3956_ = v___y_3968_;
v___y_3957_ = v___y_3967_;
v___y_3958_ = v___y_3966_;
v___y_3959_ = v___y_3969_;
v___y_3960_ = v___y_3965_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v___x_3974_ = lean_box(v___x_3893_);
v___x_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3974_);
v___x_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
lean_ctor_set(v___x_3976_, 1, v___x_3918_);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
v_a_3900_ = v___x_3977_;
goto v___jp_3899_;
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3895_);
lean_dec(v_mvarId_3883_);
lean_dec_ref(v_config_3882_);
v_a_3978_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3971_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3971_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
}
}
}
v___jp_3899_:
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3901_, 0, v_a_3900_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3901_);
v___x_3903_ = v___x_3897_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3901_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_snd_3895_);
v___x_3903_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
}
v___jp_3907_:
{
lean_object* v___x_3909_; size_t v___x_3910_; size_t v___x_3911_; lean_object* v___x_3912_; 
v___x_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3906_);
lean_ctor_set(v___x_3909_, 1, v_a_3908_);
v___x_3910_ = ((size_t)1ULL);
v___x_3911_ = lean_usize_add(v_i_3886_, v___x_3910_);
v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3882_, v_mvarId_3883_, v_as_3884_, v_sz_3885_, v___x_3911_, v___x_3909_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
return v___x_3912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4580_, lean_object* v_mvarId_4581_, lean_object* v_as_4582_, lean_object* v_sz_4583_, lean_object* v_i_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
size_t v_sz_boxed_4591_; size_t v_i_boxed_4592_; lean_object* v_res_4593_; 
v_sz_boxed_4591_ = lean_unbox_usize(v_sz_4583_);
lean_dec(v_sz_4583_);
v_i_boxed_4592_ = lean_unbox_usize(v_i_4584_);
lean_dec(v_i_4584_);
v_res_4593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4580_, v_mvarId_4581_, v_as_4582_, v_sz_boxed_4591_, v_i_boxed_4592_, v_b_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec_ref(v_as_4582_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4594_, lean_object* v_config_4595_, lean_object* v_mvarId_4596_, lean_object* v_n_4597_, lean_object* v_b_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
if (lean_obj_tag(v_n_4597_) == 0)
{
lean_object* v_cs_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; size_t v_sz_4607_; size_t v___x_4608_; lean_object* v___x_4609_; 
v_cs_4604_ = lean_ctor_get(v_n_4597_, 0);
v___x_4605_ = lean_box(0);
v___x_4606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
lean_ctor_set(v___x_4606_, 1, v_b_4598_);
v_sz_4607_ = lean_array_size(v_cs_4604_);
v___x_4608_ = ((size_t)0ULL);
v___x_4609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4594_, v_config_4595_, v_mvarId_4596_, v_cs_4604_, v_sz_4607_, v___x_4608_, v___x_4606_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
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
else
{
lean_object* v_vs_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; size_t v_sz_4636_; size_t v___x_4637_; lean_object* v___x_4638_; 
v_vs_4633_ = lean_ctor_get(v_n_4597_, 0);
v___x_4634_ = lean_box(0);
v___x_4635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
lean_ctor_set(v___x_4635_, 1, v_b_4598_);
v_sz_4636_ = lean_array_size(v_vs_4633_);
v___x_4637_ = ((size_t)0ULL);
v___x_4638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4595_, v_mvarId_4596_, v_vs_4633_, v_sz_4636_, v___x_4637_, v___x_4635_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4653_; 
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4641_ = v___x_4638_;
v_isShared_4642_ = v_isSharedCheck_4653_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4638_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4653_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v_fst_4643_; 
v_fst_4643_ = lean_ctor_get(v_a_4639_, 0);
if (lean_obj_tag(v_fst_4643_) == 0)
{
lean_object* v_snd_4644_; lean_object* v___x_4645_; lean_object* v___x_4647_; 
v_snd_4644_ = lean_ctor_get(v_a_4639_, 1);
lean_inc(v_snd_4644_);
lean_dec(v_a_4639_);
v___x_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4645_, 0, v_snd_4644_);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 0, v___x_4645_);
v___x_4647_ = v___x_4641_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
else
{
lean_object* v_val_4649_; lean_object* v___x_4651_; 
lean_inc_ref(v_fst_4643_);
lean_dec(v_a_4639_);
v_val_4649_ = lean_ctor_get(v_fst_4643_, 0);
lean_inc(v_val_4649_);
lean_dec_ref_known(v_fst_4643_, 1);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 0, v_val_4649_);
v___x_4651_ = v___x_4641_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_val_4649_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
v_a_4654_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4638_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4638_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4662_, lean_object* v_config_4663_, lean_object* v_mvarId_4664_, lean_object* v_as_4665_, size_t v_sz_4666_, size_t v_i_4667_, lean_object* v_b_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
uint8_t v___x_4674_; 
v___x_4674_ = lean_usize_dec_lt(v_i_4667_, v_sz_4666_);
if (v___x_4674_ == 0)
{
lean_object* v___x_4675_; 
lean_dec(v_mvarId_4664_);
lean_dec_ref(v_config_4663_);
v___x_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4675_, 0, v_b_4668_);
return v___x_4675_;
}
else
{
lean_object* v_snd_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4710_; 
v_snd_4676_ = lean_ctor_get(v_b_4668_, 1);
v_isSharedCheck_4710_ = !lean_is_exclusive(v_b_4668_);
if (v_isSharedCheck_4710_ == 0)
{
lean_object* v_unused_4711_; 
v_unused_4711_ = lean_ctor_get(v_b_4668_, 0);
lean_dec(v_unused_4711_);
v___x_4678_ = v_b_4668_;
v_isShared_4679_ = v_isSharedCheck_4710_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_snd_4676_);
lean_dec(v_b_4668_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4710_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v_a_4680_; lean_object* v___x_4681_; 
v_a_4680_ = lean_array_uget_borrowed(v_as_4665_, v_i_4667_);
lean_inc(v_snd_4676_);
lean_inc(v_mvarId_4664_);
lean_inc_ref(v_config_4663_);
v___x_4681_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4662_, v_config_4663_, v_mvarId_4664_, v_a_4680_, v_snd_4676_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4701_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4684_ = v___x_4681_;
v_isShared_4685_ = v_isSharedCheck_4701_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4701_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
if (lean_obj_tag(v_a_4682_) == 0)
{
lean_object* v___x_4686_; lean_object* v___x_4688_; 
lean_dec(v_mvarId_4664_);
lean_dec_ref(v_config_4663_);
v___x_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4686_, 0, v_a_4682_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 0, v___x_4686_);
v___x_4688_ = v___x_4678_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4692_, 1, v_snd_4676_);
v___x_4688_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4690_; 
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
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4694_; lean_object* v___x_4696_; 
lean_del_object(v___x_4684_);
lean_dec(v_snd_4676_);
v_a_4693_ = lean_ctor_get(v_a_4682_, 0);
lean_inc(v_a_4693_);
lean_dec_ref_known(v_a_4682_, 1);
v___x_4694_ = lean_box(0);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 1, v_a_4693_);
lean_ctor_set(v___x_4678_, 0, v___x_4694_);
v___x_4696_ = v___x_4678_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4694_);
lean_ctor_set(v_reuseFailAlloc_4700_, 1, v_a_4693_);
v___x_4696_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
size_t v___x_4697_; size_t v___x_4698_; 
v___x_4697_ = ((size_t)1ULL);
v___x_4698_ = lean_usize_add(v_i_4667_, v___x_4697_);
v_i_4667_ = v___x_4698_;
v_b_4668_ = v___x_4696_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_del_object(v___x_4678_);
lean_dec(v_snd_4676_);
lean_dec(v_mvarId_4664_);
lean_dec_ref(v_config_4663_);
v_a_4702_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4681_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4681_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4712_, lean_object* v_config_4713_, lean_object* v_mvarId_4714_, lean_object* v_as_4715_, lean_object* v_sz_4716_, lean_object* v_i_4717_, lean_object* v_b_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_){
_start:
{
size_t v_sz_boxed_4724_; size_t v_i_boxed_4725_; lean_object* v_res_4726_; 
v_sz_boxed_4724_ = lean_unbox_usize(v_sz_4716_);
lean_dec(v_sz_4716_);
v_i_boxed_4725_ = lean_unbox_usize(v_i_4717_);
lean_dec(v_i_4717_);
v_res_4726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4712_, v_config_4713_, v_mvarId_4714_, v_as_4715_, v_sz_boxed_4724_, v_i_boxed_4725_, v_b_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec_ref(v_as_4715_);
lean_dec_ref(v_init_4712_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4727_, lean_object* v_config_4728_, lean_object* v_mvarId_4729_, lean_object* v_n_4730_, lean_object* v_b_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4727_, v_config_4728_, v_mvarId_4729_, v_n_4730_, v_b_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec(v___y_4733_);
lean_dec_ref(v___y_4732_);
lean_dec_ref(v_n_4730_);
lean_dec_ref(v_init_4727_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4738_, lean_object* v_mvarId_4739_, lean_object* v_t_4740_, lean_object* v_init_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v_root_4747_; lean_object* v_tail_4748_; lean_object* v___x_4749_; 
v_root_4747_ = lean_ctor_get(v_t_4740_, 0);
v_tail_4748_ = lean_ctor_get(v_t_4740_, 1);
lean_inc(v_mvarId_4739_);
lean_inc_ref(v_config_4738_);
lean_inc_ref(v_init_4741_);
v___x_4749_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4741_, v_config_4738_, v_mvarId_4739_, v_root_4747_, v_init_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec_ref(v_init_4741_);
if (lean_obj_tag(v___x_4749_) == 0)
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4786_; 
v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4752_ = v___x_4749_;
v_isShared_4753_ = v_isSharedCheck_4786_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4749_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4786_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
if (lean_obj_tag(v_a_4750_) == 0)
{
lean_object* v_a_4754_; lean_object* v___x_4756_; 
lean_dec(v_mvarId_4739_);
lean_dec_ref(v_config_4738_);
v_a_4754_ = lean_ctor_get(v_a_4750_, 0);
lean_inc(v_a_4754_);
lean_dec_ref_known(v_a_4750_, 1);
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 0, v_a_4754_);
v___x_4756_ = v___x_4752_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4754_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; size_t v_sz_4761_; size_t v___x_4762_; lean_object* v___x_4763_; 
lean_del_object(v___x_4752_);
v_a_4758_ = lean_ctor_get(v_a_4750_, 0);
lean_inc(v_a_4758_);
lean_dec_ref_known(v_a_4750_, 1);
v___x_4759_ = lean_box(0);
v___x_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4759_);
lean_ctor_set(v___x_4760_, 1, v_a_4758_);
v_sz_4761_ = lean_array_size(v_tail_4748_);
v___x_4762_ = ((size_t)0ULL);
v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4738_, v_mvarId_4739_, v_tail_4748_, v_sz_4761_, v___x_4762_, v___x_4760_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
if (lean_obj_tag(v___x_4763_) == 0)
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4777_; 
v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4766_ = v___x_4763_;
v_isShared_4767_ = v_isSharedCheck_4777_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4763_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4777_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v_fst_4768_; 
v_fst_4768_ = lean_ctor_get(v_a_4764_, 0);
if (lean_obj_tag(v_fst_4768_) == 0)
{
lean_object* v_snd_4769_; lean_object* v___x_4771_; 
v_snd_4769_ = lean_ctor_get(v_a_4764_, 1);
lean_inc(v_snd_4769_);
lean_dec(v_a_4764_);
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 0, v_snd_4769_);
v___x_4771_ = v___x_4766_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_snd_4769_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
else
{
lean_object* v_val_4773_; lean_object* v___x_4775_; 
lean_inc_ref(v_fst_4768_);
lean_dec(v_a_4764_);
v_val_4773_ = lean_ctor_get(v_fst_4768_, 0);
lean_inc(v_val_4773_);
lean_dec_ref_known(v_fst_4768_, 1);
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 0, v_val_4773_);
v___x_4775_ = v___x_4766_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_val_4773_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
v_a_4778_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4763_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4763_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
}
}
else
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4794_; 
lean_dec(v_mvarId_4739_);
lean_dec_ref(v_config_4738_);
v_a_4787_ = lean_ctor_get(v___x_4749_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4789_ = v___x_4749_;
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4749_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4795_, lean_object* v_mvarId_4796_, lean_object* v_t_4797_, lean_object* v_init_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_){
_start:
{
lean_object* v_res_4804_; 
v_res_4804_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4795_, v_mvarId_4796_, v_t_4797_, v_init_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec(v___y_4800_);
lean_dec_ref(v___y_4799_);
lean_dec_ref(v_t_4797_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4805_, lean_object* v___x_4806_, lean_object* v_config_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v___x_4813_; 
lean_inc(v_mvarId_4805_);
v___x_4813_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4805_, v___x_4806_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v___x_4814_; 
lean_dec_ref_known(v___x_4813_, 1);
lean_inc(v_mvarId_4805_);
v___x_4814_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4805_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4848_; 
v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4817_ = v___x_4814_;
v_isShared_4818_ = v_isSharedCheck_4848_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___x_4814_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4848_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
uint8_t v___x_4819_; 
v___x_4819_ = lean_unbox(v_a_4815_);
if (v___x_4819_ == 0)
{
lean_object* v_lctx_4820_; lean_object* v_decls_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
lean_del_object(v___x_4817_);
v_lctx_4820_ = lean_ctor_get(v___y_4808_, 2);
v_decls_4821_ = lean_ctor_get(v_lctx_4820_, 1);
v___x_4822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4823_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4807_, v_mvarId_4805_, v_decls_4821_, v___x_4822_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4836_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4826_ = v___x_4823_;
v_isShared_4827_ = v_isSharedCheck_4836_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4823_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4836_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v_fst_4828_; 
v_fst_4828_ = lean_ctor_get(v_a_4824_, 0);
lean_inc(v_fst_4828_);
lean_dec(v_a_4824_);
if (lean_obj_tag(v_fst_4828_) == 0)
{
lean_object* v___x_4830_; 
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v_a_4815_);
v___x_4830_ = v___x_4826_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4815_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
else
{
lean_object* v_val_4832_; lean_object* v___x_4834_; 
lean_dec(v_a_4815_);
v_val_4832_ = lean_ctor_get(v_fst_4828_, 0);
lean_inc(v_val_4832_);
lean_dec_ref_known(v_fst_4828_, 1);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v_val_4832_);
v___x_4834_ = v___x_4826_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_val_4832_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
else
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
lean_dec(v_a_4815_);
v_a_4837_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4823_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4823_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4840_ == 0)
{
v___x_4842_ = v___x_4839_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4837_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
else
{
lean_object* v___x_4846_; 
lean_dec_ref(v_config_4807_);
lean_dec(v_mvarId_4805_);
if (v_isShared_4818_ == 0)
{
v___x_4846_ = v___x_4817_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4815_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
else
{
lean_dec_ref(v_config_4807_);
lean_dec(v_mvarId_4805_);
return v___x_4814_;
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
lean_dec_ref(v_config_4807_);
lean_dec(v_mvarId_4805_);
v_a_4849_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4813_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4813_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4854_; 
if (v_isShared_4852_ == 0)
{
v___x_4854_ = v___x_4851_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4857_, lean_object* v___x_4858_, lean_object* v_config_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4857_, v___x_4858_, v_config_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4868_, lean_object* v_config_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___x_4875_; lean_object* v___f_4876_; lean_object* v___x_4877_; 
v___x_4875_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4868_);
v___f_4876_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4876_, 0, v_mvarId_4868_);
lean_closure_set(v___f_4876_, 1, v___x_4875_);
lean_closure_set(v___f_4876_, 2, v_config_4869_);
v___x_4877_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4868_, v___f_4876_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4878_, lean_object* v_config_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_MVarId_contradictionCore(v_mvarId_4878_, v_config_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4886_, lean_object* v_config_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
lean_object* v___x_4893_; 
lean_inc(v_mvarId_4886_);
v___x_4893_ = l_Lean_MVarId_contradictionCore(v_mvarId_4886_, v_config_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4906_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4896_ = v___x_4893_;
v_isShared_4897_ = v_isSharedCheck_4906_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4893_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4906_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
uint8_t v___x_4898_; 
v___x_4898_ = lean_unbox(v_a_4894_);
lean_dec(v_a_4894_);
if (v___x_4898_ == 0)
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; 
lean_del_object(v___x_4896_);
v___x_4899_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4900_ = lean_box(0);
v___x_4901_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4899_, v_mvarId_4886_, v___x_4900_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
return v___x_4901_;
}
else
{
lean_object* v___x_4902_; lean_object* v___x_4904_; 
lean_dec(v_mvarId_4886_);
v___x_4902_ = lean_box(0);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 0, v___x_4902_);
v___x_4904_ = v___x_4896_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v___x_4902_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
else
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4914_; 
lean_dec(v_mvarId_4886_);
v_a_4907_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4909_ = v___x_4893_;
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4893_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4912_; 
if (v_isShared_4910_ == 0)
{
v___x_4912_ = v___x_4909_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4907_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4915_, lean_object* v_config_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Lean_MVarId_contradiction(v_mvarId_4915_, v_config_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4985_; uint8_t v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4985_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4986_ = 0;
v___x_4987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4988_ = l_Lean_registerTraceClass(v___x_4985_, v___x_4986_, v___x_4987_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4990_;
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
