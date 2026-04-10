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
size_t lean_usize_shift_left(size_t, size_t);
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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_51_; size_t v___x_52_; size_t v___x_53_; 
v___x_51_ = ((size_t)5ULL);
v___x_52_ = ((size_t)1ULL);
v___x_53_ = lean_usize_shift_left(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_54_; size_t v___x_55_; size_t v___x_56_; 
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_56_ = lean_usize_sub(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(lean_object* v_x_58_, size_t v_x_59_, size_t v_x_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v_es_63_; size_t v___x_64_; size_t v___x_65_; size_t v___x_66_; size_t v___x_67_; lean_object* v_j_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_es_63_ = lean_ctor_get(v_x_58_, 0);
v___x_64_ = ((size_t)5ULL);
v___x_65_ = ((size_t)1ULL);
v___x_66_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_67_ = lean_usize_land(v_x_59_, v___x_66_);
v_j_68_ = lean_usize_to_nat(v___x_67_);
v___x_69_ = lean_array_get_size(v_es_63_);
v___x_70_ = lean_nat_dec_lt(v_j_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_dec(v_j_68_);
lean_dec(v_x_62_);
lean_dec(v_x_61_);
return v_x_58_;
}
else
{
lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_107_; 
lean_inc_ref(v_es_63_);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v_x_58_, 0);
lean_dec(v_unused_108_);
v___x_72_ = v_x_58_;
v_isShared_73_ = v_isSharedCheck_107_;
goto v_resetjp_71_;
}
else
{
lean_dec(v_x_58_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_107_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_v_74_; lean_object* v___x_75_; lean_object* v_xs_x27_76_; lean_object* v___y_78_; 
v_v_74_ = lean_array_fget(v_es_63_, v_j_68_);
v___x_75_ = lean_box(0);
v_xs_x27_76_ = lean_array_fset(v_es_63_, v_j_68_, v___x_75_);
switch(lean_obj_tag(v_v_74_))
{
case 0:
{
lean_object* v_key_83_; lean_object* v_val_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_94_; 
v_key_83_ = lean_ctor_get(v_v_74_, 0);
v_val_84_ = lean_ctor_get(v_v_74_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v_v_74_);
if (v_isSharedCheck_94_ == 0)
{
v___x_86_ = v_v_74_;
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_val_84_);
lean_inc(v_key_83_);
lean_dec(v_v_74_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
uint8_t v___x_88_; 
v___x_88_ = l_Lean_instBEqMVarId_beq(v_x_61_, v_key_83_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_del_object(v___x_86_);
v___x_89_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_83_, v_val_84_, v_x_61_, v_x_62_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
v___y_78_ = v___x_90_;
goto v___jp_77_;
}
else
{
lean_object* v___x_92_; 
lean_dec(v_val_84_);
lean_dec(v_key_83_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v_x_62_);
lean_ctor_set(v___x_86_, 0, v_x_61_);
v___x_92_ = v___x_86_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_x_61_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_x_62_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
v___y_78_ = v___x_92_;
goto v___jp_77_;
}
}
}
}
case 1:
{
lean_object* v_node_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_105_; 
v_node_95_ = lean_ctor_get(v_v_74_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v_v_74_);
if (v_isSharedCheck_105_ == 0)
{
v___x_97_ = v_v_74_;
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_node_95_);
lean_dec(v_v_74_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_99_ = lean_usize_shift_right(v_x_59_, v___x_64_);
v___x_100_ = lean_usize_add(v_x_60_, v___x_65_);
v___x_101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_node_95_, v___x_99_, v___x_100_, v_x_61_, v_x_62_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_101_);
v___x_103_ = v___x_97_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
v___y_78_ = v___x_103_;
goto v___jp_77_;
}
}
}
default: 
{
lean_object* v___x_106_; 
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_x_61_);
lean_ctor_set(v___x_106_, 1, v_x_62_);
v___y_78_ = v___x_106_;
goto v___jp_77_;
}
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = lean_array_fset(v_xs_x27_76_, v_j_68_, v___y_78_);
lean_dec(v_j_68_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_79_);
v___x_81_ = v___x_72_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
else
{
lean_object* v_ks_109_; lean_object* v_vs_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_130_; 
v_ks_109_ = lean_ctor_get(v_x_58_, 0);
v_vs_110_ = lean_ctor_get(v_x_58_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_130_ == 0)
{
v___x_112_ = v_x_58_;
v_isShared_113_ = v_isSharedCheck_130_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_vs_110_);
lean_inc(v_ks_109_);
lean_dec(v_x_58_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_130_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_ks_109_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_vs_110_);
v___x_115_ = v_reuseFailAlloc_129_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v_newNode_116_; uint8_t v___y_118_; size_t v___x_124_; uint8_t v___x_125_; 
v_newNode_116_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v___x_115_, v_x_61_, v_x_62_);
v___x_124_ = ((size_t)7ULL);
v___x_125_ = lean_usize_dec_le(v___x_124_, v_x_60_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_116_);
v___x_127_ = lean_unsigned_to_nat(4u);
v___x_128_ = lean_nat_dec_lt(v___x_126_, v___x_127_);
lean_dec(v___x_126_);
v___y_118_ = v___x_128_;
goto v___jp_117_;
}
else
{
v___y_118_ = v___x_125_;
goto v___jp_117_;
}
v___jp_117_:
{
if (v___y_118_ == 0)
{
lean_object* v_ks_119_; lean_object* v_vs_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_ks_119_ = lean_ctor_get(v_newNode_116_, 0);
lean_inc_ref(v_ks_119_);
v_vs_120_ = lean_ctor_get(v_newNode_116_, 1);
lean_inc_ref(v_vs_120_);
lean_dec_ref(v_newNode_116_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_x_60_, v_ks_119_, v_vs_120_, v___x_121_, v___x_122_);
lean_dec_ref(v_vs_120_);
lean_dec_ref(v_ks_119_);
return v___x_123_;
}
else
{
return v_newNode_116_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_131_, lean_object* v_keys_132_, lean_object* v_vals_133_, lean_object* v_i_134_, lean_object* v_entries_135_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_array_get_size(v_keys_132_);
v___x_137_ = lean_nat_dec_lt(v_i_134_, v___x_136_);
if (v___x_137_ == 0)
{
lean_dec(v_i_134_);
return v_entries_135_;
}
else
{
lean_object* v_k_138_; lean_object* v_v_139_; uint64_t v___x_140_; size_t v_h_141_; size_t v___x_142_; lean_object* v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v_h_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_k_138_ = lean_array_fget_borrowed(v_keys_132_, v_i_134_);
v_v_139_ = lean_array_fget_borrowed(v_vals_133_, v_i_134_);
v___x_140_ = l_Lean_instHashableMVarId_hash(v_k_138_);
v_h_141_ = lean_uint64_to_usize(v___x_140_);
v___x_142_ = ((size_t)5ULL);
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_sub(v_depth_131_, v___x_144_);
v___x_146_ = lean_usize_mul(v___x_142_, v___x_145_);
v_h_147_ = lean_usize_shift_right(v_h_141_, v___x_146_);
v___x_148_ = lean_nat_add(v_i_134_, v___x_143_);
lean_dec(v_i_134_);
lean_inc(v_v_139_);
lean_inc(v_k_138_);
v___x_149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_entries_135_, v_h_147_, v_depth_131_, v_k_138_, v_v_139_);
v_i_134_ = v___x_148_;
v_entries_135_ = v___x_149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_151_, lean_object* v_keys_152_, lean_object* v_vals_153_, lean_object* v_i_154_, lean_object* v_entries_155_){
_start:
{
size_t v_depth_boxed_156_; lean_object* v_res_157_; 
v_depth_boxed_156_ = lean_unbox_usize(v_depth_151_);
lean_dec(v_depth_151_);
v_res_157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_156_, v_keys_152_, v_vals_153_, v_i_154_, v_entries_155_);
lean_dec_ref(v_vals_153_);
lean_dec_ref(v_keys_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
size_t v_x_1122__boxed_163_; size_t v_x_1123__boxed_164_; lean_object* v_res_165_; 
v_x_1122__boxed_163_ = lean_unbox_usize(v_x_159_);
lean_dec(v_x_159_);
v_x_1123__boxed_164_ = lean_unbox_usize(v_x_160_);
lean_dec(v_x_160_);
v_res_165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_158_, v_x_1122__boxed_163_, v_x_1123__boxed_164_, v_x_161_, v_x_162_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint64_t v___x_169_; size_t v___x_170_; size_t v___x_171_; lean_object* v___x_172_; 
v___x_169_ = l_Lean_instHashableMVarId_hash(v_x_167_);
v___x_170_ = lean_uint64_to_usize(v___x_169_);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_166_, v___x_170_, v___x_171_, v_x_167_, v_x_168_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object* v_mvarId_173_, lean_object* v_val_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; lean_object* v_mctx_178_; lean_object* v_cache_179_; lean_object* v_zetaDeltaFVarIds_180_; lean_object* v_postponed_181_; lean_object* v_diag_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_210_; 
v___x_177_ = lean_st_ref_take(v___y_175_);
v_mctx_178_ = lean_ctor_get(v___x_177_, 0);
v_cache_179_ = lean_ctor_get(v___x_177_, 1);
v_zetaDeltaFVarIds_180_ = lean_ctor_get(v___x_177_, 2);
v_postponed_181_ = lean_ctor_get(v___x_177_, 3);
v_diag_182_ = lean_ctor_get(v___x_177_, 4);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_210_ == 0)
{
v___x_184_ = v___x_177_;
v_isShared_185_ = v_isSharedCheck_210_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_diag_182_);
lean_inc(v_postponed_181_);
lean_inc(v_zetaDeltaFVarIds_180_);
lean_inc(v_cache_179_);
lean_inc(v_mctx_178_);
lean_dec(v___x_177_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_210_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_depth_186_; lean_object* v_levelAssignDepth_187_; lean_object* v_lmvarCounter_188_; lean_object* v_mvarCounter_189_; lean_object* v_lDecls_190_; lean_object* v_decls_191_; lean_object* v_userNames_192_; lean_object* v_lAssignment_193_; lean_object* v_eAssignment_194_; lean_object* v_dAssignment_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_209_; 
v_depth_186_ = lean_ctor_get(v_mctx_178_, 0);
v_levelAssignDepth_187_ = lean_ctor_get(v_mctx_178_, 1);
v_lmvarCounter_188_ = lean_ctor_get(v_mctx_178_, 2);
v_mvarCounter_189_ = lean_ctor_get(v_mctx_178_, 3);
v_lDecls_190_ = lean_ctor_get(v_mctx_178_, 4);
v_decls_191_ = lean_ctor_get(v_mctx_178_, 5);
v_userNames_192_ = lean_ctor_get(v_mctx_178_, 6);
v_lAssignment_193_ = lean_ctor_get(v_mctx_178_, 7);
v_eAssignment_194_ = lean_ctor_get(v_mctx_178_, 8);
v_dAssignment_195_ = lean_ctor_get(v_mctx_178_, 9);
v_isSharedCheck_209_ = !lean_is_exclusive(v_mctx_178_);
if (v_isSharedCheck_209_ == 0)
{
v___x_197_ = v_mctx_178_;
v_isShared_198_ = v_isSharedCheck_209_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_dAssignment_195_);
lean_inc(v_eAssignment_194_);
lean_inc(v_lAssignment_193_);
lean_inc(v_userNames_192_);
lean_inc(v_decls_191_);
lean_inc(v_lDecls_190_);
lean_inc(v_mvarCounter_189_);
lean_inc(v_lmvarCounter_188_);
lean_inc(v_levelAssignDepth_187_);
lean_inc(v_depth_186_);
lean_dec(v_mctx_178_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_209_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_194_, v_mvarId_173_, v_val_174_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 8, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_depth_186_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_levelAssignDepth_187_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_lmvarCounter_188_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_mvarCounter_189_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v_lDecls_190_);
lean_ctor_set(v_reuseFailAlloc_208_, 5, v_decls_191_);
lean_ctor_set(v_reuseFailAlloc_208_, 6, v_userNames_192_);
lean_ctor_set(v_reuseFailAlloc_208_, 7, v_lAssignment_193_);
lean_ctor_set(v_reuseFailAlloc_208_, 8, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_208_, 9, v_dAssignment_195_);
v___x_201_ = v_reuseFailAlloc_208_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_203_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_201_);
v___x_203_ = v___x_184_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_cache_179_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_zetaDeltaFVarIds_180_);
lean_ctor_set(v_reuseFailAlloc_207_, 3, v_postponed_181_);
lean_ctor_set(v_reuseFailAlloc_207_, 4, v_diag_182_);
v___x_203_ = v_reuseFailAlloc_207_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_st_ref_set(v___y_175_, v___x_203_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object* v_mvarId_211_, lean_object* v_val_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_211_, v_val_212_, v___y_213_);
lean_dec(v___y_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object* v_mvarId_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___x_223_; 
lean_inc(v_mvarId_217_);
v___x_223_ = l_Lean_MVarId_getType(v_mvarId_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_268_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_268_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_268_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_268_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___f_228_; lean_object* v___x_229_; 
v___f_228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
v___x_229_ = lean_find_expr(v___f_228_, v_a_224_);
lean_dec(v_a_224_);
if (lean_obj_tag(v___x_229_) == 1)
{
lean_object* v_val_230_; lean_object* v___x_231_; 
lean_del_object(v___x_226_);
v_val_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_230_);
lean_dec_ref(v___x_229_);
lean_inc(v_mvarId_217_);
v___x_231_ = l_Lean_MVarId_getType(v_mvarId_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref(v___x_231_);
v___x_233_ = l_Lean_Expr_appArg_x21(v_val_230_);
lean_dec(v_val_230_);
v___x_234_ = l_Lean_Meta_mkFalseElim(v_a_232_, v___x_233_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_245_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref(v___x_234_);
v___x_236_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_217_, v_a_235_, v_a_219_);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_236_, 0);
lean_dec(v_unused_246_);
v___x_238_ = v___x_236_;
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
else
{
lean_dec(v___x_236_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_240_ = 1;
v___x_241_ = lean_box(v___x_240_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_241_);
v___x_243_ = v___x_238_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec(v_mvarId_217_);
v_a_247_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_234_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_234_);
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
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec(v_val_230_);
lean_dec(v_mvarId_217_);
v_a_255_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_231_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_231_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
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
uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
lean_dec(v___x_229_);
lean_dec(v_mvarId_217_);
v___x_263_ = 0;
v___x_264_ = lean_box(v___x_263_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_264_);
v___x_266_ = v___x_226_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
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
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_mvarId_217_);
v_a_269_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_223_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_223_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object* v_mvarId_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object* v_mvarId_284_, lean_object* v_val_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_284_, v_val_285_, v___y_287_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object* v_mvarId_292_, lean_object* v_val_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(v_mvarId_292_, v_val_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object* v_00_u03b2_300_, lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_x_301_, v_x_302_, v_x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_305_, lean_object* v_x_306_, size_t v_x_307_, size_t v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_306_, v_x_307_, v_x_308_, v_x_309_, v_x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
size_t v_x_1483__boxed_318_; size_t v_x_1484__boxed_319_; lean_object* v_res_320_; 
v_x_1483__boxed_318_ = lean_unbox_usize(v_x_314_);
lean_dec(v_x_314_);
v_x_1484__boxed_319_ = lean_unbox_usize(v_x_315_);
lean_dec(v_x_315_);
v_res_320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_312_, v_x_313_, v_x_1483__boxed_318_, v_x_1484__boxed_319_, v_x_316_, v_x_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_321_, lean_object* v_n_322_, lean_object* v_k_323_, lean_object* v_v_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v_n_322_, v_k_323_, v_v_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_326_, size_t v_depth_327_, lean_object* v_keys_328_, lean_object* v_vals_329_, lean_object* v_heq_330_, lean_object* v_i_331_, lean_object* v_entries_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_327_, v_keys_328_, v_vals_329_, v_i_331_, v_entries_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_334_, lean_object* v_depth_335_, lean_object* v_keys_336_, lean_object* v_vals_337_, lean_object* v_heq_338_, lean_object* v_i_339_, lean_object* v_entries_340_){
_start:
{
size_t v_depth_boxed_341_; lean_object* v_res_342_; 
v_depth_boxed_341_ = lean_unbox_usize(v_depth_335_);
lean_dec(v_depth_335_);
v_res_342_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_334_, v_depth_boxed_341_, v_keys_336_, v_vals_337_, v_heq_338_, v_i_339_, v_entries_340_);
lean_dec_ref(v_vals_337_);
lean_dec_ref(v_keys_336_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_344_, v_x_345_, v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* v_fvarId_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_FVarId_getType___redArg(v_fvarId_349_, v_a_350_, v_a_352_, v_a_353_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref(v___x_359_);
v___x_361_ = l_Lean_Meta_whnfD(v_a_360_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_388_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_388_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_388_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_388_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Expr_getAppFn(v_a_362_);
lean_dec(v_a_362_);
if (lean_obj_tag(v___x_366_) == 4)
{
lean_object* v_declName_367_; lean_object* v___x_368_; lean_object* v_env_369_; uint8_t v___x_370_; lean_object* v___x_371_; 
v_declName_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_declName_367_);
lean_dec_ref(v___x_366_);
v___x_368_ = lean_st_ref_get(v_a_353_);
v_env_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc_ref(v_env_369_);
lean_dec(v___x_368_);
v___x_370_ = 0;
v___x_371_ = l_Lean_Environment_find_x3f(v_env_369_, v_declName_367_, v___x_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_del_object(v___x_364_);
goto v___jp_355_;
}
else
{
lean_object* v_val_372_; 
v_val_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_372_);
lean_dec_ref(v___x_371_);
if (lean_obj_tag(v_val_372_) == 5)
{
lean_object* v_val_373_; lean_object* v_numIndices_374_; lean_object* v_ctors_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_val_373_ = lean_ctor_get(v_val_372_, 0);
lean_inc_ref(v_val_373_);
lean_dec_ref(v_val_372_);
v_numIndices_374_ = lean_ctor_get(v_val_373_, 2);
lean_inc(v_numIndices_374_);
v_ctors_375_ = lean_ctor_get(v_val_373_, 4);
lean_inc(v_ctors_375_);
lean_dec_ref(v_val_373_);
v___x_376_ = l_List_lengthTR___redArg(v_ctors_375_);
lean_dec(v_ctors_375_);
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_nat_dec_eq(v___x_376_, v___x_377_);
lean_dec(v___x_376_);
if (v___x_378_ == 0)
{
uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_379_ = lean_nat_dec_lt(v___x_377_, v_numIndices_374_);
lean_dec(v_numIndices_374_);
v___x_380_ = lean_box(v___x_379_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_380_);
v___x_382_ = v___x_364_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_386_; 
lean_dec(v_numIndices_374_);
v___x_384_ = lean_box(v___x_378_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_384_);
v___x_386_ = v___x_364_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_dec(v_val_372_);
lean_del_object(v___x_364_);
goto v___jp_355_;
}
}
}
else
{
lean_dec_ref(v___x_366_);
lean_del_object(v___x_364_);
goto v___jp_355_;
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
v_a_389_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_361_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_361_);
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
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
v_a_397_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_359_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_359_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
v___jp_355_:
{
uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = 0;
v___x_357_ = lean_box(v___x_356_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object* v_fvarId_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object* v_s_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Meta_SavedState_restore___redArg(v_s_412_, v___y_415_, v___y_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object* v_s_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(v_s_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v_s_420_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object* v_x_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
lean_inc(v___y_437_);
v___x_443_ = lean_apply_6(v_x_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, lean_box(0));
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object* v_x_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(v_x_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_445_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* v_mvarId_452_, lean_object* v_x_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___f_460_; lean_object* v___x_461_; 
lean_inc(v___y_454_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_460_, 0, v_x_453_);
lean_closure_set(v___f_460_, 1, v___y_454_);
v___x_461_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_452_, v___f_460_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_461_) == 0)
{
return v___x_461_;
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object* v_mvarId_470_, lean_object* v_x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_470_, v_x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object* v_00_u03b1_479_, lean_object* v_mvarId_480_, lean_object* v_x_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_480_, v_x_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object* v_00_u03b1_489_, lean_object* v_mvarId_490_, lean_object* v_x_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(v_00_u03b1_489_, v_mvarId_490_, v_x_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* v_x_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Meta_saveState___redArg(v___y_502_, v___y_504_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___y_509_; lean_object* v___y_510_; uint8_t v___y_511_; lean_object* v___y_530_; lean_object* v_a_531_; lean_object* v___x_534_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
v___x_534_ = lean_apply_6(v_x_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, lean_box(0));
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; uint8_t v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
v___x_536_ = lean_unbox(v_a_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec_ref(v___x_534_);
v___x_537_ = l_Lean_Meta_SavedState_restore___redArg(v_a_507_, v___y_502_, v___y_504_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_a_507_);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v___x_537_, 0);
lean_dec(v_unused_545_);
v___x_539_ = v___x_537_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_dec(v___x_537_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v_a_535_);
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_535_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec(v_a_535_);
v_a_546_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_537_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_537_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
lean_inc(v_a_546_);
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
v___y_530_ = v___x_551_;
v_a_531_ = v_a_546_;
goto v___jp_529_;
}
}
}
}
else
{
lean_dec(v_a_535_);
lean_dec(v_a_507_);
return v___x_534_;
}
}
else
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_554_);
v___y_530_ = v___x_534_;
v_a_531_ = v_a_554_;
goto v___jp_529_;
}
v___jp_508_:
{
if (v___y_511_ == 0)
{
lean_object* v___x_512_; 
lean_dec_ref(v___y_510_);
v___x_512_ = l_Lean_Meta_SavedState_restore___redArg(v_a_507_, v___y_502_, v___y_504_);
lean_dec(v_a_507_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v___x_512_, 0);
lean_dec(v_unused_520_);
v___x_514_ = v___x_512_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_dec(v___x_512_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set_tag(v___x_514_, 1);
lean_ctor_set(v___x_514_, 0, v___y_509_);
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___y_509_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v___y_509_);
v_a_521_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_512_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_512_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_dec_ref(v___y_509_);
lean_dec(v_a_507_);
return v___y_510_;
}
}
v___jp_529_:
{
uint8_t v___x_532_; 
v___x_532_ = l_Lean_Exception_isInterrupt(v_a_531_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; 
lean_inc_ref(v_a_531_);
v___x_533_ = l_Lean_Exception_isRuntime(v_a_531_);
v___y_509_ = v_a_531_;
v___y_510_ = v___y_530_;
v___y_511_ = v___x_533_;
goto v___jp_508_;
}
else
{
v___y_509_ = v_a_531_;
v___y_510_ = v___y_530_;
v___y_511_ = v___x_532_;
goto v___jp_508_;
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref(v_x_499_);
v_a_555_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_506_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_506_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_x_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object* v_msgData_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; lean_object* v_env_578_; lean_object* v___x_579_; lean_object* v_mctx_580_; lean_object* v_lctx_581_; lean_object* v_options_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_577_ = lean_st_ref_get(v___y_575_);
v_env_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_577_);
v___x_579_ = lean_st_ref_get(v___y_573_);
v_mctx_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc_ref(v_mctx_580_);
lean_dec(v___x_579_);
v_lctx_581_ = lean_ctor_get(v___y_572_, 2);
v_options_582_ = lean_ctor_get(v___y_574_, 2);
lean_inc_ref(v_options_582_);
lean_inc_ref(v_lctx_581_);
v___x_583_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_583_, 0, v_env_578_);
lean_ctor_set(v___x_583_, 1, v_mctx_580_);
lean_ctor_set(v___x_583_, 2, v_lctx_581_);
lean_ctor_set(v___x_583_, 3, v_options_582_);
v___x_584_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v_msgData_571_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_592_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_593_; double v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = lean_float_of_nat(v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_598_, lean_object* v_msg_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_ref_605_; lean_object* v___x_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_651_; 
v_ref_605_ = lean_ctor_get(v___y_602_, 5);
v___x_606_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_651_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_651_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_651_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v_traceState_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_cache_617_; lean_object* v_messages_618_; lean_object* v_infoState_619_; lean_object* v_snapshotTasks_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_650_; 
v___x_611_ = lean_st_ref_take(v___y_603_);
v_traceState_612_ = lean_ctor_get(v___x_611_, 4);
v_env_613_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_614_ = lean_ctor_get(v___x_611_, 1);
v_ngen_615_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_616_ = lean_ctor_get(v___x_611_, 3);
v_cache_617_ = lean_ctor_get(v___x_611_, 5);
v_messages_618_ = lean_ctor_get(v___x_611_, 6);
v_infoState_619_ = lean_ctor_get(v___x_611_, 7);
v_snapshotTasks_620_ = lean_ctor_get(v___x_611_, 8);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_650_ == 0)
{
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_650_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_snapshotTasks_620_);
lean_inc(v_infoState_619_);
lean_inc(v_messages_618_);
lean_inc(v_cache_617_);
lean_inc(v_traceState_612_);
lean_inc(v_auxDeclNGen_616_);
lean_inc(v_ngen_615_);
lean_inc(v_nextMacroScope_614_);
lean_inc(v_env_613_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_650_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint64_t v_tid_624_; lean_object* v_traces_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_649_; 
v_tid_624_ = lean_ctor_get_uint64(v_traceState_612_, sizeof(void*)*1);
v_traces_625_ = lean_ctor_get(v_traceState_612_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_traceState_612_);
if (v_isSharedCheck_649_ == 0)
{
v___x_627_ = v_traceState_612_;
v_isShared_628_ = v_isSharedCheck_649_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_traces_625_);
lean_dec(v_traceState_612_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_649_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; double v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_629_ = lean_box(0);
v___x_630_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_631_ = 0;
v___x_632_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_633_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_633_, 0, v_cls_598_);
lean_ctor_set(v___x_633_, 1, v___x_629_);
lean_ctor_set(v___x_633_, 2, v___x_632_);
lean_ctor_set_float(v___x_633_, sizeof(void*)*3, v___x_630_);
lean_ctor_set_float(v___x_633_, sizeof(void*)*3 + 8, v___x_630_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 16, v___x_631_);
v___x_634_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_635_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v_a_607_);
lean_ctor_set(v___x_635_, 2, v___x_634_);
lean_inc(v_ref_605_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v_ref_605_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = l_Lean_PersistentArray_push___redArg(v_traces_625_, v___x_636_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_637_);
v___x_639_ = v___x_627_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_637_);
lean_ctor_set_uint64(v_reuseFailAlloc_648_, sizeof(void*)*1, v_tid_624_);
v___x_639_ = v_reuseFailAlloc_648_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v___x_639_);
v___x_641_ = v___x_622_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_env_613_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_647_, 5, v_cache_617_);
lean_ctor_set(v_reuseFailAlloc_647_, 6, v_messages_618_);
lean_ctor_set(v_reuseFailAlloc_647_, 7, v_infoState_619_);
lean_ctor_set(v_reuseFailAlloc_647_, 8, v_snapshotTasks_620_);
v___x_641_ = v_reuseFailAlloc_647_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_642_ = lean_st_ref_set(v___y_603_, v___x_641_);
v___x_643_ = lean_box(0);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_643_);
v___x_645_ = v___x_609_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_652_, lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_652_, v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_667_, lean_object* v_mvarId_668_, lean_object* v_fields_669_, lean_object* v_sz_670_, lean_object* v___x_671_, lean_object* v___x_672_, lean_object* v___x_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
size_t v_sz_boxed_680_; size_t v___x_18101__boxed_681_; uint8_t v___x_18103__boxed_682_; lean_object* v_res_683_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_670_);
lean_dec(v_sz_670_);
v___x_18101__boxed_681_ = lean_unbox_usize(v___x_671_);
lean_dec(v___x_671_);
v___x_18103__boxed_682_ = lean_unbox(v___x_673_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_667_, v_mvarId_668_, v_fields_669_, v_sz_boxed_680_, v___x_18101__boxed_681_, v___x_672_, v___x_18103__boxed_682_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v_fields_669_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_684_, lean_object* v_as_685_, size_t v_sz_686_, size_t v_i_687_, lean_object* v_b_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
uint8_t v___x_695_; 
v___x_695_ = lean_usize_dec_lt(v_i_687_, v_sz_686_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v_b_688_);
return v___x_696_;
}
else
{
lean_object* v_a_697_; lean_object* v_toInductionSubgoal_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v_b_688_);
v_a_697_ = lean_array_uget(v_as_685_, v_i_687_);
v_toInductionSubgoal_698_ = lean_ctor_get(v_a_697_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_a_697_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v_a_697_, 1);
lean_dec(v_unused_740_);
v___x_700_ = v_a_697_;
v_isShared_701_ = v_isSharedCheck_739_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_toInductionSubgoal_698_);
lean_dec(v_a_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_739_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_mvarId_702_; lean_object* v_fields_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; size_t v_sz_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___f_712_; lean_object* v___x_713_; 
v_mvarId_702_ = lean_ctor_get(v_toInductionSubgoal_698_, 0);
lean_inc_n(v_mvarId_702_, 2);
v_fields_703_ = lean_ctor_get(v_toInductionSubgoal_698_, 1);
lean_inc_ref(v_fields_703_);
v___x_704_ = lean_box(0);
v___x_705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_nat_dec_eq(v_val_684_, v___x_706_);
v_sz_708_ = lean_array_size(v_fields_703_);
v___x_709_ = lean_box_usize(v_sz_708_);
v___x_710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_711_ = lean_box(v___x_707_);
v___f_712_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_712_, 0, v_toInductionSubgoal_698_);
lean_closure_set(v___f_712_, 1, v_mvarId_702_);
lean_closure_set(v___f_712_, 2, v_fields_703_);
lean_closure_set(v___f_712_, 3, v___x_709_);
lean_closure_set(v___f_712_, 4, v___x_710_);
lean_closure_set(v___f_712_, 5, v___x_705_);
lean_closure_set(v___f_712_, 6, v___x_711_);
v___x_713_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_702_, v___f_712_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_730_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_730_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_730_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_730_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
uint8_t v___x_718_; 
v___x_718_ = lean_unbox(v_a_714_);
lean_dec(v_a_714_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_719_ = lean_box(v___x_707_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_704_);
lean_ctor_set(v___x_700_, 0, v___x_720_);
v___x_722_ = v___x_700_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_704_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_722_);
v___x_724_ = v___x_716_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
size_t v___x_727_; size_t v___x_728_; 
lean_del_object(v___x_716_);
lean_del_object(v___x_700_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_687_, v___x_727_);
v_i_687_ = v___x_728_;
v_b_688_ = v___x_705_;
goto _start;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_del_object(v___x_700_);
v_a_731_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_713_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_713_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
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
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_752_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_753_ = l_Lean_Name_append(v___x_752_, v___x_751_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_757_, lean_object* v_fvarId_758_, lean_object* v___x_759_, uint8_t v___x_760_, lean_object* v___x_761_, lean_object* v_val_762_, uint8_t v___x_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_MVarId_cases(v_mvarId_757_, v_fvarId_758_, v___x_759_, v___x_760_, v___x_761_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v_options_804_; uint8_t v_hasTrace_805_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
v_options_804_ = lean_ctor_get(v___y_767_, 2);
v_hasTrace_805_ = lean_ctor_get_uint8(v_options_804_, sizeof(void*)*1);
if (v_hasTrace_805_ == 0)
{
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
v___y_776_ = v___y_767_;
v___y_777_ = v___y_768_;
goto v___jp_772_;
}
else
{
lean_object* v_inheritedTraceOptions_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_inheritedTraceOptions_806_ = lean_ctor_get(v___y_767_, 13);
v___x_807_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_808_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_809_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_806_, v_options_804_, v___x_808_);
if (v___x_809_ == 0)
{
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
v___y_776_ = v___y_767_;
v___y_777_ = v___y_768_;
goto v___jp_772_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_810_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_811_ = lean_array_get_size(v_a_771_);
v___x_812_ = l_Nat_reprFast(v___x_811_);
v___x_813_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
v___x_814_ = l_Lean_MessageData_ofFormat(v___x_813_);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_810_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_807_, v___x_815_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_dec_ref(v___x_816_);
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
v___y_776_ = v___y_767_;
v___y_777_ = v___y_768_;
goto v___jp_772_;
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_a_771_);
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
v___jp_772_:
{
lean_object* v___x_778_; size_t v_sz_779_; size_t v___x_780_; lean_object* v___x_781_; 
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_779_ = lean_array_size(v_a_771_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_762_, v_a_771_, v_sz_779_, v___x_780_, v___x_778_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v_a_771_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_795_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_795_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_795_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_795_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_fst_786_; 
v_fst_786_ = lean_ctor_get(v_a_782_, 0);
lean_inc(v_fst_786_);
lean_dec(v_a_782_);
if (lean_obj_tag(v_fst_786_) == 0)
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_box(v___x_763_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_787_);
v___x_789_ = v___x_784_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
else
{
lean_object* v_val_791_; lean_object* v___x_793_; 
v_val_791_ = lean_ctor_get(v_fst_786_, 0);
lean_inc(v_val_791_);
lean_dec_ref(v_fst_786_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v_val_791_);
v___x_793_ = v___x_784_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_val_791_);
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
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_781_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_781_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_869_; 
v_a_825_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_869_ == 0)
{
v___x_827_ = v___x_770_;
v_isShared_828_ = v_isSharedCheck_869_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_770_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_869_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
uint8_t v___y_830_; uint8_t v___x_867_; 
v___x_867_ = l_Lean_Exception_isInterrupt(v_a_825_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; 
lean_inc(v_a_825_);
v___x_868_ = l_Lean_Exception_isRuntime(v_a_825_);
v___y_830_ = v___x_868_;
goto v___jp_829_;
}
else
{
v___y_830_ = v___x_867_;
goto v___jp_829_;
}
v___jp_829_:
{
if (v___y_830_ == 0)
{
lean_object* v_options_831_; uint8_t v_hasTrace_832_; 
v_options_831_ = lean_ctor_get(v___y_767_, 2);
v_hasTrace_832_ = lean_ctor_get_uint8(v_options_831_, sizeof(void*)*1);
if (v_hasTrace_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v_a_825_);
v___x_833_ = lean_box(v___x_760_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 0);
lean_ctor_set(v___x_827_, 0, v___x_833_);
v___x_835_ = v___x_827_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v_inheritedTraceOptions_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_inheritedTraceOptions_837_ = lean_ctor_get(v___y_767_, 13);
v___x_838_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_839_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_840_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_837_, v_options_831_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_843_; 
lean_dec(v_a_825_);
v___x_841_ = lean_box(v___x_760_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 0);
lean_ctor_set(v___x_827_, 0, v___x_841_);
v___x_843_ = v___x_827_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_del_object(v___x_827_);
v___x_845_ = l_Lean_Exception_toMessageData(v_a_825_);
v___x_846_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_838_, v___x_845_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v___x_846_, 0);
lean_dec(v_unused_855_);
v___x_848_ = v___x_846_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_dec(v___x_846_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_box(v___x_760_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_846_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_846_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
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
else
{
lean_object* v___x_865_; 
if (v_isShared_828_ == 0)
{
v___x_865_ = v___x_827_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_825_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_870_, lean_object* v_fvarId_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v_val_875_, lean_object* v___x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v___x_18223__boxed_883_; uint8_t v___x_18226__boxed_884_; lean_object* v_res_885_; 
v___x_18223__boxed_883_ = lean_unbox(v___x_873_);
v___x_18226__boxed_884_ = lean_unbox(v___x_876_);
v_res_885_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_870_, v_fvarId_871_, v___x_872_, v___x_18223__boxed_883_, v___x_874_, v_val_875_, v___x_18226__boxed_884_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec(v_val_875_);
return v_res_885_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_889_, lean_object* v_fvarId_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_st_ref_get(v_a_891_);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_nat_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; 
v___x_904_ = lean_st_ref_take(v_a_891_);
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_sub(v___x_904_, v___x_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_st_ref_set(v_a_891_, v___x_906_);
v___x_908_ = 1;
v___x_909_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_910_ = lean_box(0);
v___x_911_ = lean_box(v___x_903_);
v___x_912_ = lean_box(v___x_908_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_913_, 0, v_mvarId_889_);
lean_closure_set(v___f_913_, 1, v_fvarId_890_);
lean_closure_set(v___f_913_, 2, v___x_909_);
lean_closure_set(v___f_913_, 3, v___x_911_);
lean_closure_set(v___f_913_, 4, v___x_910_);
lean_closure_set(v___f_913_, 5, v___x_901_);
lean_closure_set(v___f_913_, 6, v___x_912_);
v___x_914_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_913_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_914_;
}
else
{
lean_object* v_options_915_; uint8_t v_hasTrace_916_; 
lean_dec(v___x_901_);
lean_dec(v_fvarId_890_);
lean_dec(v_mvarId_889_);
v_options_915_ = lean_ctor_get(v_a_894_, 2);
v_hasTrace_916_ = lean_ctor_get_uint8(v_options_915_, sizeof(void*)*1);
if (v_hasTrace_916_ == 0)
{
goto v___jp_897_;
}
else
{
lean_object* v_inheritedTraceOptions_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_inheritedTraceOptions_917_ = lean_ctor_get(v_a_894_, 13);
v___x_918_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_919_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_917_, v_options_915_, v___x_919_);
if (v___x_920_ == 0)
{
goto v___jp_897_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_922_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_918_, v___x_921_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_dec_ref(v___x_922_);
goto v___jp_897_;
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
v___jp_897_:
{
uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = 0;
v___x_899_ = lean_box(v___x_898_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_931_, lean_object* v___x_932_, lean_object* v_as_933_, size_t v_sz_934_, size_t v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_a_944_; uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_lt(v_i_935_, v_sz_934_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec(v___x_932_);
lean_dec_ref(v___x_931_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_b_936_);
return v___x_949_;
}
else
{
lean_object* v_subst_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_a_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
lean_dec_ref(v_b_936_);
v_subst_950_ = lean_ctor_get(v___x_931_, 2);
v___x_951_ = lean_box(0);
v___x_952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_953_ = lean_array_uget_borrowed(v_as_933_, v_i_935_);
lean_inc(v_subst_950_);
v___x_954_ = l_Lean_Meta_FVarSubst_apply(v_subst_950_, v_a_953_);
v___x_955_ = l_Lean_Expr_isFVar(v___x_954_);
if (v___x_955_ == 0)
{
lean_dec_ref(v___x_954_);
v_a_944_ = v___x_952_;
goto v___jp_943_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = l_Lean_Expr_fvarId_x21(v___x_954_);
lean_dec_ref(v___x_954_);
lean_inc(v___x_956_);
v___x_957_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_956_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; uint8_t v___x_959_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_957_);
v___x_959_ = lean_unbox(v_a_958_);
lean_dec(v_a_958_);
if (v___x_959_ == 0)
{
lean_dec(v___x_956_);
v_a_944_ = v___x_952_;
goto v___jp_943_;
}
else
{
lean_object* v___x_960_; 
lean_inc(v___x_932_);
v___x_960_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_932_, v___x_956_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_971_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_971_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_971_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
uint8_t v___x_965_; 
v___x_965_ = lean_unbox(v_a_961_);
if (v___x_965_ == 0)
{
lean_del_object(v___x_963_);
lean_dec(v_a_961_);
v_a_944_ = v___x_952_;
goto v___jp_943_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
lean_dec(v___x_932_);
lean_dec_ref(v___x_931_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v_a_961_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_951_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_967_);
v___x_969_ = v___x_963_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v___x_932_);
lean_dec_ref(v___x_931_);
v_a_972_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_960_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_960_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v___x_956_);
lean_dec(v___x_932_);
lean_dec_ref(v___x_931_);
v_a_980_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_957_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_957_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
v___jp_943_:
{
size_t v___x_945_; size_t v___x_946_; 
v___x_945_ = ((size_t)1ULL);
v___x_946_ = lean_usize_add(v_i_935_, v___x_945_);
lean_inc_ref(v_a_944_);
v_i_935_ = v___x_946_;
v_b_936_ = v_a_944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_988_, lean_object* v_mvarId_989_, lean_object* v_fields_990_, size_t v_sz_991_, size_t v___x_992_, lean_object* v___x_993_, uint8_t v___x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_988_, v_mvarId_989_, v_fields_990_, v_sz_991_, v___x_992_, v___x_993_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1015_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1015_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1015_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_fst_1006_; 
v_fst_1006_ = lean_ctor_get(v_a_1002_, 0);
lean_inc(v_fst_1006_);
lean_dec(v_a_1002_);
if (lean_obj_tag(v_fst_1006_) == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = lean_box(v___x_994_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1007_);
v___x_1009_ = v___x_1004_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
else
{
lean_object* v_val_1011_; lean_object* v___x_1013_; 
v_val_1011_ = lean_ctor_get(v_fst_1006_, 0);
lean_inc(v_val_1011_);
lean_dec_ref(v_fst_1006_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_val_1011_);
v___x_1013_ = v___x_1004_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_val_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
v_a_1016_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1001_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1001_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1024_, lean_object* v_as_1025_, lean_object* v_sz_1026_, lean_object* v_i_1027_, lean_object* v_b_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1026_);
lean_dec(v_sz_1026_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1027_);
lean_dec(v_i_1027_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1024_, v_as_1025_, v_sz_boxed_1035_, v_i_boxed_1036_, v_b_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v_as_1025_);
lean_dec(v_val_1024_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1038_, lean_object* v___x_1039_, lean_object* v_as_1040_, lean_object* v_sz_1041_, lean_object* v_i_1042_, lean_object* v_b_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
size_t v_sz_boxed_1050_; size_t v_i_boxed_1051_; lean_object* v_res_1052_; 
v_sz_boxed_1050_ = lean_unbox_usize(v_sz_1041_);
lean_dec(v_sz_1041_);
v_i_boxed_1051_ = lean_unbox_usize(v_i_1042_);
lean_dec(v_i_1042_);
v_res_1052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1038_, v___x_1039_, v_as_1040_, v_sz_boxed_1050_, v_i_boxed_1051_, v_b_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v_as_1040_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1053_, lean_object* v_fvarId_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1053_, v_fvarId_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1062_, lean_object* v_msg_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1062_, v_msg_1063_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1071_, lean_object* v_msg_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1071_, v_msg_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Meta_saveState___redArg(v___y_1082_, v___y_1084_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v___y_1091_; lean_object* v___y_1110_; lean_object* v_a_1111_; lean_object* v___x_1114_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref(v___x_1086_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
v___x_1114_ = lean_apply_5(v_x_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, lean_box(0));
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; uint8_t v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
v___x_1116_ = lean_unbox(v_a_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v___x_1114_);
v___x_1117_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1087_, v___y_1082_, v___y_1084_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_a_1087_);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v___x_1117_, 0);
lean_dec(v_unused_1125_);
v___x_1119_ = v___x_1117_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_dec(v___x_1117_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v_a_1115_);
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1115_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_a_1115_);
v_a_1126_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1117_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
lean_inc(v_a_1126_);
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
v___y_1110_ = v___x_1131_;
v_a_1111_ = v_a_1126_;
goto v___jp_1109_;
}
}
}
}
else
{
lean_dec(v_a_1115_);
lean_dec(v_a_1087_);
return v___x_1114_;
}
}
else
{
lean_object* v_a_1134_; 
v_a_1134_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1134_);
v___y_1110_ = v___x_1114_;
v_a_1111_ = v_a_1134_;
goto v___jp_1109_;
}
v___jp_1088_:
{
if (v___y_1091_ == 0)
{
lean_object* v___x_1092_; 
lean_dec_ref(v___y_1090_);
v___x_1092_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1087_, v___y_1082_, v___y_1084_);
lean_dec(v_a_1087_);
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
lean_ctor_set(v___x_1094_, 0, v___y_1089_);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___y_1089_);
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
lean_dec_ref(v___y_1089_);
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
lean_dec_ref(v___y_1089_);
lean_dec(v_a_1087_);
return v___y_1090_;
}
}
v___jp_1109_:
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Lean_Exception_isInterrupt(v_a_1111_);
if (v___x_1112_ == 0)
{
uint8_t v___x_1113_; 
lean_inc_ref(v_a_1111_);
v___x_1113_ = l_Lean_Exception_isRuntime(v_a_1111_);
v___y_1089_ = v_a_1111_;
v___y_1090_ = v___y_1110_;
v___y_1091_ = v___x_1113_;
goto v___jp_1088_;
}
else
{
v___y_1089_ = v_a_1111_;
v___y_1090_ = v___y_1110_;
v___y_1091_ = v___x_1112_;
goto v___jp_1088_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v_x_1080_);
v_a_1135_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1086_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1086_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1150_, lean_object* v_x_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1150_, v_x_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1157_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1157_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1174_, v_x_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1182_, lean_object* v_mvarId_1183_, lean_object* v_x_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1183_, v_x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_mvarId_1192_, lean_object* v_x_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1191_, v_mvarId_1192_, v_x_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1200_, lean_object* v_fuel_1201_, lean_object* v_fvarId_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_MVarId_exfalso(v_mvarId_1200_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref(v___x_1208_);
v___x_1210_ = lean_st_mk_ref(v_fuel_1201_);
v___x_1211_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1209_, v_fvarId_1202_, v___x_1210_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1220_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_st_ref_get(v___x_1210_);
lean_dec(v___x_1210_);
lean_dec(v___x_1216_);
if (v_isShared_1215_ == 0)
{
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1212_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_dec(v___x_1210_);
return v___x_1211_;
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_fvarId_1202_);
lean_dec(v_fuel_1201_);
v_a_1221_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1208_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1208_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1229_, lean_object* v_fuel_1230_, lean_object* v_fvarId_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1229_, v_fuel_1230_, v_fvarId_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1238_, lean_object* v___f_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1238_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; uint8_t v___x_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
v___x_1247_ = lean_unbox(v_a_1246_);
lean_dec(v_a_1246_);
if (v___x_1247_ == 0)
{
lean_dec_ref(v___f_1239_);
return v___x_1245_;
}
else
{
lean_object* v___x_1248_; 
lean_dec_ref(v___x_1245_);
v___x_1248_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1248_;
}
}
else
{
lean_dec_ref(v___f_1239_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1249_, lean_object* v___f_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1249_, v___f_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1257_, lean_object* v_fvarId_1258_, lean_object* v_fuel_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; 
lean_inc(v_fvarId_1258_);
lean_inc(v_mvarId_1257_);
v___f_1265_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1265_, 0, v_mvarId_1257_);
lean_closure_set(v___f_1265_, 1, v_fuel_1259_);
lean_closure_set(v___f_1265_, 2, v_fvarId_1258_);
v___f_1266_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1266_, 0, v_fvarId_1258_);
lean_closure_set(v___f_1266_, 1, v___f_1265_);
v___x_1267_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1257_, v___f_1266_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1268_, lean_object* v_fvarId_1269_, lean_object* v_fuel_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1268_, v_fvarId_1269_, v_fuel_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1277_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1279_){
_start:
{
uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1279_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1282_, lean_object* v_acc_1283_){
_start:
{
if (lean_obj_tag(v_e_1282_) == 7)
{
lean_object* v_binderType_1284_; lean_object* v_body_1285_; uint8_t v___y_1287_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_binderType_1284_ = lean_ctor_get(v_e_1282_, 1);
v_body_1285_ = lean_ctor_get(v_e_1282_, 2);
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_expr_has_loose_bvar(v_body_1285_, v___x_1291_);
if (v___x_1292_ == 0)
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_Expr_isEq(v_binderType_1284_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Expr_isHEq(v_binderType_1284_);
v___y_1287_ = v___x_1294_;
goto v___jp_1286_;
}
else
{
v___y_1287_ = v___x_1293_;
goto v___jp_1286_;
}
}
else
{
uint8_t v___x_1295_; 
v___x_1295_ = 0;
v___y_1287_ = v___x_1295_;
goto v___jp_1286_;
}
v___jp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_box(v___y_1287_);
v___x_1289_ = lean_array_push(v_acc_1283_, v___x_1288_);
v_e_1282_ = v_body_1285_;
v_acc_1283_ = v___x_1289_;
goto _start;
}
}
else
{
return v_acc_1283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1296_, lean_object* v_acc_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1296_, v_acc_1297_);
lean_dec_ref(v_e_1296_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1301_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1303_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1301_, v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_mkGenDiseqMask(v_e_1304_);
lean_dec_ref(v_e_1304_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___f_1313_; lean_object* v___x_5507__overap_1314_; lean_object* v___x_1315_; 
v___f_1313_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_5507__overap_1314_ = lean_panic_fn_borrowed(v___f_1313_, v_msg_1307_);
lean_inc(v___y_1311_);
lean_inc_ref(v___y_1310_);
lean_inc(v___y_1309_);
lean_inc_ref(v___y_1308_);
v___x_1315_ = lean_apply_5(v___x_5507__overap_1314_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, lean_box(0));
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Lean_Expr_hasMVar(v_e_1323_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_e_1323_);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; lean_object* v_mctx_1329_; lean_object* v___x_1330_; lean_object* v_fst_1331_; lean_object* v_snd_1332_; lean_object* v___x_1333_; lean_object* v_cache_1334_; lean_object* v_zetaDeltaFVarIds_1335_; lean_object* v_postponed_1336_; lean_object* v_diag_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1346_; 
v___x_1328_ = lean_st_ref_get(v___y_1324_);
v_mctx_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc_ref(v_mctx_1329_);
lean_dec(v___x_1328_);
v___x_1330_ = l_Lean_instantiateMVarsCore(v_mctx_1329_, v_e_1323_);
v_fst_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_fst_1331_);
v_snd_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_snd_1332_);
lean_dec_ref(v___x_1330_);
v___x_1333_ = lean_st_ref_take(v___y_1324_);
v_cache_1334_ = lean_ctor_get(v___x_1333_, 1);
v_zetaDeltaFVarIds_1335_ = lean_ctor_get(v___x_1333_, 2);
v_postponed_1336_ = lean_ctor_get(v___x_1333_, 3);
v_diag_1337_ = lean_ctor_get(v___x_1333_, 4);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v___x_1333_, 0);
lean_dec(v_unused_1347_);
v___x_1339_ = v___x_1333_;
v_isShared_1340_ = v_isSharedCheck_1346_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_diag_1337_);
lean_inc(v_postponed_1336_);
lean_inc(v_zetaDeltaFVarIds_1335_);
lean_inc(v_cache_1334_);
lean_dec(v___x_1333_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1346_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_snd_1332_);
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_snd_1332_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_cache_1334_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_zetaDeltaFVarIds_1335_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_postponed_1336_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_diag_1337_);
v___x_1342_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_st_ref_set(v___y_1324_, v___x_1342_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_fst_1331_);
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1348_, v___y_1349_);
lean_dec(v___y_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1352_, v___y_1354_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1366_, uint8_t v_allowLevelAssignments_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1367_, v_k_1366_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
v_a_1382_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1373_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1373_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1390_, lean_object* v_allowLevelAssignments_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1397_; lean_object* v_res_1398_; 
v_allowLevelAssignments_boxed_1397_ = lean_unbox(v_allowLevelAssignments_1391_);
v_res_1398_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1390_, v_allowLevelAssignments_boxed_1397_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1399_, lean_object* v_k_1400_, uint8_t v_allowLevelAssignments_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1400_, v_allowLevelAssignments_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1408_, lean_object* v_k_1409_, lean_object* v_allowLevelAssignments_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1416_; lean_object* v_res_1417_; 
v_allowLevelAssignments_boxed_1416_ = lean_unbox(v_allowLevelAssignments_1410_);
v_res_1417_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1408_, v_k_1409_, v_allowLevelAssignments_boxed_1416_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1420_, size_t v_sz_1421_, size_t v_i_1422_, lean_object* v_b_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_a_1430_; uint8_t v___x_1434_; 
v___x_1434_ = lean_usize_dec_lt(v_i_1422_, v_sz_1421_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_b_1423_);
return v___x_1435_;
}
else
{
lean_object* v_snd_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1598_; 
v_snd_1436_ = lean_ctor_get(v_b_1423_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_b_1423_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v_b_1423_, 0);
lean_dec(v_unused_1599_);
v___x_1438_ = v_b_1423_;
v_isShared_1439_ = v_isSharedCheck_1598_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_snd_1436_);
lean_dec(v_b_1423_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1598_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_array_1440_; lean_object* v_start_1441_; lean_object* v_stop_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_array_1440_ = lean_ctor_get(v_snd_1436_, 0);
v_start_1441_ = lean_ctor_get(v_snd_1436_, 1);
v_stop_1442_ = lean_ctor_get(v_snd_1436_, 2);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_nat_dec_lt(v_start_1441_, v_stop_1442_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1446_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1443_);
v___x_1446_ = v___x_1438_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_snd_1436_);
v___x_1446_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
}
else
{
lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1594_; 
lean_inc(v_stop_1442_);
lean_inc(v_start_1441_);
lean_inc_ref(v_array_1440_);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_snd_1436_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; lean_object* v_unused_1596_; lean_object* v_unused_1597_; 
v_unused_1595_ = lean_ctor_get(v_snd_1436_, 2);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_snd_1436_, 1);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_snd_1436_, 0);
lean_dec(v_unused_1597_);
v___x_1450_ = v_snd_1436_;
v_isShared_1451_ = v_isSharedCheck_1594_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v_snd_1436_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1594_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1452_ = lean_array_fget(v_array_1440_, v_start_1441_);
v___x_1453_ = lean_unsigned_to_nat(1u);
v___x_1454_ = lean_nat_add(v_start_1441_, v___x_1453_);
lean_dec(v_start_1441_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 1, v___x_1454_);
v___x_1456_ = v___x_1450_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_array_1440_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_stop_1442_);
v___x_1456_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_unbox(v___x_1452_);
lean_dec(v___x_1452_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1459_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 1, v___x_1456_);
lean_ctor_set(v___x_1438_, 0, v___x_1443_);
v___x_1459_ = v___x_1438_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1456_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
v_a_1430_ = v___x_1459_;
goto v___jp_1429_;
}
}
else
{
lean_object* v_a_1461_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___x_1533_; 
v_a_1461_ = lean_array_uget_borrowed(v_as_1420_, v_i_1422_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
lean_inc(v_a_1461_);
v___x_1533_ = lean_infer_type(v_a_1461_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = l_Lean_Meta_matchEq_x3f(v_a_1534_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___x_1535_);
if (lean_obj_tag(v_a_1536_) == 1)
{
lean_object* v_val_1537_; lean_object* v_snd_1538_; lean_object* v_fst_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1575_; 
v_val_1537_ = lean_ctor_get(v_a_1536_, 0);
lean_inc(v_val_1537_);
lean_dec_ref(v_a_1536_);
v_snd_1538_ = lean_ctor_get(v_val_1537_, 1);
lean_inc(v_snd_1538_);
lean_dec(v_val_1537_);
v_fst_1539_ = lean_ctor_get(v_snd_1538_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_snd_1538_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_snd_1538_, 1);
lean_dec(v_unused_1576_);
v___x_1541_ = v_snd_1538_;
v_isShared_1542_ = v_isSharedCheck_1575_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_fst_1539_);
lean_dec(v_snd_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1575_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Meta_mkEqRefl(v_fst_1539_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1543_);
lean_inc(v_a_1461_);
v___x_1545_ = l_Lean_Meta_isExprDefEq(v_a_1461_, v_a_1544_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1558_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1558_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1558_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_unbox(v_a_1546_);
lean_dec(v_a_1546_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
lean_del_object(v___x_1438_);
v___x_1551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 1, v___x_1456_);
lean_ctor_set(v___x_1541_, 0, v___x_1551_);
v___x_1553_ = v___x_1541_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1456_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1553_);
v___x_1555_ = v___x_1548_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
lean_del_object(v___x_1548_);
lean_del_object(v___x_1541_);
v___y_1463_ = v___y_1424_;
v___y_1464_ = v___y_1425_;
v___y_1465_ = v___y_1426_;
v___y_1466_ = v___y_1427_;
goto v___jp_1462_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_del_object(v___x_1541_);
lean_dec_ref(v___x_1456_);
lean_del_object(v___x_1438_);
v_a_1559_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1545_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1545_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_del_object(v___x_1541_);
lean_dec_ref(v___x_1456_);
lean_del_object(v___x_1438_);
v_a_1567_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1543_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1543_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
else
{
lean_dec(v_a_1536_);
v___y_1463_ = v___y_1424_;
v___y_1464_ = v___y_1425_;
v___y_1465_ = v___y_1426_;
v___y_1466_ = v___y_1427_;
goto v___jp_1462_;
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v___x_1456_);
lean_del_object(v___x_1438_);
v_a_1577_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1535_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1535_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v___x_1456_);
lean_del_object(v___x_1438_);
v_a_1585_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1533_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1533_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
v___jp_1462_:
{
lean_object* v___x_1467_; 
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v_a_1461_);
v___x_1467_ = lean_infer_type(v_a_1461_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1469_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref(v___x_1467_);
v___x_1469_ = l_Lean_Meta_matchHEq_x3f(v_a_1468_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___x_1469_);
if (lean_obj_tag(v_a_1470_) == 1)
{
lean_object* v_val_1471_; lean_object* v_snd_1472_; lean_object* v_fst_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1512_; 
lean_del_object(v___x_1438_);
v_val_1471_ = lean_ctor_get(v_a_1470_, 0);
lean_inc(v_val_1471_);
lean_dec_ref(v_a_1470_);
v_snd_1472_ = lean_ctor_get(v_val_1471_, 1);
lean_inc(v_snd_1472_);
lean_dec(v_val_1471_);
v_fst_1473_ = lean_ctor_get(v_snd_1472_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_snd_1472_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_snd_1472_, 1);
lean_dec(v_unused_1513_);
v___x_1475_ = v_snd_1472_;
v_isShared_1476_ = v_isSharedCheck_1512_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_fst_1473_);
lean_dec(v_snd_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1512_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Meta_mkHEqRefl(v_fst_1473_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1477_);
lean_inc(v_a_1461_);
v___x_1479_ = l_Lean_Meta_isExprDefEq(v_a_1461_, v_a_1478_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1495_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1495_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1495_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
uint8_t v___x_1484_; 
v___x_1484_ = lean_unbox(v_a_1480_);
lean_dec(v_a_1480_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1456_);
lean_ctor_set(v___x_1475_, 0, v___x_1485_);
v___x_1487_ = v___x_1475_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1456_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1487_);
v___x_1489_ = v___x_1482_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
else
{
lean_object* v___x_1493_; 
lean_del_object(v___x_1482_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1456_);
lean_ctor_set(v___x_1475_, 0, v___x_1443_);
v___x_1493_ = v___x_1475_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1456_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
v_a_1430_ = v___x_1493_;
goto v___jp_1429_;
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_del_object(v___x_1475_);
lean_dec_ref(v___x_1456_);
v_a_1496_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1479_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1479_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_del_object(v___x_1475_);
lean_dec_ref(v___x_1456_);
v_a_1504_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1477_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1477_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v___x_1515_; 
lean_dec(v_a_1470_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 1, v___x_1456_);
lean_ctor_set(v___x_1438_, 0, v___x_1443_);
v___x_1515_ = v___x_1438_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1456_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
v_a_1430_ = v___x_1515_;
goto v___jp_1429_;
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v___x_1456_);
lean_del_object(v___x_1438_);
v_a_1517_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1469_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1469_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec_ref(v___x_1456_);
lean_del_object(v___x_1438_);
v_a_1525_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1467_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1467_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
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
v___jp_1429_:
{
size_t v___x_1431_; size_t v___x_1432_; 
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_add(v_i_1422_, v___x_1431_);
v_i_1422_ = v___x_1432_;
v_b_1423_ = v_a_1430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1600_, lean_object* v_sz_1601_, lean_object* v_i_1602_, lean_object* v_b_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
size_t v_sz_boxed_1609_; size_t v_i_boxed_1610_; lean_object* v_res_1611_; 
v_sz_boxed_1609_ = lean_unbox_usize(v_sz_1601_);
lean_dec(v_sz_1601_);
v_i_boxed_1610_ = lean_unbox_usize(v_i_1602_);
lean_dec(v_i_1602_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1600_, v_sz_boxed_1609_, v_i_boxed_1610_, v_b_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec_ref(v_as_1600_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1612_, uint8_t v___x_1613_, lean_object* v_localDecl_1614_, lean_object* v_mvarId_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
lean_inc_ref(v___x_1612_);
v___x_1621_ = l_Lean_Meta_forallMetaTelescope(v___x_1612_, v___x_1613_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v_fst_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1712_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref(v___x_1621_);
v_fst_1623_ = lean_ctor_get(v_a_1622_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_a_1622_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; 
v_unused_1713_ = lean_ctor_get(v_a_1622_, 1);
lean_dec(v_unused_1713_);
v___x_1625_ = v_a_1622_;
v_isShared_1626_ = v_isSharedCheck_1712_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_fst_1623_);
lean_dec(v_a_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1712_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1627_ = l_Lean_Meta_mkGenDiseqMask(v___x_1612_);
lean_dec_ref(v___x_1612_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = lean_array_get_size(v___x_1627_);
v___x_1630_ = l_Array_toSubarray___redArg(v___x_1627_, v___x_1628_, v___x_1629_);
v___x_1631_ = lean_box(0);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 1, v___x_1630_);
lean_ctor_set(v___x_1625_, 0, v___x_1631_);
v___x_1633_ = v___x_1625_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1630_);
v___x_1633_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
size_t v_sz_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
v_sz_1634_ = lean_array_size(v_fst_1623_);
v___x_1635_ = ((size_t)0ULL);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1623_, v_sz_1634_, v___x_1635_, v___x_1633_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1702_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1702_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1702_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v_fst_1641_; 
v_fst_1641_ = lean_ctor_get(v_a_1637_, 0);
lean_inc(v_fst_1641_);
lean_dec(v_a_1637_);
if (lean_obj_tag(v_fst_1641_) == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1697_; 
lean_del_object(v___x_1639_);
v___x_1642_ = l_Lean_LocalDecl_toExpr(v_localDecl_1614_);
v___x_1643_ = l_Lean_mkAppN(v___x_1642_, v_fst_1623_);
lean_dec(v_fst_1623_);
v___x_1644_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1643_, v___y_1617_);
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1697_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1697_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; 
lean_inc(v_a_1645_);
v___x_1649_ = l_Lean_Meta_hasAssignableMVar(v_a_1645_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1688_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1688_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1688_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
uint8_t v___x_1654_; 
v___x_1654_ = lean_unbox(v_a_1650_);
lean_dec(v_a_1650_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_del_object(v___x_1652_);
v___x_1655_ = l_Lean_MVarId_getType(v_mvarId_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v___x_1655_);
v___x_1657_ = l_Lean_Meta_mkFalseElim(v_a_1656_, v_a_1645_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1668_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1668_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1668_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
lean_ctor_set(v___x_1647_, 0, v_a_1658_);
v___x_1663_ = v___x_1647_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1663_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_del_object(v___x_1647_);
v_a_1669_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1657_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1657_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_del_object(v___x_1647_);
lean_dec(v_a_1645_);
v_a_1677_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1655_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1655_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
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
lean_object* v___x_1686_; 
lean_del_object(v___x_1647_);
lean_dec(v_a_1645_);
lean_dec(v_mvarId_1615_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1631_);
v___x_1686_ = v___x_1652_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1631_);
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
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_del_object(v___x_1647_);
lean_dec(v_a_1645_);
lean_dec(v_mvarId_1615_);
v_a_1689_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1649_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1649_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
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
}
else
{
lean_object* v_val_1698_; lean_object* v___x_1700_; 
lean_dec(v_fst_1623_);
lean_dec(v_mvarId_1615_);
lean_dec_ref(v_localDecl_1614_);
v_val_1698_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_val_1698_);
lean_dec_ref(v_fst_1641_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_val_1698_);
v___x_1700_ = v___x_1639_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_val_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_fst_1623_);
lean_dec(v_mvarId_1615_);
lean_dec_ref(v_localDecl_1614_);
v_a_1703_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1636_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1636_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_mvarId_1615_);
lean_dec_ref(v_localDecl_1614_);
lean_dec_ref(v___x_1612_);
v_a_1714_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1621_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1621_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1722_, lean_object* v___x_1723_, lean_object* v_localDecl_1724_, lean_object* v_mvarId_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v___x_7188__boxed_1731_; lean_object* v_res_1732_; 
v___x_7188__boxed_1731_ = lean_unbox(v___x_1723_);
v_res_1732_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1722_, v___x_7188__boxed_1731_, v_localDecl_1724_, v_mvarId_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
return v_res_1732_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1737_ = lean_unsigned_to_nat(2u);
v___x_1738_ = lean_unsigned_to_nat(120u);
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1741_ = l_mkPanicMessageWithDecl(v___x_1740_, v___x_1739_, v___x_1738_, v___x_1737_, v___x_1736_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1742_, lean_object* v_localDecl_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = l_Lean_LocalDecl_type(v_localDecl_1743_);
lean_inc_ref(v___x_1749_);
v___x_1750_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec_ref(v___x_1749_);
lean_dec_ref(v_localDecl_1743_);
lean_dec(v_mvarId_1742_);
v___x_1751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1752_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1751_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
return v___x_1752_;
}
else
{
uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___f_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1753_ = 0;
v___x_1754_ = lean_box(v___x_1753_);
lean_inc(v_mvarId_1742_);
v___f_1755_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1755_, 0, v___x_1749_);
lean_closure_set(v___f_1755_, 1, v___x_1754_);
lean_closure_set(v___f_1755_, 2, v_localDecl_1743_);
lean_closure_set(v___f_1755_, 3, v_mvarId_1742_);
v___x_1756_ = 0;
v___x_1757_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1755_, v___x_1756_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1777_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1777_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1777_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
if (lean_obj_tag(v_a_1758_) == 1)
{
lean_object* v_val_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1771_; 
lean_del_object(v___x_1760_);
v_val_1762_ = lean_ctor_get(v_a_1758_, 0);
lean_inc(v_val_1762_);
lean_dec_ref(v_a_1758_);
v___x_1763_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1742_, v_val_1762_, v_a_1745_);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v___x_1763_, 0);
lean_dec(v_unused_1772_);
v___x_1765_ = v___x_1763_;
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v___x_1763_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_box(v___x_1750_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1769_ = v___x_1765_;
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
else
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
lean_dec(v_a_1758_);
lean_dec(v_mvarId_1742_);
v___x_1773_ = lean_box(v___x_1756_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1773_);
v___x_1775_ = v___x_1760_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
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
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_mvarId_1742_);
v_a_1778_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1757_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1757_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1786_, lean_object* v_localDecl_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1786_, v_localDecl_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1793_;
}
}
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1(void){
_start:
{
uint8_t v___x_1797_; uint64_t v___x_1798_; 
v___x_1797_ = 1;
v___x_1798_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = lean_box(0);
v___x_1808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6));
v___x_1809_ = l_Lean_mkConst(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8(void){
_start:
{
lean_object* v___x_1810_; lean_object* v_dummy_1811_; 
v___x_1810_ = lean_box(0);
v_dummy_1811_ = l_Lean_Expr_sort___override(v___x_1810_);
return v_dummy_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1812_, lean_object* v_mvarId_1813_, lean_object* v_as_1814_, size_t v_sz_1815_, size_t v_i_1816_, lean_object* v_b_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_lt(v_i_1816_, v_sz_1815_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_b_1817_);
return v___x_1824_;
}
else
{
lean_object* v_snd_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_2493_; 
v_snd_1825_ = lean_ctor_get(v_b_1817_, 1);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_b_1817_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v_b_1817_, 0);
lean_dec(v_unused_2494_);
v___x_1827_ = v_b_1817_;
v_isShared_1828_ = v_isSharedCheck_2493_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_snd_1825_);
lean_dec(v_b_1817_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_2493_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_a_1830_; lean_object* v___x_1836_; lean_object* v_a_1838_; lean_object* v_a_1843_; 
v___x_1836_ = lean_box(0);
v_a_1843_ = lean_array_uget(v_as_1814_, v_i_1816_);
if (lean_obj_tag(v_a_1843_) == 0)
{
lean_del_object(v___x_1827_);
v_a_1838_ = v_snd_1825_;
goto v___jp_1837_;
}
else
{
lean_object* v_val_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_2492_; 
v_val_1844_ = lean_ctor_get(v_a_1843_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_a_1843_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_1846_ = v_a_1843_;
v_isShared_1847_ = v_isSharedCheck_2492_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_val_1844_);
lean_dec(v_a_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_2492_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___x_1889_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; uint8_t v___y_1916_; uint8_t v___x_1917_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; uint8_t v___y_1923_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; uint8_t v___y_1929_; uint8_t v___y_1930_; uint8_t v___y_1932_; uint8_t v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; uint8_t v___y_1943_; uint8_t v___y_1944_; lean_object* v___y_1945_; uint8_t v___y_1946_; 
v___x_1848_ = lean_box(0);
v___x_1889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1917_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1844_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1961_; uint8_t v___y_1963_; uint8_t v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; uint8_t v___y_1977_; uint8_t v___y_1978_; uint8_t v___y_1979_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; uint8_t v___y_1986_; uint8_t v___y_1987_; lean_object* v_a_1988_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; uint8_t v___y_1996_; uint8_t v___y_1997_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; uint8_t v___y_2087_; uint8_t v___y_2088_; uint8_t v___y_2089_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; uint8_t v___y_2096_; uint8_t v___y_2097_; uint8_t v___y_2098_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; uint8_t v___y_2106_; uint8_t v___y_2107_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; uint8_t v___y_2124_; uint8_t v___y_2125_; uint8_t v___y_2126_; uint8_t v___y_2128_; uint8_t v_isHEq_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; uint8_t v___y_2142_; lean_object* v___y_2143_; uint8_t v_isEq_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___x_2429_; 
v___x_1961_ = l_Lean_LocalDecl_type(v_val_1844_);
lean_inc_ref(v___x_1961_);
v___x_2429_ = l_Lean_Meta_matchNot_x3f(v___x_1961_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref(v___x_2429_);
if (lean_obj_tag(v_a_2430_) == 1)
{
lean_object* v_val_2431_; lean_object* v___x_2432_; 
v_val_2431_ = lean_ctor_get(v_a_2430_, 0);
lean_inc(v_val_2431_);
lean_dec_ref(v_a_2430_);
v___x_2432_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2431_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref(v___x_2432_);
if (lean_obj_tag(v_a_2433_) == 1)
{
lean_object* v_val_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2475_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec_ref(v_config_1812_);
v_val_2434_ = lean_ctor_get(v_a_2433_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_a_2433_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2436_ = v_a_2433_;
v_isShared_2437_ = v_isSharedCheck_2475_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_val_2434_);
lean_dec(v_a_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2475_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; 
lean_inc(v_mvarId_1813_);
v___x_2438_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2441_ = l_Lean_mkFVar(v_val_2434_);
v___x_2442_ = l_Lean_Expr_app___override(v___x_2440_, v___x_2441_);
v___x_2443_ = l_Lean_Meta_mkFalseElim(v_a_2439_, v___x_2442_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref(v___x_2443_);
v___x_2445_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2444_, v___y_1819_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
lean_dec_ref(v___x_2445_);
v___x_2446_ = lean_box(v___x_1823_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2446_);
v___x_2448_ = v___x_2436_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
lean_ctor_set(v___x_2449_, 1, v___x_1848_);
v_a_1830_ = v___x_2449_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_del_object(v___x_2436_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_2451_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2445_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2445_);
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
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_del_object(v___x_2436_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2459_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2443_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2443_);
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
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_del_object(v___x_2436_);
lean_dec(v_val_2434_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2467_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2438_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2438_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
else
{
lean_dec(v_a_2433_);
v___y_2295_ = v___y_1818_;
v___y_2296_ = v___y_1819_;
v___y_2297_ = v___y_1820_;
v___y_2298_ = v___y_1821_;
goto v___jp_2294_;
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2476_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2432_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2432_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_dec(v_a_2430_);
v___y_2295_ = v___y_1818_;
v___y_2296_ = v___y_1819_;
v___y_2297_ = v___y_1820_;
v___y_2298_ = v___y_1821_;
goto v___jp_2294_;
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2484_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2429_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2429_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
v___jp_1962_:
{
uint8_t v_genDiseq_1969_; 
v_genDiseq_1969_ = lean_ctor_get_uint8(v_config_1812_, sizeof(void*)*1 + 2);
if (v_genDiseq_1969_ == 0)
{
lean_dec_ref(v___x_1961_);
v___y_1940_ = v___y_1968_;
v___y_1941_ = v___y_1966_;
v___y_1942_ = v___y_1965_;
v___y_1943_ = v___y_1963_;
v___y_1944_ = v___y_1964_;
v___y_1945_ = v___y_1967_;
v___y_1946_ = v___x_1917_;
goto v___jp_1939_;
}
else
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1961_);
v___y_1940_ = v___y_1968_;
v___y_1941_ = v___y_1966_;
v___y_1942_ = v___y_1965_;
v___y_1943_ = v___y_1963_;
v___y_1944_ = v___y_1964_;
v___y_1945_ = v___y_1967_;
v___y_1946_ = v___x_1970_;
goto v___jp_1939_;
}
}
v___jp_1971_:
{
if (v___y_1979_ == 0)
{
lean_dec_ref(v___y_1972_);
v___y_1963_ = v___y_1977_;
v___y_1964_ = v___y_1978_;
v___y_1965_ = v___y_1974_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1973_;
v___y_1968_ = v___y_1975_;
goto v___jp_1962_;
}
else
{
lean_object* v___x_1980_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___y_1972_);
return v___x_1980_;
}
}
v___jp_1981_:
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_Exception_isInterrupt(v_a_1988_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
lean_inc_ref(v_a_1988_);
v___x_1990_ = l_Lean_Exception_isRuntime(v_a_1988_);
v___y_1972_ = v_a_1988_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1983_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1985_;
v___y_1977_ = v___y_1986_;
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___x_1990_;
goto v___jp_1971_;
}
else
{
v___y_1972_ = v_a_1988_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1983_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1985_;
v___y_1977_ = v___y_1986_;
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___x_1989_;
goto v___jp_1971_;
}
}
v___jp_1991_:
{
lean_object* v___x_1998_; 
lean_inc_ref(v___x_1961_);
v___x_1998_ = l_Lean_Meta_mkDecide(v___x_1961_, v___y_1993_, v___y_1995_, v___y_1992_, v___y_1994_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; uint8_t v_foApprox_2001_; uint8_t v_ctxApprox_2002_; uint8_t v_quasiPatternApprox_2003_; uint8_t v_constApprox_2004_; uint8_t v_isDefEqStuckEx_2005_; uint8_t v_unificationHints_2006_; uint8_t v_proofIrrelevance_2007_; uint8_t v_assignSyntheticOpaque_2008_; uint8_t v_offsetCnstrs_2009_; uint8_t v_etaStruct_2010_; uint8_t v_univApprox_2011_; uint8_t v_iota_2012_; uint8_t v_beta_2013_; uint8_t v_proj_2014_; uint8_t v_zeta_2015_; uint8_t v_zetaDelta_2016_; uint8_t v_zetaUnused_2017_; uint8_t v_zetaHave_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2080_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
v___x_2000_ = l_Lean_Meta_Context_config(v___y_1993_);
v_foApprox_2001_ = lean_ctor_get_uint8(v___x_2000_, 0);
v_ctxApprox_2002_ = lean_ctor_get_uint8(v___x_2000_, 1);
v_quasiPatternApprox_2003_ = lean_ctor_get_uint8(v___x_2000_, 2);
v_constApprox_2004_ = lean_ctor_get_uint8(v___x_2000_, 3);
v_isDefEqStuckEx_2005_ = lean_ctor_get_uint8(v___x_2000_, 4);
v_unificationHints_2006_ = lean_ctor_get_uint8(v___x_2000_, 5);
v_proofIrrelevance_2007_ = lean_ctor_get_uint8(v___x_2000_, 6);
v_assignSyntheticOpaque_2008_ = lean_ctor_get_uint8(v___x_2000_, 7);
v_offsetCnstrs_2009_ = lean_ctor_get_uint8(v___x_2000_, 8);
v_etaStruct_2010_ = lean_ctor_get_uint8(v___x_2000_, 10);
v_univApprox_2011_ = lean_ctor_get_uint8(v___x_2000_, 11);
v_iota_2012_ = lean_ctor_get_uint8(v___x_2000_, 12);
v_beta_2013_ = lean_ctor_get_uint8(v___x_2000_, 13);
v_proj_2014_ = lean_ctor_get_uint8(v___x_2000_, 14);
v_zeta_2015_ = lean_ctor_get_uint8(v___x_2000_, 15);
v_zetaDelta_2016_ = lean_ctor_get_uint8(v___x_2000_, 16);
v_zetaUnused_2017_ = lean_ctor_get_uint8(v___x_2000_, 17);
v_zetaHave_2018_ = lean_ctor_get_uint8(v___x_2000_, 18);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2020_ = v___x_2000_;
v_isShared_2021_ = v_isSharedCheck_2080_;
goto v_resetjp_2019_;
}
else
{
lean_dec(v___x_2000_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2080_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
uint8_t v_trackZetaDelta_2022_; lean_object* v_zetaDeltaSet_2023_; lean_object* v_lctx_2024_; lean_object* v_localInstances_2025_; lean_object* v_defEqCtx_x3f_2026_; lean_object* v_synthPendingDepth_2027_; lean_object* v_canUnfold_x3f_2028_; uint8_t v_univApprox_2029_; uint8_t v_inTypeClassResolution_2030_; uint8_t v_cacheInferType_2031_; uint8_t v___x_2032_; lean_object* v_config_2034_; 
v_trackZetaDelta_2022_ = lean_ctor_get_uint8(v___y_1993_, sizeof(void*)*7);
v_zetaDeltaSet_2023_ = lean_ctor_get(v___y_1993_, 1);
v_lctx_2024_ = lean_ctor_get(v___y_1993_, 2);
v_localInstances_2025_ = lean_ctor_get(v___y_1993_, 3);
v_defEqCtx_x3f_2026_ = lean_ctor_get(v___y_1993_, 4);
v_synthPendingDepth_2027_ = lean_ctor_get(v___y_1993_, 5);
v_canUnfold_x3f_2028_ = lean_ctor_get(v___y_1993_, 6);
v_univApprox_2029_ = lean_ctor_get_uint8(v___y_1993_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2030_ = lean_ctor_get_uint8(v___y_1993_, sizeof(void*)*7 + 2);
v_cacheInferType_2031_ = lean_ctor_get_uint8(v___y_1993_, sizeof(void*)*7 + 3);
v___x_2032_ = 1;
if (v_isShared_2021_ == 0)
{
v_config_2034_ = v___x_2020_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 0, v_foApprox_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 1, v_ctxApprox_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 2, v_quasiPatternApprox_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 3, v_constApprox_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 4, v_isDefEqStuckEx_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 5, v_unificationHints_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 6, v_proofIrrelevance_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 7, v_assignSyntheticOpaque_2008_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 8, v_offsetCnstrs_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 10, v_etaStruct_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 11, v_univApprox_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 12, v_iota_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 13, v_beta_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 14, v_proj_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 15, v_zeta_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 16, v_zetaDelta_2016_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 17, v_zetaUnused_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, 18, v_zetaHave_2018_);
v_config_2034_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
uint64_t v___x_2035_; uint64_t v___x_2036_; uint64_t v___x_2037_; uint64_t v___x_2038_; uint64_t v___x_2039_; uint64_t v_key_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_ctor_set_uint8(v_config_2034_, 9, v___x_2032_);
v___x_2035_ = l_Lean_Meta_Context_configKey(v___y_1993_);
v___x_2036_ = 2ULL;
v___x_2037_ = lean_uint64_shift_right(v___x_2035_, v___x_2036_);
v___x_2038_ = lean_uint64_shift_left(v___x_2037_, v___x_2036_);
v___x_2039_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_2040_ = lean_uint64_lor(v___x_2038_, v___x_2039_);
v___x_2041_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2041_, 0, v_config_2034_);
lean_ctor_set_uint64(v___x_2041_, sizeof(void*)*1, v_key_2040_);
lean_inc(v_canUnfold_x3f_2028_);
lean_inc(v_synthPendingDepth_2027_);
lean_inc(v_defEqCtx_x3f_2026_);
lean_inc_ref(v_localInstances_2025_);
lean_inc_ref(v_lctx_2024_);
lean_inc(v_zetaDeltaSet_2023_);
v___x_2042_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v_zetaDeltaSet_2023_);
lean_ctor_set(v___x_2042_, 2, v_lctx_2024_);
lean_ctor_set(v___x_2042_, 3, v_localInstances_2025_);
lean_ctor_set(v___x_2042_, 4, v_defEqCtx_x3f_2026_);
lean_ctor_set(v___x_2042_, 5, v_synthPendingDepth_2027_);
lean_ctor_set(v___x_2042_, 6, v_canUnfold_x3f_2028_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*7, v_trackZetaDelta_2022_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*7 + 1, v_univApprox_2029_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2030_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*7 + 3, v_cacheInferType_2031_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1992_);
lean_inc(v___y_1995_);
lean_inc(v_a_1999_);
v___x_2043_ = lean_whnf(v_a_1999_, v___x_2042_, v___y_1995_, v___y_1992_, v___y_1994_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_2046_ = l_Lean_Expr_isConstOf(v_a_2044_, v___x_2045_);
lean_dec(v_a_2044_);
if (v___x_2046_ == 0)
{
lean_dec(v_a_1999_);
v___y_1963_ = v___y_1996_;
v___y_1964_ = v___y_1997_;
v___y_1965_ = v___y_1993_;
v___y_1966_ = v___y_1995_;
v___y_1967_ = v___y_1992_;
v___y_1968_ = v___y_1994_;
goto v___jp_1962_;
}
else
{
lean_object* v___x_2047_; 
lean_inc(v_a_1999_);
v___x_2047_ = l_Lean_Meta_mkEqRefl(v_a_1999_, v___y_1993_, v___y_1995_, v___y_1992_, v___y_1994_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
lean_inc(v_mvarId_1813_);
v___x_2049_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_1993_, v___y_1995_, v___y_1992_, v___y_1994_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v_nargs_2051_; lean_object* v___x_2052_; lean_object* v_dummy_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v_nargs_2051_ = l_Lean_Expr_getAppNumArgs(v_a_1999_);
v___x_2052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2053_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2051_);
v___x_2054_ = lean_mk_array(v_nargs_2051_, v_dummy_2053_);
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_sub(v_nargs_2051_, v___x_2055_);
lean_dec(v_nargs_2051_);
v___x_2057_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1999_, v___x_2054_, v___x_2056_);
v___x_2058_ = lean_array_push(v___x_2057_, v_a_2048_);
v___x_2059_ = l_Lean_mkAppN(v___x_2052_, v___x_2058_);
lean_dec_ref(v___x_2058_);
lean_inc(v_val_1844_);
v___x_2060_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2061_ = l_Lean_Meta_mkAbsurd(v_a_2050_, v___x_2060_, v___x_2059_, v___y_1993_, v___y_1995_, v___y_1992_, v___y_1994_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref(v___x_2061_);
lean_inc(v_mvarId_1813_);
v___x_2063_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2062_, v___y_1995_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2063_, 0);
lean_dec(v_unused_2073_);
v___x_2065_ = v___x_2063_;
v_isShared_2066_ = v_isSharedCheck_2072_;
goto v_resetjp_2064_;
}
else
{
lean_dec(v___x_2063_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2072_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_box(v___x_1823_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set_tag(v___x_2065_, 1);
lean_ctor_set(v___x_2065_, 0, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___x_1848_);
v_a_1830_ = v___x_2070_;
goto v___jp_1829_;
}
}
}
else
{
lean_object* v_a_2074_; 
v_a_2074_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2063_);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2074_;
goto v___jp_1981_;
}
}
else
{
lean_object* v_a_2075_; 
v_a_2075_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2061_);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2075_;
goto v___jp_1981_;
}
}
else
{
lean_object* v_a_2076_; 
lean_dec(v_a_2048_);
lean_dec(v_a_1999_);
v_a_2076_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2076_);
lean_dec_ref(v___x_2049_);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2076_;
goto v___jp_1981_;
}
}
else
{
lean_object* v_a_2077_; 
lean_dec(v_a_1999_);
v_a_2077_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2047_);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2077_;
goto v___jp_1981_;
}
}
}
else
{
lean_object* v_a_2078_; 
lean_dec(v_a_1999_);
v_a_2078_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2043_);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2078_;
goto v___jp_1981_;
}
}
}
}
else
{
lean_object* v_a_2081_; 
v_a_2081_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_2081_);
lean_dec_ref(v___x_1998_);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2081_;
goto v___jp_1981_;
}
}
v___jp_2082_:
{
if (v___y_2089_ == 0)
{
v___y_1963_ = v___y_2087_;
v___y_1964_ = v___y_2088_;
v___y_1965_ = v___y_2084_;
v___y_1966_ = v___y_2086_;
v___y_1967_ = v___y_2083_;
v___y_1968_ = v___y_2085_;
goto v___jp_1962_;
}
else
{
v___y_1992_ = v___y_2083_;
v___y_1993_ = v___y_2084_;
v___y_1994_ = v___y_2085_;
v___y_1995_ = v___y_2086_;
v___y_1996_ = v___y_2087_;
v___y_1997_ = v___y_2088_;
goto v___jp_1991_;
}
}
v___jp_2090_:
{
if (v___y_2098_ == 0)
{
lean_dec_ref(v___y_2093_);
v___y_2083_ = v___y_2091_;
v___y_2084_ = v___y_2092_;
v___y_2085_ = v___y_2094_;
v___y_2086_ = v___y_2095_;
v___y_2087_ = v___y_2096_;
v___y_2088_ = v___y_2097_;
v___y_2089_ = v___x_1917_;
goto v___jp_2082_;
}
else
{
uint8_t v___x_2099_; 
v___x_2099_ = l_Lean_Expr_hasFVar(v___y_2093_);
lean_dec_ref(v___y_2093_);
if (v___x_2099_ == 0)
{
v___y_1992_ = v___y_2091_;
v___y_1993_ = v___y_2092_;
v___y_1994_ = v___y_2094_;
v___y_1995_ = v___y_2095_;
v___y_1996_ = v___y_2096_;
v___y_1997_ = v___y_2097_;
goto v___jp_1991_;
}
else
{
v___y_2083_ = v___y_2091_;
v___y_2084_ = v___y_2092_;
v___y_2085_ = v___y_2094_;
v___y_2086_ = v___y_2095_;
v___y_2087_ = v___y_2096_;
v___y_2088_ = v___y_2097_;
v___y_2089_ = v___x_1917_;
goto v___jp_2082_;
}
}
}
v___jp_2100_:
{
lean_object* v___x_2108_; 
lean_inc_ref(v___x_1961_);
v___x_2108_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1961_, v___y_2104_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; uint8_t v___x_2110_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
v___x_2110_ = l_Lean_Expr_hasMVar(v_a_2109_);
if (v___x_2110_ == 0)
{
v___y_2091_ = v___y_2101_;
v___y_2092_ = v___y_2102_;
v___y_2093_ = v_a_2109_;
v___y_2094_ = v___y_2103_;
v___y_2095_ = v___y_2104_;
v___y_2096_ = v___y_2105_;
v___y_2097_ = v___y_2106_;
v___y_2098_ = v___y_2107_;
goto v___jp_2090_;
}
else
{
v___y_2091_ = v___y_2101_;
v___y_2092_ = v___y_2102_;
v___y_2093_ = v_a_2109_;
v___y_2094_ = v___y_2103_;
v___y_2095_ = v___y_2104_;
v___y_2096_ = v___y_2105_;
v___y_2097_ = v___y_2106_;
v___y_2098_ = v___x_1917_;
goto v___jp_2090_;
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2111_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2108_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2108_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
v___jp_2119_:
{
if (v___y_2126_ == 0)
{
v___y_1963_ = v___y_2124_;
v___y_1964_ = v___y_2125_;
v___y_1965_ = v___y_2121_;
v___y_1966_ = v___y_2123_;
v___y_1967_ = v___y_2120_;
v___y_1968_ = v___y_2122_;
goto v___jp_1962_;
}
else
{
v___y_2101_ = v___y_2120_;
v___y_2102_ = v___y_2121_;
v___y_2103_ = v___y_2122_;
v___y_2104_ = v___y_2123_;
v___y_2105_ = v___y_2124_;
v___y_2106_ = v___y_2125_;
v___y_2107_ = v___y_2126_;
goto v___jp_2100_;
}
}
v___jp_2127_:
{
uint8_t v_useDecide_2134_; 
v_useDecide_2134_ = lean_ctor_get_uint8(v_config_1812_, sizeof(void*)*1);
if (v_useDecide_2134_ == 0)
{
v___y_2120_ = v___y_2132_;
v___y_2121_ = v___y_2130_;
v___y_2122_ = v___y_2133_;
v___y_2123_ = v___y_2131_;
v___y_2124_ = v_isHEq_2129_;
v___y_2125_ = v___y_2128_;
v___y_2126_ = v___x_1917_;
goto v___jp_2119_;
}
else
{
uint8_t v___x_2135_; 
v___x_2135_ = l_Lean_Expr_hasFVar(v___x_1961_);
if (v___x_2135_ == 0)
{
v___y_2101_ = v___y_2132_;
v___y_2102_ = v___y_2130_;
v___y_2103_ = v___y_2133_;
v___y_2104_ = v___y_2131_;
v___y_2105_ = v_isHEq_2129_;
v___y_2106_ = v___y_2128_;
v___y_2107_ = v_useDecide_2134_;
goto v___jp_2100_;
}
else
{
v___y_2120_ = v___y_2132_;
v___y_2121_ = v___y_2130_;
v___y_2122_ = v___y_2133_;
v___y_2123_ = v___y_2131_;
v___y_2124_ = v_isHEq_2129_;
v___y_2125_ = v___y_2128_;
v___y_2126_ = v___x_1917_;
goto v___jp_2119_;
}
}
}
v___jp_2136_:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Meta_isExprDefEq(v___y_2143_, v___y_2140_, v___y_2138_, v___y_2141_, v___y_2137_, v___y_2139_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; uint8_t v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = lean_unbox(v_a_2145_);
lean_dec(v_a_2145_);
if (v___x_2146_ == 0)
{
v___y_2128_ = v___y_2142_;
v_isHEq_2129_ = v___x_1823_;
v___y_2130_ = v___y_2138_;
v___y_2131_ = v___y_2141_;
v___y_2132_ = v___y_2137_;
v___y_2133_ = v___y_2139_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2147_; 
lean_dec_ref(v___x_1961_);
lean_dec_ref(v_config_1812_);
lean_inc(v_mvarId_1813_);
v___x_2147_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_2138_, v___y_2141_, v___y_2137_, v___y_2139_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2150_ = l_Lean_Meta_mkEqOfHEq(v___x_2149_, v___x_1823_, v___y_2138_, v___y_2141_, v___y_2137_, v___y_2139_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v___x_2150_);
v___x_2152_ = l_Lean_Meta_mkNoConfusion(v_a_2148_, v_a_2151_, v___y_2138_, v___y_2141_, v___y_2137_, v___y_2139_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2154_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref(v___x_2152_);
v___x_2154_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2153_, v___y_2141_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v___x_2154_);
v___x_2155_ = lean_box(v___x_1823_);
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v___x_1848_);
v_a_1830_ = v___x_2157_;
goto v___jp_1829_;
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_2158_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2154_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2154_);
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
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2166_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2152_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2152_);
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
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2148_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2174_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2150_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2150_);
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
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2182_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2147_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2147_);
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
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2190_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2144_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2144_);
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
v___jp_2198_:
{
lean_object* v___x_2204_; 
lean_inc_ref(v___x_1961_);
v___x_2204_ = l_Lean_Meta_matchHEq_x3f(v___x_1961_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2204_);
if (lean_obj_tag(v_a_2205_) == 1)
{
lean_object* v_val_2206_; lean_object* v_snd_2207_; lean_object* v_snd_2208_; lean_object* v_fst_2209_; lean_object* v_fst_2210_; lean_object* v_fst_2211_; lean_object* v_snd_2212_; lean_object* v___x_2213_; 
v_val_2206_ = lean_ctor_get(v_a_2205_, 0);
lean_inc(v_val_2206_);
lean_dec_ref(v_a_2205_);
v_snd_2207_ = lean_ctor_get(v_val_2206_, 1);
lean_inc(v_snd_2207_);
v_snd_2208_ = lean_ctor_get(v_snd_2207_, 1);
lean_inc(v_snd_2208_);
v_fst_2209_ = lean_ctor_get(v_val_2206_, 0);
lean_inc(v_fst_2209_);
lean_dec(v_val_2206_);
v_fst_2210_ = lean_ctor_get(v_snd_2207_, 0);
lean_inc(v_fst_2210_);
lean_dec(v_snd_2207_);
v_fst_2211_ = lean_ctor_get(v_snd_2208_, 0);
lean_inc(v_fst_2211_);
v_snd_2212_ = lean_ctor_get(v_snd_2208_, 1);
lean_inc(v_snd_2212_);
lean_dec(v_snd_2208_);
v___x_2213_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2210_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref(v___x_2213_);
if (lean_obj_tag(v_a_2214_) == 1)
{
lean_object* v_val_2215_; lean_object* v___x_2216_; 
v_val_2215_ = lean_ctor_get(v_a_2214_, 0);
lean_inc(v_val_2215_);
lean_dec_ref(v_a_2214_);
v___x_2216_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2212_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2216_);
if (lean_obj_tag(v_a_2217_) == 1)
{
lean_object* v_toConstantVal_2218_; lean_object* v_val_2219_; lean_object* v_toConstantVal_2220_; lean_object* v_name_2221_; lean_object* v_name_2222_; uint8_t v___x_2223_; 
v_toConstantVal_2218_ = lean_ctor_get(v_val_2215_, 0);
lean_inc_ref(v_toConstantVal_2218_);
lean_dec(v_val_2215_);
v_val_2219_ = lean_ctor_get(v_a_2217_, 0);
lean_inc(v_val_2219_);
lean_dec_ref(v_a_2217_);
v_toConstantVal_2220_ = lean_ctor_get(v_val_2219_, 0);
lean_inc_ref(v_toConstantVal_2220_);
lean_dec(v_val_2219_);
v_name_2221_ = lean_ctor_get(v_toConstantVal_2218_, 0);
lean_inc(v_name_2221_);
lean_dec_ref(v_toConstantVal_2218_);
v_name_2222_ = lean_ctor_get(v_toConstantVal_2220_, 0);
lean_inc(v_name_2222_);
lean_dec_ref(v_toConstantVal_2220_);
v___x_2223_ = lean_name_eq(v_name_2221_, v_name_2222_);
lean_dec(v_name_2222_);
lean_dec(v_name_2221_);
if (v___x_2223_ == 0)
{
v___y_2137_ = v___y_2202_;
v___y_2138_ = v___y_2200_;
v___y_2139_ = v___y_2203_;
v___y_2140_ = v_fst_2211_;
v___y_2141_ = v___y_2201_;
v___y_2142_ = v_isEq_2199_;
v___y_2143_ = v_fst_2209_;
goto v___jp_2136_;
}
else
{
if (v___x_1917_ == 0)
{
lean_dec(v_fst_2211_);
lean_dec(v_fst_2209_);
v___y_2128_ = v_isEq_2199_;
v_isHEq_2129_ = v___x_1823_;
v___y_2130_ = v___y_2200_;
v___y_2131_ = v___y_2201_;
v___y_2132_ = v___y_2202_;
v___y_2133_ = v___y_2203_;
goto v___jp_2127_;
}
else
{
v___y_2137_ = v___y_2202_;
v___y_2138_ = v___y_2200_;
v___y_2139_ = v___y_2203_;
v___y_2140_ = v_fst_2211_;
v___y_2141_ = v___y_2201_;
v___y_2142_ = v_isEq_2199_;
v___y_2143_ = v_fst_2209_;
goto v___jp_2136_;
}
}
}
else
{
lean_dec(v_a_2217_);
lean_dec(v_val_2215_);
lean_dec(v_fst_2211_);
lean_dec(v_fst_2209_);
v___y_2128_ = v_isEq_2199_;
v_isHEq_2129_ = v___x_1823_;
v___y_2130_ = v___y_2200_;
v___y_2131_ = v___y_2201_;
v___y_2132_ = v___y_2202_;
v___y_2133_ = v___y_2203_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_val_2215_);
lean_dec(v_fst_2211_);
lean_dec(v_fst_2209_);
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2224_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2216_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2216_);
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
else
{
lean_dec(v_a_2214_);
lean_dec(v_snd_2212_);
lean_dec(v_fst_2211_);
lean_dec(v_fst_2209_);
v___y_2128_ = v_isEq_2199_;
v_isHEq_2129_ = v___x_1823_;
v___y_2130_ = v___y_2200_;
v___y_2131_ = v___y_2201_;
v___y_2132_ = v___y_2202_;
v___y_2133_ = v___y_2203_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_snd_2212_);
lean_dec(v_fst_2211_);
lean_dec(v_fst_2209_);
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2232_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2213_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2213_);
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
else
{
lean_dec(v_a_2205_);
v___y_2128_ = v_isEq_2199_;
v_isHEq_2129_ = v___x_1917_;
v___y_2130_ = v___y_2200_;
v___y_2131_ = v___y_2201_;
v___y_2132_ = v___y_2202_;
v___y_2133_ = v___y_2203_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2240_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2204_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2204_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
v___jp_2248_:
{
lean_object* v___x_2253_; 
lean_inc_ref(v___x_1961_);
v___x_2253_ = l_Lean_Meta_matchEq_x3f(v___x_1961_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref(v___x_2253_);
if (lean_obj_tag(v_a_2254_) == 1)
{
lean_object* v_val_2255_; lean_object* v_snd_2256_; lean_object* v_fst_2257_; lean_object* v_snd_2258_; lean_object* v___x_2259_; 
v_val_2255_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_val_2255_);
lean_dec_ref(v_a_2254_);
v_snd_2256_ = lean_ctor_get(v_val_2255_, 1);
lean_inc(v_snd_2256_);
lean_dec(v_val_2255_);
v_fst_2257_ = lean_ctor_get(v_snd_2256_, 0);
lean_inc(v_fst_2257_);
v_snd_2258_ = lean_ctor_get(v_snd_2256_, 1);
lean_inc(v_snd_2258_);
lean_dec(v_snd_2256_);
v___x_2259_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2257_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2259_);
if (lean_obj_tag(v_a_2260_) == 1)
{
lean_object* v_val_2261_; lean_object* v___x_2262_; 
v_val_2261_ = lean_ctor_get(v_a_2260_, 0);
lean_inc(v_val_2261_);
lean_dec_ref(v_a_2260_);
v___x_2262_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2258_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2262_);
if (lean_obj_tag(v_a_2263_) == 1)
{
lean_object* v_toConstantVal_2264_; lean_object* v_val_2265_; lean_object* v_toConstantVal_2266_; lean_object* v_name_2267_; lean_object* v_name_2268_; uint8_t v___x_2269_; 
v_toConstantVal_2264_ = lean_ctor_get(v_val_2261_, 0);
lean_inc_ref(v_toConstantVal_2264_);
lean_dec(v_val_2261_);
v_val_2265_ = lean_ctor_get(v_a_2263_, 0);
lean_inc(v_val_2265_);
lean_dec_ref(v_a_2263_);
v_toConstantVal_2266_ = lean_ctor_get(v_val_2265_, 0);
lean_inc_ref(v_toConstantVal_2266_);
lean_dec(v_val_2265_);
v_name_2267_ = lean_ctor_get(v_toConstantVal_2264_, 0);
lean_inc(v_name_2267_);
lean_dec_ref(v_toConstantVal_2264_);
v_name_2268_ = lean_ctor_get(v_toConstantVal_2266_, 0);
lean_inc(v_name_2268_);
lean_dec_ref(v_toConstantVal_2266_);
v___x_2269_ = lean_name_eq(v_name_2267_, v_name_2268_);
lean_dec(v_name_2268_);
lean_dec(v_name_2267_);
if (v___x_2269_ == 0)
{
lean_dec_ref(v___x_1961_);
lean_dec_ref(v_config_1812_);
v___y_1850_ = v___y_2252_;
v___y_1851_ = v___y_2250_;
v___y_1852_ = v___y_2251_;
v___y_1853_ = v___y_2249_;
goto v___jp_1849_;
}
else
{
if (v___x_1917_ == 0)
{
lean_del_object(v___x_1846_);
v_isEq_2199_ = v___x_1823_;
v___y_2200_ = v___y_2249_;
v___y_2201_ = v___y_2250_;
v___y_2202_ = v___y_2251_;
v___y_2203_ = v___y_2252_;
goto v___jp_2198_;
}
else
{
lean_dec_ref(v___x_1961_);
lean_dec_ref(v_config_1812_);
v___y_1850_ = v___y_2252_;
v___y_1851_ = v___y_2250_;
v___y_1852_ = v___y_2251_;
v___y_1853_ = v___y_2249_;
goto v___jp_1849_;
}
}
}
else
{
lean_dec(v_a_2263_);
lean_dec(v_val_2261_);
lean_del_object(v___x_1846_);
v_isEq_2199_ = v___x_1823_;
v___y_2200_ = v___y_2249_;
v___y_2201_ = v___y_2250_;
v___y_2202_ = v___y_2251_;
v___y_2203_ = v___y_2252_;
goto v___jp_2198_;
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_val_2261_);
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2270_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2262_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2262_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_dec(v_a_2260_);
lean_dec(v_snd_2258_);
lean_del_object(v___x_1846_);
v_isEq_2199_ = v___x_1823_;
v___y_2200_ = v___y_2249_;
v___y_2201_ = v___y_2250_;
v___y_2202_ = v___y_2251_;
v___y_2203_ = v___y_2252_;
goto v___jp_2198_;
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_snd_2258_);
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2278_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2259_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2259_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_dec(v_a_2254_);
lean_del_object(v___x_1846_);
v_isEq_2199_ = v___x_1917_;
v___y_2200_ = v___y_2249_;
v___y_2201_ = v___y_2250_;
v___y_2202_ = v___y_2251_;
v___y_2203_ = v___y_2252_;
goto v___jp_2198_;
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2286_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2253_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2253_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
v___jp_2294_:
{
lean_object* v___x_2299_; 
lean_inc_ref(v___x_1961_);
v___x_2299_ = l_refutableHasNotBit_x3f(v___x_1961_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v___x_2299_);
if (lean_obj_tag(v_a_2300_) == 1)
{
lean_object* v_val_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec_ref(v_config_1812_);
v_val_2301_ = lean_ctor_get(v_a_2300_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_a_2300_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2303_ = v_a_2300_;
v_isShared_2304_ = v_isSharedCheck_2340_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_val_2301_);
lean_dec(v_a_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2340_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; 
lean_inc(v_mvarId_1813_);
v___x_2305_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref(v___x_2305_);
v___x_2307_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2308_ = l_Lean_Meta_mkAbsurd(v_a_2306_, v_val_2301_, v___x_2307_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2309_, v___y_2296_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
lean_dec_ref(v___x_2310_);
v___x_2311_ = lean_box(v___x_1823_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2311_);
v___x_2313_ = v___x_2303_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v___x_1848_);
v_a_1830_ = v___x_2314_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_del_object(v___x_2303_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_2316_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2310_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2310_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_del_object(v___x_2303_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2324_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2308_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2308_);
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
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_del_object(v___x_2303_);
lean_dec(v_val_2301_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2332_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2305_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2305_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
else
{
lean_object* v___x_2341_; 
lean_dec(v_a_2300_);
lean_inc_ref(v___x_1961_);
v___x_2341_ = l_Lean_Meta_matchNe_x3f(v___x_1961_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref(v___x_2341_);
if (lean_obj_tag(v_a_2342_) == 1)
{
lean_object* v_val_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2412_; 
v_val_2343_ = lean_ctor_get(v_a_2342_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_a_2342_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2345_ = v_a_2342_;
v_isShared_2346_ = v_isSharedCheck_2412_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_val_2343_);
lean_dec(v_a_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2412_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v_snd_2347_; lean_object* v_fst_2348_; lean_object* v_snd_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2411_; 
v_snd_2347_ = lean_ctor_get(v_val_2343_, 1);
lean_inc(v_snd_2347_);
lean_dec(v_val_2343_);
v_fst_2348_ = lean_ctor_get(v_snd_2347_, 0);
v_snd_2349_ = lean_ctor_get(v_snd_2347_, 1);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_snd_2347_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2351_ = v_snd_2347_;
v_isShared_2352_ = v_isSharedCheck_2411_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snd_2349_);
lean_inc(v_fst_2348_);
lean_dec(v_snd_2347_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2411_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; 
lean_inc(v_fst_2348_);
v___x_2353_ = l_Lean_Meta_isExprDefEq(v_fst_2348_, v_snd_2349_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; uint8_t v___x_2355_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref(v___x_2353_);
v___x_2355_ = lean_unbox(v_a_2354_);
lean_dec(v_a_2354_);
if (v___x_2355_ == 0)
{
lean_del_object(v___x_2351_);
lean_dec(v_fst_2348_);
lean_del_object(v___x_2345_);
v___y_2249_ = v___y_2295_;
v___y_2250_ = v___y_2296_;
v___y_2251_ = v___y_2297_;
v___y_2252_ = v___y_2298_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2356_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec_ref(v_config_1812_);
lean_inc(v_mvarId_1813_);
v___x_2356_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2358_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref(v___x_2356_);
v___x_2358_ = l_Lean_Meta_mkEqRefl(v_fst_2348_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref(v___x_2358_);
v___x_2360_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2361_ = l_Lean_Meta_mkAbsurd(v_a_2357_, v_a_2359_, v___x_2360_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2362_, v___y_2296_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
lean_dec_ref(v___x_2363_);
v___x_2364_ = lean_box(v___x_1823_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2364_);
v___x_2366_ = v___x_2345_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 1, v___x_1848_);
lean_ctor_set(v___x_2351_, 0, v___x_2366_);
v___x_2368_ = v___x_2351_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_1848_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
v_a_1830_ = v___x_2368_;
goto v___jp_1829_;
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_del_object(v___x_2351_);
lean_del_object(v___x_2345_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_2371_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2363_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2363_);
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
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_del_object(v___x_2351_);
lean_del_object(v___x_2345_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2379_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2361_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2361_);
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
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_a_2357_);
lean_del_object(v___x_2351_);
lean_del_object(v___x_2345_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2387_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2358_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2358_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_del_object(v___x_2351_);
lean_dec(v_fst_2348_);
lean_del_object(v___x_2345_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2395_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2356_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2356_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_del_object(v___x_2351_);
lean_dec(v_fst_2348_);
lean_del_object(v___x_2345_);
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2403_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2353_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2353_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2342_);
v___y_2249_ = v___y_2295_;
v___y_2250_ = v___y_2296_;
v___y_2251_ = v___y_2297_;
v___y_2252_ = v___y_2298_;
goto v___jp_2248_;
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2413_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2341_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2341_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2421_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2299_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2299_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
else
{
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_1838_ = v___x_1889_;
goto v___jp_1837_;
}
v___jp_1849_:
{
lean_object* v___x_1854_; 
lean_inc(v_mvarId_1813_);
v___x_1854_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_1853_, v___y_1851_, v___y_1852_, v___y_1850_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_1857_ = l_Lean_Meta_mkNoConfusion(v_a_1855_, v___x_1856_, v___y_1853_, v___y_1851_, v___y_1852_, v___y_1850_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1859_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_1858_, v___y_1851_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
lean_dec_ref(v___x_1859_);
v___x_1860_ = lean_box(v___x_1823_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1860_);
v___x_1862_ = v___x_1846_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v___x_1848_);
v_a_1830_ = v___x_1863_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_del_object(v___x_1846_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_1865_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1859_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1859_);
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
lean_del_object(v___x_1846_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_1873_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1857_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1857_);
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
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_1881_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1854_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1854_);
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
v___jp_1890_:
{
lean_object* v_searchFuel_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_searchFuel_1895_ = lean_ctor_get(v_config_1812_, 0);
v___x_1896_ = l_Lean_LocalDecl_fvarId(v_val_1844_);
lean_dec(v_val_1844_);
lean_inc(v_searchFuel_1895_);
lean_inc(v_mvarId_1813_);
v___x_1897_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1813_, v___x_1896_, v_searchFuel_1895_, v___y_1893_, v___y_1891_, v___y_1892_, v___y_1894_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; uint8_t v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = lean_unbox(v_a_1898_);
lean_dec(v_a_1898_);
if (v___x_1899_ == 0)
{
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_1838_ = v___x_1889_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v___x_1900_ = lean_box(v___x_1823_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___x_1848_);
v_a_1830_ = v___x_1902_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_1903_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1897_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1897_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
v___jp_1911_:
{
if (v___y_1916_ == 0)
{
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_1838_ = v___x_1889_;
goto v___jp_1837_;
}
else
{
v___y_1891_ = v___y_1912_;
v___y_1892_ = v___y_1913_;
v___y_1893_ = v___y_1914_;
v___y_1894_ = v___y_1915_;
goto v___jp_1890_;
}
}
v___jp_1918_:
{
if (v___y_1923_ == 0)
{
v___y_1891_ = v___y_1919_;
v___y_1892_ = v___y_1920_;
v___y_1893_ = v___y_1921_;
v___y_1894_ = v___y_1922_;
goto v___jp_1890_;
}
else
{
v___y_1912_ = v___y_1919_;
v___y_1913_ = v___y_1920_;
v___y_1914_ = v___y_1921_;
v___y_1915_ = v___y_1922_;
v___y_1916_ = v___x_1917_;
goto v___jp_1911_;
}
}
v___jp_1924_:
{
if (v___y_1930_ == 0)
{
v___y_1912_ = v___y_1925_;
v___y_1913_ = v___y_1926_;
v___y_1914_ = v___y_1927_;
v___y_1915_ = v___y_1928_;
v___y_1916_ = v___x_1917_;
goto v___jp_1911_;
}
else
{
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1926_;
v___y_1921_ = v___y_1927_;
v___y_1922_ = v___y_1928_;
v___y_1923_ = v___y_1929_;
goto v___jp_1918_;
}
}
v___jp_1931_:
{
uint8_t v_emptyType_1938_; 
v_emptyType_1938_ = lean_ctor_get_uint8(v_config_1812_, sizeof(void*)*1 + 1);
if (v_emptyType_1938_ == 0)
{
v___y_1925_ = v___y_1935_;
v___y_1926_ = v___y_1936_;
v___y_1927_ = v___y_1934_;
v___y_1928_ = v___y_1937_;
v___y_1929_ = v___y_1932_;
v___y_1930_ = v___x_1917_;
goto v___jp_1924_;
}
else
{
if (v___y_1933_ == 0)
{
v___y_1919_ = v___y_1935_;
v___y_1920_ = v___y_1936_;
v___y_1921_ = v___y_1934_;
v___y_1922_ = v___y_1937_;
v___y_1923_ = v___y_1932_;
goto v___jp_1918_;
}
else
{
v___y_1925_ = v___y_1935_;
v___y_1926_ = v___y_1936_;
v___y_1927_ = v___y_1934_;
v___y_1928_ = v___y_1937_;
v___y_1929_ = v___y_1932_;
v___y_1930_ = v___x_1917_;
goto v___jp_1924_;
}
}
}
v___jp_1939_:
{
if (v___y_1946_ == 0)
{
v___y_1932_ = v___y_1943_;
v___y_1933_ = v___y_1944_;
v___y_1934_ = v___y_1942_;
v___y_1935_ = v___y_1941_;
v___y_1936_ = v___y_1945_;
v___y_1937_ = v___y_1940_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1947_; 
lean_inc(v_val_1844_);
lean_inc(v_mvarId_1813_);
v___x_1947_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1813_, v_val_1844_, v___y_1942_, v___y_1941_, v___y_1945_, v___y_1940_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; uint8_t v___x_1949_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = lean_unbox(v_a_1948_);
lean_dec(v_a_1948_);
if (v___x_1949_ == 0)
{
v___y_1932_ = v___y_1943_;
v___y_1933_ = v___y_1944_;
v___y_1934_ = v___y_1942_;
v___y_1935_ = v___y_1941_;
v___y_1936_ = v___y_1945_;
v___y_1937_ = v___y_1940_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec(v_val_1844_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v___x_1950_ = lean_box(v___x_1823_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v___x_1848_);
v_a_1830_ = v___x_1952_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_1953_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1947_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1947_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
}
v___jp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_a_1830_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1831_);
v___x_1833_ = v___x_1827_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_snd_1825_);
v___x_1833_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
v___jp_1837_:
{
lean_object* v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; 
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1836_);
lean_ctor_set(v___x_1839_, 1, v_a_1838_);
v___x_1840_ = ((size_t)1ULL);
v___x_1841_ = lean_usize_add(v_i_1816_, v___x_1840_);
v_i_1816_ = v___x_1841_;
v_b_1817_ = v___x_1839_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2495_, lean_object* v_mvarId_2496_, lean_object* v_as_2497_, lean_object* v_sz_2498_, lean_object* v_i_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
size_t v_sz_boxed_2506_; size_t v_i_boxed_2507_; lean_object* v_res_2508_; 
v_sz_boxed_2506_ = lean_unbox_usize(v_sz_2498_);
lean_dec(v_sz_2498_);
v_i_boxed_2507_ = lean_unbox_usize(v_i_2499_);
lean_dec(v_i_2499_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2495_, v_mvarId_2496_, v_as_2497_, v_sz_boxed_2506_, v_i_boxed_2507_, v_b_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_as_2497_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2509_, lean_object* v_mvarId_2510_, lean_object* v_as_2511_, size_t v_sz_2512_, size_t v_i_2513_, lean_object* v_b_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_usize_dec_lt(v_i_2513_, v_sz_2512_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; 
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v_b_2514_);
return v___x_2521_;
}
else
{
lean_object* v_snd_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_3190_; 
v_snd_2522_ = lean_ctor_get(v_b_2514_, 1);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_b_2514_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v_b_2514_, 0);
lean_dec(v_unused_3191_);
v___x_2524_ = v_b_2514_;
v_isShared_2525_ = v_isSharedCheck_3190_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_snd_2522_);
lean_dec(v_b_2514_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_3190_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_a_2527_; lean_object* v___x_2533_; lean_object* v_a_2535_; lean_object* v_a_2540_; 
v___x_2533_ = lean_box(0);
v_a_2540_ = lean_array_uget(v_as_2511_, v_i_2513_);
if (lean_obj_tag(v_a_2540_) == 0)
{
lean_del_object(v___x_2524_);
v_a_2535_ = v_snd_2522_;
goto v___jp_2534_;
}
else
{
lean_object* v_val_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_3189_; 
v_val_2541_ = lean_ctor_get(v_a_2540_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_a_2540_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_2543_ = v_a_2540_;
v_isShared_2544_ = v_isSharedCheck_3189_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_val_2541_);
lean_dec(v_a_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_3189_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___x_2586_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; uint8_t v___y_2613_; uint8_t v___x_2614_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; uint8_t v___y_2620_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; uint8_t v___y_2626_; uint8_t v___y_2627_; uint8_t v___y_2629_; uint8_t v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2637_; uint8_t v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; uint8_t v___y_2641_; lean_object* v___y_2642_; uint8_t v___y_2643_; 
v___x_2545_ = lean_box(0);
v___x_2586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2614_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2541_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2658_; uint8_t v___y_2660_; uint8_t v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2669_; uint8_t v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; uint8_t v___y_2674_; lean_object* v___y_2675_; uint8_t v___y_2676_; lean_object* v___y_2679_; uint8_t v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; uint8_t v___y_2683_; lean_object* v___y_2684_; lean_object* v_a_2685_; uint8_t v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; uint8_t v___y_2693_; lean_object* v___y_2694_; uint8_t v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; lean_object* v___y_2785_; uint8_t v___y_2786_; lean_object* v___y_2788_; lean_object* v___y_2789_; uint8_t v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; uint8_t v___y_2793_; lean_object* v___y_2794_; uint8_t v___y_2795_; uint8_t v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; uint8_t v___y_2802_; lean_object* v___y_2803_; uint8_t v___y_2804_; uint8_t v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; uint8_t v___y_2821_; lean_object* v___y_2822_; uint8_t v___y_2823_; uint8_t v___y_2825_; uint8_t v_isHEq_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2834_; lean_object* v___y_2835_; uint8_t v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; uint8_t v_isEq_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___x_3126_; 
v___x_2658_ = l_Lean_LocalDecl_type(v_val_2541_);
lean_inc_ref(v___x_2658_);
v___x_3126_ = l_Lean_Meta_matchNot_x3f(v___x_2658_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
if (lean_obj_tag(v_a_3127_) == 1)
{
lean_object* v_val_3128_; lean_object* v___x_3129_; 
v_val_3128_ = lean_ctor_get(v_a_3127_, 0);
lean_inc(v_val_3128_);
lean_dec_ref(v_a_3127_);
v___x_3129_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3128_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref(v___x_3129_);
if (lean_obj_tag(v_a_3130_) == 1)
{
lean_object* v_val_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3172_; 
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec_ref(v_config_2509_);
v_val_3131_ = lean_ctor_get(v_a_3130_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_a_3130_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3133_ = v_a_3130_;
v_isShared_3134_ = v_isSharedCheck_3172_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_val_3131_);
lean_dec(v_a_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3172_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; 
lean_inc(v_mvarId_2510_);
v___x_3135_ = l_Lean_MVarId_getType(v_mvarId_2510_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref(v___x_3135_);
v___x_3137_ = l_Lean_LocalDecl_toExpr(v_val_2541_);
v___x_3138_ = l_Lean_mkFVar(v_val_3131_);
v___x_3139_ = l_Lean_Expr_app___override(v___x_3137_, v___x_3138_);
v___x_3140_ = l_Lean_Meta_mkFalseElim(v_a_3136_, v___x_3139_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref(v___x_3140_);
v___x_3142_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2510_, v_a_3141_, v___y_2516_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
lean_dec_ref(v___x_3142_);
v___x_3143_ = lean_box(v___x_2520_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3143_);
v___x_3145_ = v___x_3133_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
lean_ctor_set(v___x_3146_, 1, v___x_2545_);
v_a_2527_ = v___x_3146_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_del_object(v___x_3133_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
v_a_3148_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3142_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3142_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_del_object(v___x_3133_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_3156_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3140_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3140_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_del_object(v___x_3133_);
lean_dec(v_val_3131_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_3164_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3135_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3135_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
else
{
lean_dec(v_a_3130_);
v___y_2992_ = v___y_2515_;
v___y_2993_ = v___y_2516_;
v___y_2994_ = v___y_2517_;
v___y_2995_ = v___y_2518_;
goto v___jp_2991_;
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_3173_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3129_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3129_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_dec(v_a_3127_);
v___y_2992_ = v___y_2515_;
v___y_2993_ = v___y_2516_;
v___y_2994_ = v___y_2517_;
v___y_2995_ = v___y_2518_;
goto v___jp_2991_;
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_3181_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3126_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3126_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
v___jp_2659_:
{
uint8_t v_genDiseq_2666_; 
v_genDiseq_2666_ = lean_ctor_get_uint8(v_config_2509_, sizeof(void*)*1 + 2);
if (v_genDiseq_2666_ == 0)
{
lean_dec_ref(v___x_2658_);
v___y_2637_ = v___y_2663_;
v___y_2638_ = v___y_2660_;
v___y_2639_ = v___y_2662_;
v___y_2640_ = v___y_2665_;
v___y_2641_ = v___y_2661_;
v___y_2642_ = v___y_2664_;
v___y_2643_ = v___x_2614_;
goto v___jp_2636_;
}
else
{
uint8_t v___x_2667_; 
v___x_2667_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2658_);
v___y_2637_ = v___y_2663_;
v___y_2638_ = v___y_2660_;
v___y_2639_ = v___y_2662_;
v___y_2640_ = v___y_2665_;
v___y_2641_ = v___y_2661_;
v___y_2642_ = v___y_2664_;
v___y_2643_ = v___x_2667_;
goto v___jp_2636_;
}
}
v___jp_2668_:
{
if (v___y_2676_ == 0)
{
lean_dec_ref(v___y_2669_);
v___y_2660_ = v___y_2670_;
v___y_2661_ = v___y_2674_;
v___y_2662_ = v___y_2672_;
v___y_2663_ = v___y_2671_;
v___y_2664_ = v___y_2675_;
v___y_2665_ = v___y_2673_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2677_; 
lean_dec_ref(v___x_2658_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___y_2669_);
return v___x_2677_;
}
}
v___jp_2678_:
{
uint8_t v___x_2686_; 
v___x_2686_ = l_Lean_Exception_isInterrupt(v_a_2685_);
if (v___x_2686_ == 0)
{
uint8_t v___x_2687_; 
lean_inc_ref(v_a_2685_);
v___x_2687_ = l_Lean_Exception_isRuntime(v_a_2685_);
v___y_2669_ = v_a_2685_;
v___y_2670_ = v___y_2680_;
v___y_2671_ = v___y_2679_;
v___y_2672_ = v___y_2681_;
v___y_2673_ = v___y_2682_;
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2684_;
v___y_2676_ = v___x_2687_;
goto v___jp_2668_;
}
else
{
v___y_2669_ = v_a_2685_;
v___y_2670_ = v___y_2680_;
v___y_2671_ = v___y_2679_;
v___y_2672_ = v___y_2681_;
v___y_2673_ = v___y_2682_;
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2684_;
v___y_2676_ = v___x_2686_;
goto v___jp_2668_;
}
}
v___jp_2688_:
{
lean_object* v___x_2695_; 
lean_inc_ref(v___x_2658_);
v___x_2695_ = l_Lean_Meta_mkDecide(v___x_2658_, v___y_2691_, v___y_2690_, v___y_2694_, v___y_2692_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; uint8_t v_foApprox_2698_; uint8_t v_ctxApprox_2699_; uint8_t v_quasiPatternApprox_2700_; uint8_t v_constApprox_2701_; uint8_t v_isDefEqStuckEx_2702_; uint8_t v_unificationHints_2703_; uint8_t v_proofIrrelevance_2704_; uint8_t v_assignSyntheticOpaque_2705_; uint8_t v_offsetCnstrs_2706_; uint8_t v_etaStruct_2707_; uint8_t v_univApprox_2708_; uint8_t v_iota_2709_; uint8_t v_beta_2710_; uint8_t v_proj_2711_; uint8_t v_zeta_2712_; uint8_t v_zetaDelta_2713_; uint8_t v_zetaUnused_2714_; uint8_t v_zetaHave_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2777_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = l_Lean_Meta_Context_config(v___y_2691_);
v_foApprox_2698_ = lean_ctor_get_uint8(v___x_2697_, 0);
v_ctxApprox_2699_ = lean_ctor_get_uint8(v___x_2697_, 1);
v_quasiPatternApprox_2700_ = lean_ctor_get_uint8(v___x_2697_, 2);
v_constApprox_2701_ = lean_ctor_get_uint8(v___x_2697_, 3);
v_isDefEqStuckEx_2702_ = lean_ctor_get_uint8(v___x_2697_, 4);
v_unificationHints_2703_ = lean_ctor_get_uint8(v___x_2697_, 5);
v_proofIrrelevance_2704_ = lean_ctor_get_uint8(v___x_2697_, 6);
v_assignSyntheticOpaque_2705_ = lean_ctor_get_uint8(v___x_2697_, 7);
v_offsetCnstrs_2706_ = lean_ctor_get_uint8(v___x_2697_, 8);
v_etaStruct_2707_ = lean_ctor_get_uint8(v___x_2697_, 10);
v_univApprox_2708_ = lean_ctor_get_uint8(v___x_2697_, 11);
v_iota_2709_ = lean_ctor_get_uint8(v___x_2697_, 12);
v_beta_2710_ = lean_ctor_get_uint8(v___x_2697_, 13);
v_proj_2711_ = lean_ctor_get_uint8(v___x_2697_, 14);
v_zeta_2712_ = lean_ctor_get_uint8(v___x_2697_, 15);
v_zetaDelta_2713_ = lean_ctor_get_uint8(v___x_2697_, 16);
v_zetaUnused_2714_ = lean_ctor_get_uint8(v___x_2697_, 17);
v_zetaHave_2715_ = lean_ctor_get_uint8(v___x_2697_, 18);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2717_ = v___x_2697_;
v_isShared_2718_ = v_isSharedCheck_2777_;
goto v_resetjp_2716_;
}
else
{
lean_dec(v___x_2697_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2777_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
uint8_t v_trackZetaDelta_2719_; lean_object* v_zetaDeltaSet_2720_; lean_object* v_lctx_2721_; lean_object* v_localInstances_2722_; lean_object* v_defEqCtx_x3f_2723_; lean_object* v_synthPendingDepth_2724_; lean_object* v_canUnfold_x3f_2725_; uint8_t v_univApprox_2726_; uint8_t v_inTypeClassResolution_2727_; uint8_t v_cacheInferType_2728_; uint8_t v___x_2729_; lean_object* v_config_2731_; 
v_trackZetaDelta_2719_ = lean_ctor_get_uint8(v___y_2691_, sizeof(void*)*7);
v_zetaDeltaSet_2720_ = lean_ctor_get(v___y_2691_, 1);
v_lctx_2721_ = lean_ctor_get(v___y_2691_, 2);
v_localInstances_2722_ = lean_ctor_get(v___y_2691_, 3);
v_defEqCtx_x3f_2723_ = lean_ctor_get(v___y_2691_, 4);
v_synthPendingDepth_2724_ = lean_ctor_get(v___y_2691_, 5);
v_canUnfold_x3f_2725_ = lean_ctor_get(v___y_2691_, 6);
v_univApprox_2726_ = lean_ctor_get_uint8(v___y_2691_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2727_ = lean_ctor_get_uint8(v___y_2691_, sizeof(void*)*7 + 2);
v_cacheInferType_2728_ = lean_ctor_get_uint8(v___y_2691_, sizeof(void*)*7 + 3);
v___x_2729_ = 1;
if (v_isShared_2718_ == 0)
{
v_config_2731_ = v___x_2717_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 0, v_foApprox_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 1, v_ctxApprox_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 2, v_quasiPatternApprox_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 3, v_constApprox_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 4, v_isDefEqStuckEx_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 5, v_unificationHints_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 6, v_proofIrrelevance_2704_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 7, v_assignSyntheticOpaque_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 8, v_offsetCnstrs_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 10, v_etaStruct_2707_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 11, v_univApprox_2708_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 12, v_iota_2709_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 13, v_beta_2710_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 14, v_proj_2711_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 15, v_zeta_2712_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 16, v_zetaDelta_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 17, v_zetaUnused_2714_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, 18, v_zetaHave_2715_);
v_config_2731_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
uint64_t v___x_2732_; uint64_t v___x_2733_; uint64_t v___x_2734_; uint64_t v___x_2735_; uint64_t v___x_2736_; uint64_t v_key_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_ctor_set_uint8(v_config_2731_, 9, v___x_2729_);
v___x_2732_ = l_Lean_Meta_Context_configKey(v___y_2691_);
v___x_2733_ = 2ULL;
v___x_2734_ = lean_uint64_shift_right(v___x_2732_, v___x_2733_);
v___x_2735_ = lean_uint64_shift_left(v___x_2734_, v___x_2733_);
v___x_2736_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_2737_ = lean_uint64_lor(v___x_2735_, v___x_2736_);
v___x_2738_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2738_, 0, v_config_2731_);
lean_ctor_set_uint64(v___x_2738_, sizeof(void*)*1, v_key_2737_);
lean_inc(v_canUnfold_x3f_2725_);
lean_inc(v_synthPendingDepth_2724_);
lean_inc(v_defEqCtx_x3f_2723_);
lean_inc_ref(v_localInstances_2722_);
lean_inc_ref(v_lctx_2721_);
lean_inc(v_zetaDeltaSet_2720_);
v___x_2739_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
lean_ctor_set(v___x_2739_, 1, v_zetaDeltaSet_2720_);
lean_ctor_set(v___x_2739_, 2, v_lctx_2721_);
lean_ctor_set(v___x_2739_, 3, v_localInstances_2722_);
lean_ctor_set(v___x_2739_, 4, v_defEqCtx_x3f_2723_);
lean_ctor_set(v___x_2739_, 5, v_synthPendingDepth_2724_);
lean_ctor_set(v___x_2739_, 6, v_canUnfold_x3f_2725_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*7, v_trackZetaDelta_2719_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*7 + 1, v_univApprox_2726_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2727_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*7 + 3, v_cacheInferType_2728_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2690_);
lean_inc(v_a_2696_);
v___x_2740_ = lean_whnf(v_a_2696_, v___x_2739_, v___y_2690_, v___y_2694_, v___y_2692_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2740_);
v___x_2742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_2743_ = l_Lean_Expr_isConstOf(v_a_2741_, v___x_2742_);
lean_dec(v_a_2741_);
if (v___x_2743_ == 0)
{
lean_dec(v_a_2696_);
v___y_2660_ = v___y_2689_;
v___y_2661_ = v___y_2693_;
v___y_2662_ = v___y_2691_;
v___y_2663_ = v___y_2690_;
v___y_2664_ = v___y_2694_;
v___y_2665_ = v___y_2692_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2744_; 
lean_inc(v_a_2696_);
v___x_2744_ = l_Lean_Meta_mkEqRefl(v_a_2696_, v___y_2691_, v___y_2690_, v___y_2694_, v___y_2692_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
lean_inc(v_mvarId_2510_);
v___x_2746_ = l_Lean_MVarId_getType(v_mvarId_2510_, v___y_2691_, v___y_2690_, v___y_2694_, v___y_2692_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v_nargs_2748_; lean_object* v___x_2749_; lean_object* v_dummy_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
v_nargs_2748_ = l_Lean_Expr_getAppNumArgs(v_a_2696_);
v___x_2749_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2750_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2748_);
v___x_2751_ = lean_mk_array(v_nargs_2748_, v_dummy_2750_);
v___x_2752_ = lean_unsigned_to_nat(1u);
v___x_2753_ = lean_nat_sub(v_nargs_2748_, v___x_2752_);
lean_dec(v_nargs_2748_);
v___x_2754_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2696_, v___x_2751_, v___x_2753_);
v___x_2755_ = lean_array_push(v___x_2754_, v_a_2745_);
v___x_2756_ = l_Lean_mkAppN(v___x_2749_, v___x_2755_);
lean_dec_ref(v___x_2755_);
lean_inc(v_val_2541_);
v___x_2757_ = l_Lean_LocalDecl_toExpr(v_val_2541_);
v___x_2758_ = l_Lean_Meta_mkAbsurd(v_a_2747_, v___x_2757_, v___x_2756_, v___y_2691_, v___y_2690_, v___y_2694_, v___y_2692_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2760_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
lean_inc(v_mvarId_2510_);
v___x_2760_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2510_, v_a_2759_, v___y_2690_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2769_; 
lean_dec_ref(v___x_2658_);
lean_dec(v_val_2541_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v___x_2760_, 0);
lean_dec(v_unused_2770_);
v___x_2762_ = v___x_2760_;
v_isShared_2763_ = v_isSharedCheck_2769_;
goto v_resetjp_2761_;
}
else
{
lean_dec(v___x_2760_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2769_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2764_ = lean_box(v___x_2520_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 1);
lean_ctor_set(v___x_2762_, 0, v___x_2764_);
v___x_2766_ = v___x_2762_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v___x_2545_);
v_a_2527_ = v___x_2767_;
goto v___jp_2526_;
}
}
}
else
{
lean_object* v_a_2771_; 
v_a_2771_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2771_);
lean_dec_ref(v___x_2760_);
v___y_2679_ = v___y_2690_;
v___y_2680_ = v___y_2689_;
v___y_2681_ = v___y_2691_;
v___y_2682_ = v___y_2692_;
v___y_2683_ = v___y_2693_;
v___y_2684_ = v___y_2694_;
v_a_2685_ = v_a_2771_;
goto v___jp_2678_;
}
}
else
{
lean_object* v_a_2772_; 
v_a_2772_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2772_);
lean_dec_ref(v___x_2758_);
v___y_2679_ = v___y_2690_;
v___y_2680_ = v___y_2689_;
v___y_2681_ = v___y_2691_;
v___y_2682_ = v___y_2692_;
v___y_2683_ = v___y_2693_;
v___y_2684_ = v___y_2694_;
v_a_2685_ = v_a_2772_;
goto v___jp_2678_;
}
}
else
{
lean_object* v_a_2773_; 
lean_dec(v_a_2745_);
lean_dec(v_a_2696_);
v_a_2773_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2773_);
lean_dec_ref(v___x_2746_);
v___y_2679_ = v___y_2690_;
v___y_2680_ = v___y_2689_;
v___y_2681_ = v___y_2691_;
v___y_2682_ = v___y_2692_;
v___y_2683_ = v___y_2693_;
v___y_2684_ = v___y_2694_;
v_a_2685_ = v_a_2773_;
goto v___jp_2678_;
}
}
else
{
lean_object* v_a_2774_; 
lean_dec(v_a_2696_);
v_a_2774_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2774_);
lean_dec_ref(v___x_2744_);
v___y_2679_ = v___y_2690_;
v___y_2680_ = v___y_2689_;
v___y_2681_ = v___y_2691_;
v___y_2682_ = v___y_2692_;
v___y_2683_ = v___y_2693_;
v___y_2684_ = v___y_2694_;
v_a_2685_ = v_a_2774_;
goto v___jp_2678_;
}
}
}
else
{
lean_object* v_a_2775_; 
lean_dec(v_a_2696_);
v_a_2775_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2775_);
lean_dec_ref(v___x_2740_);
v___y_2679_ = v___y_2690_;
v___y_2680_ = v___y_2689_;
v___y_2681_ = v___y_2691_;
v___y_2682_ = v___y_2692_;
v___y_2683_ = v___y_2693_;
v___y_2684_ = v___y_2694_;
v_a_2685_ = v_a_2775_;
goto v___jp_2678_;
}
}
}
}
else
{
lean_object* v_a_2778_; 
v_a_2778_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2778_);
lean_dec_ref(v___x_2695_);
v___y_2679_ = v___y_2690_;
v___y_2680_ = v___y_2689_;
v___y_2681_ = v___y_2691_;
v___y_2682_ = v___y_2692_;
v___y_2683_ = v___y_2693_;
v___y_2684_ = v___y_2694_;
v_a_2685_ = v_a_2778_;
goto v___jp_2678_;
}
}
v___jp_2779_:
{
if (v___y_2786_ == 0)
{
v___y_2660_ = v___y_2780_;
v___y_2661_ = v___y_2784_;
v___y_2662_ = v___y_2782_;
v___y_2663_ = v___y_2781_;
v___y_2664_ = v___y_2785_;
v___y_2665_ = v___y_2783_;
goto v___jp_2659_;
}
else
{
v___y_2689_ = v___y_2780_;
v___y_2690_ = v___y_2781_;
v___y_2691_ = v___y_2782_;
v___y_2692_ = v___y_2783_;
v___y_2693_ = v___y_2784_;
v___y_2694_ = v___y_2785_;
goto v___jp_2688_;
}
}
v___jp_2787_:
{
if (v___y_2795_ == 0)
{
lean_dec_ref(v___y_2788_);
v___y_2780_ = v___y_2790_;
v___y_2781_ = v___y_2789_;
v___y_2782_ = v___y_2791_;
v___y_2783_ = v___y_2792_;
v___y_2784_ = v___y_2793_;
v___y_2785_ = v___y_2794_;
v___y_2786_ = v___x_2614_;
goto v___jp_2779_;
}
else
{
uint8_t v___x_2796_; 
v___x_2796_ = l_Lean_Expr_hasFVar(v___y_2788_);
lean_dec_ref(v___y_2788_);
if (v___x_2796_ == 0)
{
v___y_2689_ = v___y_2790_;
v___y_2690_ = v___y_2789_;
v___y_2691_ = v___y_2791_;
v___y_2692_ = v___y_2792_;
v___y_2693_ = v___y_2793_;
v___y_2694_ = v___y_2794_;
goto v___jp_2688_;
}
else
{
v___y_2780_ = v___y_2790_;
v___y_2781_ = v___y_2789_;
v___y_2782_ = v___y_2791_;
v___y_2783_ = v___y_2792_;
v___y_2784_ = v___y_2793_;
v___y_2785_ = v___y_2794_;
v___y_2786_ = v___x_2614_;
goto v___jp_2779_;
}
}
}
v___jp_2797_:
{
lean_object* v___x_2805_; 
lean_inc_ref(v___x_2658_);
v___x_2805_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2658_, v___y_2799_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; uint8_t v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref(v___x_2805_);
v___x_2807_ = l_Lean_Expr_hasMVar(v_a_2806_);
if (v___x_2807_ == 0)
{
v___y_2788_ = v_a_2806_;
v___y_2789_ = v___y_2799_;
v___y_2790_ = v___y_2798_;
v___y_2791_ = v___y_2800_;
v___y_2792_ = v___y_2801_;
v___y_2793_ = v___y_2802_;
v___y_2794_ = v___y_2803_;
v___y_2795_ = v___y_2804_;
goto v___jp_2787_;
}
else
{
v___y_2788_ = v_a_2806_;
v___y_2789_ = v___y_2799_;
v___y_2790_ = v___y_2798_;
v___y_2791_ = v___y_2800_;
v___y_2792_ = v___y_2801_;
v___y_2793_ = v___y_2802_;
v___y_2794_ = v___y_2803_;
v___y_2795_ = v___x_2614_;
goto v___jp_2787_;
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec_ref(v___x_2658_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2808_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2805_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2805_);
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
v___jp_2816_:
{
if (v___y_2823_ == 0)
{
v___y_2660_ = v___y_2817_;
v___y_2661_ = v___y_2821_;
v___y_2662_ = v___y_2819_;
v___y_2663_ = v___y_2818_;
v___y_2664_ = v___y_2822_;
v___y_2665_ = v___y_2820_;
goto v___jp_2659_;
}
else
{
v___y_2798_ = v___y_2817_;
v___y_2799_ = v___y_2818_;
v___y_2800_ = v___y_2819_;
v___y_2801_ = v___y_2820_;
v___y_2802_ = v___y_2821_;
v___y_2803_ = v___y_2822_;
v___y_2804_ = v___y_2823_;
goto v___jp_2797_;
}
}
v___jp_2824_:
{
uint8_t v_useDecide_2831_; 
v_useDecide_2831_ = lean_ctor_get_uint8(v_config_2509_, sizeof(void*)*1);
if (v_useDecide_2831_ == 0)
{
v___y_2817_ = v___y_2825_;
v___y_2818_ = v___y_2828_;
v___y_2819_ = v___y_2827_;
v___y_2820_ = v___y_2830_;
v___y_2821_ = v_isHEq_2826_;
v___y_2822_ = v___y_2829_;
v___y_2823_ = v___x_2614_;
goto v___jp_2816_;
}
else
{
uint8_t v___x_2832_; 
v___x_2832_ = l_Lean_Expr_hasFVar(v___x_2658_);
if (v___x_2832_ == 0)
{
v___y_2798_ = v___y_2825_;
v___y_2799_ = v___y_2828_;
v___y_2800_ = v___y_2827_;
v___y_2801_ = v___y_2830_;
v___y_2802_ = v_isHEq_2826_;
v___y_2803_ = v___y_2829_;
v___y_2804_ = v_useDecide_2831_;
goto v___jp_2797_;
}
else
{
v___y_2817_ = v___y_2825_;
v___y_2818_ = v___y_2828_;
v___y_2819_ = v___y_2827_;
v___y_2820_ = v___y_2830_;
v___y_2821_ = v_isHEq_2826_;
v___y_2822_ = v___y_2829_;
v___y_2823_ = v___x_2614_;
goto v___jp_2816_;
}
}
}
v___jp_2833_:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_Meta_isExprDefEq(v___y_2835_, v___y_2840_, v___y_2838_, v___y_2837_, v___y_2834_, v___y_2839_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; uint8_t v___x_2843_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = lean_unbox(v_a_2842_);
lean_dec(v_a_2842_);
if (v___x_2843_ == 0)
{
v___y_2825_ = v___y_2836_;
v_isHEq_2826_ = v___x_2520_;
v___y_2827_ = v___y_2838_;
v___y_2828_ = v___y_2837_;
v___y_2829_ = v___y_2834_;
v___y_2830_ = v___y_2839_;
goto v___jp_2824_;
}
else
{
lean_object* v___x_2844_; 
lean_dec_ref(v___x_2658_);
lean_dec_ref(v_config_2509_);
lean_inc(v_mvarId_2510_);
v___x_2844_ = l_Lean_MVarId_getType(v_mvarId_2510_, v___y_2838_, v___y_2837_, v___y_2834_, v___y_2839_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = l_Lean_LocalDecl_toExpr(v_val_2541_);
v___x_2847_ = l_Lean_Meta_mkEqOfHEq(v___x_2846_, v___x_2520_, v___y_2838_, v___y_2837_, v___y_2834_, v___y_2839_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref(v___x_2847_);
v___x_2849_ = l_Lean_Meta_mkNoConfusion(v_a_2845_, v_a_2848_, v___y_2838_, v___y_2837_, v___y_2834_, v___y_2839_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2510_, v_a_2850_, v___y_2837_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_dec_ref(v___x_2851_);
v___x_2852_ = lean_box(v___x_2520_);
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___x_2545_);
v_a_2527_ = v___x_2854_;
goto v___jp_2526_;
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
v_a_2855_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2851_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2851_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_2863_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2849_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2849_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_a_2845_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_2871_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2847_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2847_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_2879_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2844_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2844_);
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
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v___x_2658_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2887_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2841_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2841_);
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
v___jp_2895_:
{
lean_object* v___x_2901_; 
lean_inc_ref(v___x_2658_);
v___x_2901_ = l_Lean_Meta_matchHEq_x3f(v___x_2658_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref(v___x_2901_);
if (lean_obj_tag(v_a_2902_) == 1)
{
lean_object* v_val_2903_; lean_object* v_snd_2904_; lean_object* v_snd_2905_; lean_object* v_fst_2906_; lean_object* v_fst_2907_; lean_object* v_fst_2908_; lean_object* v_snd_2909_; lean_object* v___x_2910_; 
v_val_2903_ = lean_ctor_get(v_a_2902_, 0);
lean_inc(v_val_2903_);
lean_dec_ref(v_a_2902_);
v_snd_2904_ = lean_ctor_get(v_val_2903_, 1);
lean_inc(v_snd_2904_);
v_snd_2905_ = lean_ctor_get(v_snd_2904_, 1);
lean_inc(v_snd_2905_);
v_fst_2906_ = lean_ctor_get(v_val_2903_, 0);
lean_inc(v_fst_2906_);
lean_dec(v_val_2903_);
v_fst_2907_ = lean_ctor_get(v_snd_2904_, 0);
lean_inc(v_fst_2907_);
lean_dec(v_snd_2904_);
v_fst_2908_ = lean_ctor_get(v_snd_2905_, 0);
lean_inc(v_fst_2908_);
v_snd_2909_ = lean_ctor_get(v_snd_2905_, 1);
lean_inc(v_snd_2909_);
lean_dec(v_snd_2905_);
v___x_2910_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2907_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2910_);
if (lean_obj_tag(v_a_2911_) == 1)
{
lean_object* v_val_2912_; lean_object* v___x_2913_; 
v_val_2912_ = lean_ctor_get(v_a_2911_, 0);
lean_inc(v_val_2912_);
lean_dec_ref(v_a_2911_);
v___x_2913_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2909_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref(v___x_2913_);
if (lean_obj_tag(v_a_2914_) == 1)
{
lean_object* v_toConstantVal_2915_; lean_object* v_val_2916_; lean_object* v_toConstantVal_2917_; lean_object* v_name_2918_; lean_object* v_name_2919_; uint8_t v___x_2920_; 
v_toConstantVal_2915_ = lean_ctor_get(v_val_2912_, 0);
lean_inc_ref(v_toConstantVal_2915_);
lean_dec(v_val_2912_);
v_val_2916_ = lean_ctor_get(v_a_2914_, 0);
lean_inc(v_val_2916_);
lean_dec_ref(v_a_2914_);
v_toConstantVal_2917_ = lean_ctor_get(v_val_2916_, 0);
lean_inc_ref(v_toConstantVal_2917_);
lean_dec(v_val_2916_);
v_name_2918_ = lean_ctor_get(v_toConstantVal_2915_, 0);
lean_inc(v_name_2918_);
lean_dec_ref(v_toConstantVal_2915_);
v_name_2919_ = lean_ctor_get(v_toConstantVal_2917_, 0);
lean_inc(v_name_2919_);
lean_dec_ref(v_toConstantVal_2917_);
v___x_2920_ = lean_name_eq(v_name_2918_, v_name_2919_);
lean_dec(v_name_2919_);
lean_dec(v_name_2918_);
if (v___x_2920_ == 0)
{
v___y_2834_ = v___y_2899_;
v___y_2835_ = v_fst_2906_;
v___y_2836_ = v_isEq_2896_;
v___y_2837_ = v___y_2898_;
v___y_2838_ = v___y_2897_;
v___y_2839_ = v___y_2900_;
v___y_2840_ = v_fst_2908_;
goto v___jp_2833_;
}
else
{
if (v___x_2614_ == 0)
{
lean_dec(v_fst_2908_);
lean_dec(v_fst_2906_);
v___y_2825_ = v_isEq_2896_;
v_isHEq_2826_ = v___x_2520_;
v___y_2827_ = v___y_2897_;
v___y_2828_ = v___y_2898_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
goto v___jp_2824_;
}
else
{
v___y_2834_ = v___y_2899_;
v___y_2835_ = v_fst_2906_;
v___y_2836_ = v_isEq_2896_;
v___y_2837_ = v___y_2898_;
v___y_2838_ = v___y_2897_;
v___y_2839_ = v___y_2900_;
v___y_2840_ = v_fst_2908_;
goto v___jp_2833_;
}
}
}
else
{
lean_dec(v_a_2914_);
lean_dec(v_val_2912_);
lean_dec(v_fst_2908_);
lean_dec(v_fst_2906_);
v___y_2825_ = v_isEq_2896_;
v_isHEq_2826_ = v___x_2520_;
v___y_2827_ = v___y_2897_;
v___y_2828_ = v___y_2898_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_val_2912_);
lean_dec(v_fst_2908_);
lean_dec(v_fst_2906_);
lean_dec_ref(v___x_2658_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2921_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2913_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2913_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_dec(v_a_2911_);
lean_dec(v_snd_2909_);
lean_dec(v_fst_2908_);
lean_dec(v_fst_2906_);
v___y_2825_ = v_isEq_2896_;
v_isHEq_2826_ = v___x_2520_;
v___y_2827_ = v___y_2897_;
v___y_2828_ = v___y_2898_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_snd_2909_);
lean_dec(v_fst_2908_);
lean_dec(v_fst_2906_);
lean_dec_ref(v___x_2658_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2929_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2910_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2910_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
lean_dec(v_a_2902_);
v___y_2825_ = v_isEq_2896_;
v_isHEq_2826_ = v___x_2614_;
v___y_2827_ = v___y_2897_;
v___y_2828_ = v___y_2898_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v___x_2658_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2937_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2901_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2901_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
v___jp_2945_:
{
lean_object* v___x_2950_; 
lean_inc_ref(v___x_2658_);
v___x_2950_ = l_Lean_Meta_matchEq_x3f(v___x_2658_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref(v___x_2950_);
if (lean_obj_tag(v_a_2951_) == 1)
{
lean_object* v_val_2952_; lean_object* v_snd_2953_; lean_object* v_fst_2954_; lean_object* v_snd_2955_; lean_object* v___x_2956_; 
v_val_2952_ = lean_ctor_get(v_a_2951_, 0);
lean_inc(v_val_2952_);
lean_dec_ref(v_a_2951_);
v_snd_2953_ = lean_ctor_get(v_val_2952_, 1);
lean_inc(v_snd_2953_);
lean_dec(v_val_2952_);
v_fst_2954_ = lean_ctor_get(v_snd_2953_, 0);
lean_inc(v_fst_2954_);
v_snd_2955_ = lean_ctor_get(v_snd_2953_, 1);
lean_inc(v_snd_2955_);
lean_dec(v_snd_2953_);
v___x_2956_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2954_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref(v___x_2956_);
if (lean_obj_tag(v_a_2957_) == 1)
{
lean_object* v_val_2958_; lean_object* v___x_2959_; 
v_val_2958_ = lean_ctor_get(v_a_2957_, 0);
lean_inc(v_val_2958_);
lean_dec_ref(v_a_2957_);
v___x_2959_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2955_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref(v___x_2959_);
if (lean_obj_tag(v_a_2960_) == 1)
{
lean_object* v_toConstantVal_2961_; lean_object* v_val_2962_; lean_object* v_toConstantVal_2963_; lean_object* v_name_2964_; lean_object* v_name_2965_; uint8_t v___x_2966_; 
v_toConstantVal_2961_ = lean_ctor_get(v_val_2958_, 0);
lean_inc_ref(v_toConstantVal_2961_);
lean_dec(v_val_2958_);
v_val_2962_ = lean_ctor_get(v_a_2960_, 0);
lean_inc(v_val_2962_);
lean_dec_ref(v_a_2960_);
v_toConstantVal_2963_ = lean_ctor_get(v_val_2962_, 0);
lean_inc_ref(v_toConstantVal_2963_);
lean_dec(v_val_2962_);
v_name_2964_ = lean_ctor_get(v_toConstantVal_2961_, 0);
lean_inc(v_name_2964_);
lean_dec_ref(v_toConstantVal_2961_);
v_name_2965_ = lean_ctor_get(v_toConstantVal_2963_, 0);
lean_inc(v_name_2965_);
lean_dec_ref(v_toConstantVal_2963_);
v___x_2966_ = lean_name_eq(v_name_2964_, v_name_2965_);
lean_dec(v_name_2965_);
lean_dec(v_name_2964_);
if (v___x_2966_ == 0)
{
lean_dec_ref(v___x_2658_);
lean_dec_ref(v_config_2509_);
v___y_2547_ = v___y_2947_;
v___y_2548_ = v___y_2946_;
v___y_2549_ = v___y_2948_;
v___y_2550_ = v___y_2949_;
goto v___jp_2546_;
}
else
{
if (v___x_2614_ == 0)
{
lean_del_object(v___x_2543_);
v_isEq_2896_ = v___x_2520_;
v___y_2897_ = v___y_2946_;
v___y_2898_ = v___y_2947_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
goto v___jp_2895_;
}
else
{
lean_dec_ref(v___x_2658_);
lean_dec_ref(v_config_2509_);
v___y_2547_ = v___y_2947_;
v___y_2548_ = v___y_2946_;
v___y_2549_ = v___y_2948_;
v___y_2550_ = v___y_2949_;
goto v___jp_2546_;
}
}
}
else
{
lean_dec(v_a_2960_);
lean_dec(v_val_2958_);
lean_del_object(v___x_2543_);
v_isEq_2896_ = v___x_2520_;
v___y_2897_ = v___y_2946_;
v___y_2898_ = v___y_2947_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
goto v___jp_2895_;
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_val_2958_);
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2967_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2959_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2959_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_dec(v_a_2957_);
lean_dec(v_snd_2955_);
lean_del_object(v___x_2543_);
v_isEq_2896_ = v___x_2520_;
v___y_2897_ = v___y_2946_;
v___y_2898_ = v___y_2947_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
goto v___jp_2895_;
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_snd_2955_);
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2975_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2956_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2956_);
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
lean_dec(v_a_2951_);
lean_del_object(v___x_2543_);
v_isEq_2896_ = v___x_2614_;
v___y_2897_ = v___y_2946_;
v___y_2898_ = v___y_2947_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
goto v___jp_2895_;
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2983_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2950_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2950_);
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
v___jp_2991_:
{
lean_object* v___x_2996_; 
lean_inc_ref(v___x_2658_);
v___x_2996_ = l_refutableHasNotBit_x3f(v___x_2658_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref(v___x_2996_);
if (lean_obj_tag(v_a_2997_) == 1)
{
lean_object* v_val_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3037_; 
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec_ref(v_config_2509_);
v_val_2998_ = lean_ctor_get(v_a_2997_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_a_2997_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3000_ = v_a_2997_;
v_isShared_3001_ = v_isSharedCheck_3037_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_val_2998_);
lean_dec(v_a_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3037_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; 
lean_inc(v_mvarId_2510_);
v___x_3002_ = l_Lean_MVarId_getType(v_mvarId_2510_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref(v___x_3002_);
v___x_3004_ = l_Lean_LocalDecl_toExpr(v_val_2541_);
v___x_3005_ = l_Lean_Meta_mkAbsurd(v_a_3003_, v_val_2998_, v___x_3004_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref(v___x_3005_);
v___x_3007_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2510_, v_a_3006_, v___y_2993_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3010_; 
lean_dec_ref(v___x_3007_);
v___x_3008_ = lean_box(v___x_2520_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3008_);
v___x_3010_ = v___x_3000_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; 
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___x_2545_);
v_a_2527_ = v___x_3011_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_del_object(v___x_3000_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
v_a_3013_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_3007_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3007_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_del_object(v___x_3000_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_3021_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3005_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3005_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_del_object(v___x_3000_);
lean_dec(v_val_2998_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_3029_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3002_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3002_);
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
}
else
{
lean_object* v___x_3038_; 
lean_dec(v_a_2997_);
lean_inc_ref(v___x_2658_);
v___x_3038_ = l_Lean_Meta_matchNe_x3f(v___x_2658_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref(v___x_3038_);
if (lean_obj_tag(v_a_3039_) == 1)
{
lean_object* v_val_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3109_; 
v_val_3040_ = lean_ctor_get(v_a_3039_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_a_3039_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3042_ = v_a_3039_;
v_isShared_3043_ = v_isSharedCheck_3109_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_val_3040_);
lean_dec(v_a_3039_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3109_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_snd_3044_; lean_object* v_fst_3045_; lean_object* v_snd_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3108_; 
v_snd_3044_ = lean_ctor_get(v_val_3040_, 1);
lean_inc(v_snd_3044_);
lean_dec(v_val_3040_);
v_fst_3045_ = lean_ctor_get(v_snd_3044_, 0);
v_snd_3046_ = lean_ctor_get(v_snd_3044_, 1);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_snd_3044_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3048_ = v_snd_3044_;
v_isShared_3049_ = v_isSharedCheck_3108_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_snd_3046_);
lean_inc(v_fst_3045_);
lean_dec(v_snd_3044_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3108_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; 
lean_inc(v_fst_3045_);
v___x_3050_ = l_Lean_Meta_isExprDefEq(v_fst_3045_, v_snd_3046_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; uint8_t v___x_3052_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___x_3050_);
v___x_3052_ = lean_unbox(v_a_3051_);
lean_dec(v_a_3051_);
if (v___x_3052_ == 0)
{
lean_del_object(v___x_3048_);
lean_dec(v_fst_3045_);
lean_del_object(v___x_3042_);
v___y_2946_ = v___y_2992_;
v___y_2947_ = v___y_2993_;
v___y_2948_ = v___y_2994_;
v___y_2949_ = v___y_2995_;
goto v___jp_2945_;
}
else
{
lean_object* v___x_3053_; 
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec_ref(v_config_2509_);
lean_inc(v_mvarId_2510_);
v___x_3053_ = l_Lean_MVarId_getType(v_mvarId_2510_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3053_);
v___x_3055_ = l_Lean_Meta_mkEqRefl(v_fst_3045_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = l_Lean_LocalDecl_toExpr(v_val_2541_);
v___x_3058_ = l_Lean_Meta_mkAbsurd(v_a_3054_, v_a_3056_, v___x_3057_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2510_, v_a_3059_, v___y_2993_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_dec_ref(v___x_3060_);
v___x_3061_ = lean_box(v___x_2520_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3061_);
v___x_3063_ = v___x_3042_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3065_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 1, v___x_2545_);
lean_ctor_set(v___x_3048_, 0, v___x_3063_);
v___x_3065_ = v___x_3048_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___x_2545_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
v_a_2527_ = v___x_3065_;
goto v___jp_2526_;
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_del_object(v___x_3048_);
lean_del_object(v___x_3042_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
v_a_3068_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3060_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3060_);
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
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_del_object(v___x_3048_);
lean_del_object(v___x_3042_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_3076_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3058_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3058_);
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
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_3054_);
lean_del_object(v___x_3048_);
lean_del_object(v___x_3042_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_3084_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3055_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3055_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_del_object(v___x_3048_);
lean_dec(v_fst_3045_);
lean_del_object(v___x_3042_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_3092_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3053_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3053_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_del_object(v___x_3048_);
lean_dec(v_fst_3045_);
lean_del_object(v___x_3042_);
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_3100_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3050_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3050_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3039_);
v___y_2946_ = v___y_2992_;
v___y_2947_ = v___y_2993_;
v___y_2948_ = v___y_2994_;
v___y_2949_ = v___y_2995_;
goto v___jp_2945_;
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_3110_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3038_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3038_);
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
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v___x_2658_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_3118_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_2996_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_2996_);
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
}
else
{
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
v_a_2535_ = v___x_2586_;
goto v___jp_2534_;
}
v___jp_2546_:
{
lean_object* v___x_2551_; 
lean_inc(v_mvarId_2510_);
v___x_2551_ = l_Lean_MVarId_getType(v_mvarId_2510_, v___y_2548_, v___y_2547_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref(v___x_2551_);
v___x_2553_ = l_Lean_LocalDecl_toExpr(v_val_2541_);
v___x_2554_ = l_Lean_Meta_mkNoConfusion(v_a_2552_, v___x_2553_, v___y_2548_, v___y_2547_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2556_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref(v___x_2554_);
v___x_2556_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2510_, v_a_2555_, v___y_2547_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
lean_dec_ref(v___x_2556_);
v___x_2557_ = lean_box(v___x_2520_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2557_);
v___x_2559_ = v___x_2543_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v___x_2545_);
v_a_2527_ = v___x_2560_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_del_object(v___x_2543_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
v_a_2562_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2556_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2556_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_del_object(v___x_2543_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_2570_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2554_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2554_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
v_a_2578_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2551_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2551_);
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
v___jp_2587_:
{
lean_object* v_searchFuel_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_searchFuel_2592_ = lean_ctor_get(v_config_2509_, 0);
v___x_2593_ = l_Lean_LocalDecl_fvarId(v_val_2541_);
lean_dec(v_val_2541_);
lean_inc(v_searchFuel_2592_);
lean_inc(v_mvarId_2510_);
v___x_2594_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2510_, v___x_2593_, v_searchFuel_2592_, v___y_2590_, v___y_2589_, v___y_2591_, v___y_2588_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; uint8_t v___x_2596_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref(v___x_2594_);
v___x_2596_ = lean_unbox(v_a_2595_);
lean_dec(v_a_2595_);
if (v___x_2596_ == 0)
{
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
v_a_2535_ = v___x_2586_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v___x_2597_ = lean_box(v___x_2520_);
v___x_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v___x_2545_);
v_a_2527_ = v___x_2599_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2600_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2594_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2594_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
v___jp_2608_:
{
if (v___y_2613_ == 0)
{
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
v_a_2535_ = v___x_2586_;
goto v___jp_2534_;
}
else
{
v___y_2588_ = v___y_2609_;
v___y_2589_ = v___y_2611_;
v___y_2590_ = v___y_2610_;
v___y_2591_ = v___y_2612_;
goto v___jp_2587_;
}
}
v___jp_2615_:
{
if (v___y_2620_ == 0)
{
v___y_2588_ = v___y_2616_;
v___y_2589_ = v___y_2618_;
v___y_2590_ = v___y_2617_;
v___y_2591_ = v___y_2619_;
goto v___jp_2587_;
}
else
{
v___y_2609_ = v___y_2616_;
v___y_2610_ = v___y_2617_;
v___y_2611_ = v___y_2618_;
v___y_2612_ = v___y_2619_;
v___y_2613_ = v___x_2614_;
goto v___jp_2608_;
}
}
v___jp_2621_:
{
if (v___y_2627_ == 0)
{
v___y_2609_ = v___y_2622_;
v___y_2610_ = v___y_2624_;
v___y_2611_ = v___y_2623_;
v___y_2612_ = v___y_2625_;
v___y_2613_ = v___x_2614_;
goto v___jp_2608_;
}
else
{
v___y_2616_ = v___y_2622_;
v___y_2617_ = v___y_2624_;
v___y_2618_ = v___y_2623_;
v___y_2619_ = v___y_2625_;
v___y_2620_ = v___y_2626_;
goto v___jp_2615_;
}
}
v___jp_2628_:
{
uint8_t v_emptyType_2635_; 
v_emptyType_2635_ = lean_ctor_get_uint8(v_config_2509_, sizeof(void*)*1 + 1);
if (v_emptyType_2635_ == 0)
{
v___y_2622_ = v___y_2634_;
v___y_2623_ = v___y_2632_;
v___y_2624_ = v___y_2631_;
v___y_2625_ = v___y_2633_;
v___y_2626_ = v___y_2630_;
v___y_2627_ = v___x_2614_;
goto v___jp_2621_;
}
else
{
if (v___y_2629_ == 0)
{
v___y_2616_ = v___y_2634_;
v___y_2617_ = v___y_2631_;
v___y_2618_ = v___y_2632_;
v___y_2619_ = v___y_2633_;
v___y_2620_ = v___y_2630_;
goto v___jp_2615_;
}
else
{
v___y_2622_ = v___y_2634_;
v___y_2623_ = v___y_2632_;
v___y_2624_ = v___y_2631_;
v___y_2625_ = v___y_2633_;
v___y_2626_ = v___y_2630_;
v___y_2627_ = v___x_2614_;
goto v___jp_2621_;
}
}
}
v___jp_2636_:
{
if (v___y_2643_ == 0)
{
v___y_2629_ = v___y_2638_;
v___y_2630_ = v___y_2641_;
v___y_2631_ = v___y_2639_;
v___y_2632_ = v___y_2637_;
v___y_2633_ = v___y_2642_;
v___y_2634_ = v___y_2640_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2644_; 
lean_inc(v_val_2541_);
lean_inc(v_mvarId_2510_);
v___x_2644_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2510_, v_val_2541_, v___y_2639_, v___y_2637_, v___y_2642_, v___y_2640_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; uint8_t v___x_2646_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref(v___x_2644_);
v___x_2646_ = lean_unbox(v_a_2645_);
lean_dec(v_a_2645_);
if (v___x_2646_ == 0)
{
v___y_2629_ = v___y_2638_;
v___y_2630_ = v___y_2641_;
v___y_2631_ = v___y_2639_;
v___y_2632_ = v___y_2637_;
v___y_2633_ = v___y_2642_;
v___y_2634_ = v___y_2640_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec(v_val_2541_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v___x_2647_ = lean_box(v___x_2520_);
v___x_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
lean_ctor_set(v___x_2649_, 1, v___x_2545_);
v_a_2527_ = v___x_2649_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v_val_2541_);
lean_del_object(v___x_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_mvarId_2510_);
lean_dec_ref(v_config_2509_);
v_a_2650_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2644_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2644_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
}
}
v___jp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_a_2527_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2528_);
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_snd_2522_);
v___x_2530_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
return v___x_2531_;
}
}
v___jp_2534_:
{
lean_object* v___x_2536_; size_t v___x_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2533_);
lean_ctor_set(v___x_2536_, 1, v_a_2535_);
v___x_2537_ = ((size_t)1ULL);
v___x_2538_ = lean_usize_add(v_i_2513_, v___x_2537_);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2509_, v_mvarId_2510_, v_as_2511_, v_sz_2512_, v___x_2538_, v___x_2536_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
return v___x_2539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3192_, lean_object* v_mvarId_3193_, lean_object* v_as_3194_, lean_object* v_sz_3195_, lean_object* v_i_3196_, lean_object* v_b_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
size_t v_sz_boxed_3203_; size_t v_i_boxed_3204_; lean_object* v_res_3205_; 
v_sz_boxed_3203_ = lean_unbox_usize(v_sz_3195_);
lean_dec(v_sz_3195_);
v_i_boxed_3204_ = lean_unbox_usize(v_i_3196_);
lean_dec(v_i_3196_);
v_res_3205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3192_, v_mvarId_3193_, v_as_3194_, v_sz_boxed_3203_, v_i_boxed_3204_, v_b_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec_ref(v_as_3194_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3209_, lean_object* v_mvarId_3210_, lean_object* v_as_3211_, size_t v_sz_3212_, size_t v_i_3213_, lean_object* v_b_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
uint8_t v___x_3220_; 
v___x_3220_ = lean_usize_dec_lt(v_i_3213_, v_sz_3212_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_b_3214_);
return v___x_3221_;
}
else
{
lean_object* v_snd_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3910_; 
v_snd_3222_ = lean_ctor_get(v_b_3214_, 1);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_b_3214_);
if (v_isSharedCheck_3910_ == 0)
{
lean_object* v_unused_3911_; 
v_unused_3911_ = lean_ctor_get(v_b_3214_, 0);
lean_dec(v_unused_3911_);
v___x_3224_ = v_b_3214_;
v_isShared_3225_ = v_isSharedCheck_3910_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_snd_3222_);
lean_dec(v_b_3214_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3910_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v_a_3227_; lean_object* v___x_3233_; lean_object* v_a_3235_; lean_object* v_a_3240_; 
v___x_3233_ = lean_box(0);
v_a_3240_ = lean_array_uget(v_as_3211_, v_i_3213_);
if (lean_obj_tag(v_a_3240_) == 0)
{
lean_del_object(v___x_3224_);
v_a_3235_ = v_snd_3222_;
goto v___jp_3234_;
}
else
{
lean_object* v_val_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3909_; 
v_val_3241_ = lean_ctor_get(v_a_3240_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_a_3240_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3243_ = v_a_3240_;
v_isShared_3244_ = v_isSharedCheck_3909_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_val_3241_);
lean_dec(v_a_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3909_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___x_3287_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; uint8_t v___y_3315_; uint8_t v___x_3316_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; uint8_t v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; uint8_t v___y_3327_; lean_object* v___y_3328_; uint8_t v___y_3329_; uint8_t v___y_3331_; uint8_t v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3339_; uint8_t v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; uint8_t v___y_3343_; lean_object* v___y_3344_; uint8_t v___y_3345_; 
v___x_3245_ = lean_box(0);
v___x_3287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3316_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3241_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3361_; uint8_t v___y_3363_; uint8_t v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; uint8_t v___y_3376_; lean_object* v___y_3377_; uint8_t v___y_3378_; uint8_t v___y_3379_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; uint8_t v___y_3385_; lean_object* v___y_3386_; uint8_t v___y_3387_; lean_object* v_a_3388_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; uint8_t v___y_3395_; lean_object* v___y_3396_; uint8_t v___y_3397_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; uint8_t v___y_3493_; lean_object* v___y_3494_; uint8_t v___y_3495_; uint8_t v___y_3496_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; uint8_t v___y_3501_; lean_object* v___y_3502_; uint8_t v___y_3503_; lean_object* v___y_3504_; uint8_t v___y_3505_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; uint8_t v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3513_; uint8_t v___y_3514_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; uint8_t v___y_3530_; lean_object* v___y_3531_; uint8_t v___y_3532_; uint8_t v___y_3533_; uint8_t v___y_3535_; uint8_t v_isHEq_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; uint8_t v_isEq_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___x_3839_; 
v___x_3361_ = l_Lean_LocalDecl_type(v_val_3241_);
lean_inc_ref(v___x_3361_);
v___x_3839_ = l_Lean_Meta_matchNot_x3f(v___x_3361_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref(v___x_3839_);
if (lean_obj_tag(v_a_3840_) == 1)
{
lean_object* v_val_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3900_; 
v_val_3841_ = lean_ctor_get(v_a_3840_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v_a_3840_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3843_ = v_a_3840_;
v_isShared_3844_ = v_isSharedCheck_3900_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_val_3841_);
lean_dec(v_a_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3900_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3841_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref(v___x_3845_);
if (lean_obj_tag(v_a_3846_) == 1)
{
lean_object* v_val_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3891_; 
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec_ref(v_config_3209_);
v_val_3847_ = lean_ctor_get(v_a_3846_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_a_3846_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3849_ = v_a_3846_;
v_isShared_3850_ = v_isSharedCheck_3891_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_val_3847_);
lean_dec(v_a_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3891_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; 
lean_inc(v_mvarId_3210_);
v___x_3851_ = l_Lean_MVarId_getType(v_mvarId_3210_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref(v___x_3851_);
v___x_3853_ = l_Lean_LocalDecl_toExpr(v_val_3241_);
v___x_3854_ = l_Lean_mkFVar(v_val_3847_);
v___x_3855_ = l_Lean_Expr_app___override(v___x_3853_, v___x_3854_);
v___x_3856_ = l_Lean_Meta_mkFalseElim(v_a_3852_, v___x_3855_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___x_3856_);
v___x_3858_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3210_, v_a_3857_, v___y_3216_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
lean_dec_ref(v___x_3858_);
v___x_3859_ = lean_box(v___x_3220_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3859_);
v___x_3861_ = v___x_3849_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; lean_object* v___x_3864_; 
v___x_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
lean_ctor_set(v___x_3862_, 1, v___x_3245_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3862_);
v___x_3864_ = v___x_3843_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
v_a_3227_ = v___x_3864_;
goto v___jp_3226_;
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_del_object(v___x_3849_);
lean_del_object(v___x_3843_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
v_a_3867_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3858_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3858_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_del_object(v___x_3849_);
lean_del_object(v___x_3843_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3875_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3856_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3856_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_del_object(v___x_3849_);
lean_dec(v_val_3847_);
lean_del_object(v___x_3843_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3883_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3851_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3851_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
else
{
lean_dec(v_a_3846_);
lean_del_object(v___x_3843_);
v___y_3703_ = v___y_3215_;
v___y_3704_ = v___y_3216_;
v___y_3705_ = v___y_3217_;
v___y_3706_ = v___y_3218_;
goto v___jp_3702_;
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_del_object(v___x_3843_);
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3892_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3845_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3845_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
else
{
lean_dec(v_a_3840_);
v___y_3703_ = v___y_3215_;
v___y_3704_ = v___y_3216_;
v___y_3705_ = v___y_3217_;
v___y_3706_ = v___y_3218_;
goto v___jp_3702_;
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3901_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3839_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3839_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
v___jp_3362_:
{
uint8_t v_genDiseq_3369_; 
v_genDiseq_3369_ = lean_ctor_get_uint8(v_config_3209_, sizeof(void*)*1 + 2);
if (v_genDiseq_3369_ == 0)
{
lean_dec_ref(v___x_3361_);
v___y_3339_ = v___y_3365_;
v___y_3340_ = v___y_3363_;
v___y_3341_ = v___y_3366_;
v___y_3342_ = v___y_3367_;
v___y_3343_ = v___y_3364_;
v___y_3344_ = v___y_3368_;
v___y_3345_ = v___x_3316_;
goto v___jp_3338_;
}
else
{
uint8_t v___x_3370_; 
v___x_3370_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3361_);
v___y_3339_ = v___y_3365_;
v___y_3340_ = v___y_3363_;
v___y_3341_ = v___y_3366_;
v___y_3342_ = v___y_3367_;
v___y_3343_ = v___y_3364_;
v___y_3344_ = v___y_3368_;
v___y_3345_ = v___x_3370_;
goto v___jp_3338_;
}
}
v___jp_3371_:
{
if (v___y_3379_ == 0)
{
lean_dec_ref(v___y_3374_);
v___y_3363_ = v___y_3376_;
v___y_3364_ = v___y_3378_;
v___y_3365_ = v___y_3372_;
v___y_3366_ = v___y_3373_;
v___y_3367_ = v___y_3377_;
v___y_3368_ = v___y_3375_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3380_; 
lean_dec_ref(v___x_3361_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v___x_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___y_3374_);
return v___x_3380_;
}
}
v___jp_3381_:
{
uint8_t v___x_3389_; 
v___x_3389_ = l_Lean_Exception_isInterrupt(v_a_3388_);
if (v___x_3389_ == 0)
{
uint8_t v___x_3390_; 
lean_inc_ref(v_a_3388_);
v___x_3390_ = l_Lean_Exception_isRuntime(v_a_3388_);
v___y_3372_ = v___y_3382_;
v___y_3373_ = v___y_3383_;
v___y_3374_ = v_a_3388_;
v___y_3375_ = v___y_3384_;
v___y_3376_ = v___y_3385_;
v___y_3377_ = v___y_3386_;
v___y_3378_ = v___y_3387_;
v___y_3379_ = v___x_3390_;
goto v___jp_3371_;
}
else
{
v___y_3372_ = v___y_3382_;
v___y_3373_ = v___y_3383_;
v___y_3374_ = v_a_3388_;
v___y_3375_ = v___y_3384_;
v___y_3376_ = v___y_3385_;
v___y_3377_ = v___y_3386_;
v___y_3378_ = v___y_3387_;
v___y_3379_ = v___x_3389_;
goto v___jp_3371_;
}
}
v___jp_3391_:
{
lean_object* v___x_3398_; 
lean_inc_ref(v___x_3361_);
v___x_3398_ = l_Lean_Meta_mkDecide(v___x_3361_, v___y_3392_, v___y_3393_, v___y_3396_, v___y_3394_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; uint8_t v_foApprox_3401_; uint8_t v_ctxApprox_3402_; uint8_t v_quasiPatternApprox_3403_; uint8_t v_constApprox_3404_; uint8_t v_isDefEqStuckEx_3405_; uint8_t v_unificationHints_3406_; uint8_t v_proofIrrelevance_3407_; uint8_t v_assignSyntheticOpaque_3408_; uint8_t v_offsetCnstrs_3409_; uint8_t v_etaStruct_3410_; uint8_t v_univApprox_3411_; uint8_t v_iota_3412_; uint8_t v_beta_3413_; uint8_t v_proj_3414_; uint8_t v_zeta_3415_; uint8_t v_zetaDelta_3416_; uint8_t v_zetaUnused_3417_; uint8_t v_zetaHave_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3487_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = l_Lean_Meta_Context_config(v___y_3392_);
v_foApprox_3401_ = lean_ctor_get_uint8(v___x_3400_, 0);
v_ctxApprox_3402_ = lean_ctor_get_uint8(v___x_3400_, 1);
v_quasiPatternApprox_3403_ = lean_ctor_get_uint8(v___x_3400_, 2);
v_constApprox_3404_ = lean_ctor_get_uint8(v___x_3400_, 3);
v_isDefEqStuckEx_3405_ = lean_ctor_get_uint8(v___x_3400_, 4);
v_unificationHints_3406_ = lean_ctor_get_uint8(v___x_3400_, 5);
v_proofIrrelevance_3407_ = lean_ctor_get_uint8(v___x_3400_, 6);
v_assignSyntheticOpaque_3408_ = lean_ctor_get_uint8(v___x_3400_, 7);
v_offsetCnstrs_3409_ = lean_ctor_get_uint8(v___x_3400_, 8);
v_etaStruct_3410_ = lean_ctor_get_uint8(v___x_3400_, 10);
v_univApprox_3411_ = lean_ctor_get_uint8(v___x_3400_, 11);
v_iota_3412_ = lean_ctor_get_uint8(v___x_3400_, 12);
v_beta_3413_ = lean_ctor_get_uint8(v___x_3400_, 13);
v_proj_3414_ = lean_ctor_get_uint8(v___x_3400_, 14);
v_zeta_3415_ = lean_ctor_get_uint8(v___x_3400_, 15);
v_zetaDelta_3416_ = lean_ctor_get_uint8(v___x_3400_, 16);
v_zetaUnused_3417_ = lean_ctor_get_uint8(v___x_3400_, 17);
v_zetaHave_3418_ = lean_ctor_get_uint8(v___x_3400_, 18);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3420_ = v___x_3400_;
v_isShared_3421_ = v_isSharedCheck_3487_;
goto v_resetjp_3419_;
}
else
{
lean_dec(v___x_3400_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3487_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
uint8_t v_trackZetaDelta_3422_; lean_object* v_zetaDeltaSet_3423_; lean_object* v_lctx_3424_; lean_object* v_localInstances_3425_; lean_object* v_defEqCtx_x3f_3426_; lean_object* v_synthPendingDepth_3427_; lean_object* v_canUnfold_x3f_3428_; uint8_t v_univApprox_3429_; uint8_t v_inTypeClassResolution_3430_; uint8_t v_cacheInferType_3431_; uint8_t v___x_3432_; lean_object* v_config_3434_; 
v_trackZetaDelta_3422_ = lean_ctor_get_uint8(v___y_3392_, sizeof(void*)*7);
v_zetaDeltaSet_3423_ = lean_ctor_get(v___y_3392_, 1);
v_lctx_3424_ = lean_ctor_get(v___y_3392_, 2);
v_localInstances_3425_ = lean_ctor_get(v___y_3392_, 3);
v_defEqCtx_x3f_3426_ = lean_ctor_get(v___y_3392_, 4);
v_synthPendingDepth_3427_ = lean_ctor_get(v___y_3392_, 5);
v_canUnfold_x3f_3428_ = lean_ctor_get(v___y_3392_, 6);
v_univApprox_3429_ = lean_ctor_get_uint8(v___y_3392_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3430_ = lean_ctor_get_uint8(v___y_3392_, sizeof(void*)*7 + 2);
v_cacheInferType_3431_ = lean_ctor_get_uint8(v___y_3392_, sizeof(void*)*7 + 3);
v___x_3432_ = 1;
if (v_isShared_3421_ == 0)
{
v_config_3434_ = v___x_3420_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 0, v_foApprox_3401_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 1, v_ctxApprox_3402_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 2, v_quasiPatternApprox_3403_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 3, v_constApprox_3404_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 4, v_isDefEqStuckEx_3405_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 5, v_unificationHints_3406_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 6, v_proofIrrelevance_3407_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 7, v_assignSyntheticOpaque_3408_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 8, v_offsetCnstrs_3409_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 10, v_etaStruct_3410_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 11, v_univApprox_3411_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 12, v_iota_3412_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 13, v_beta_3413_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 14, v_proj_3414_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 15, v_zeta_3415_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 16, v_zetaDelta_3416_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 17, v_zetaUnused_3417_);
lean_ctor_set_uint8(v_reuseFailAlloc_3486_, 18, v_zetaHave_3418_);
v_config_3434_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
uint64_t v___x_3435_; uint64_t v___x_3436_; uint64_t v___x_3437_; uint64_t v___x_3438_; uint64_t v___x_3439_; uint64_t v_key_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_ctor_set_uint8(v_config_3434_, 9, v___x_3432_);
v___x_3435_ = l_Lean_Meta_Context_configKey(v___y_3392_);
v___x_3436_ = 2ULL;
v___x_3437_ = lean_uint64_shift_right(v___x_3435_, v___x_3436_);
v___x_3438_ = lean_uint64_shift_left(v___x_3437_, v___x_3436_);
v___x_3439_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_3440_ = lean_uint64_lor(v___x_3438_, v___x_3439_);
v___x_3441_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3441_, 0, v_config_3434_);
lean_ctor_set_uint64(v___x_3441_, sizeof(void*)*1, v_key_3440_);
lean_inc(v_canUnfold_x3f_3428_);
lean_inc(v_synthPendingDepth_3427_);
lean_inc(v_defEqCtx_x3f_3426_);
lean_inc_ref(v_localInstances_3425_);
lean_inc_ref(v_lctx_3424_);
lean_inc(v_zetaDeltaSet_3423_);
v___x_3442_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
lean_ctor_set(v___x_3442_, 1, v_zetaDeltaSet_3423_);
lean_ctor_set(v___x_3442_, 2, v_lctx_3424_);
lean_ctor_set(v___x_3442_, 3, v_localInstances_3425_);
lean_ctor_set(v___x_3442_, 4, v_defEqCtx_x3f_3426_);
lean_ctor_set(v___x_3442_, 5, v_synthPendingDepth_3427_);
lean_ctor_set(v___x_3442_, 6, v_canUnfold_x3f_3428_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*7, v_trackZetaDelta_3422_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*7 + 1, v_univApprox_3429_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3430_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*7 + 3, v_cacheInferType_3431_);
lean_inc(v___y_3394_);
lean_inc_ref(v___y_3396_);
lean_inc(v___y_3393_);
lean_inc(v_a_3399_);
v___x_3443_ = lean_whnf(v_a_3399_, v___x_3442_, v___y_3393_, v___y_3396_, v___y_3394_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref(v___x_3443_);
v___x_3445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_3446_ = l_Lean_Expr_isConstOf(v_a_3444_, v___x_3445_);
lean_dec(v_a_3444_);
if (v___x_3446_ == 0)
{
lean_dec(v_a_3399_);
v___y_3363_ = v___y_3395_;
v___y_3364_ = v___y_3397_;
v___y_3365_ = v___y_3392_;
v___y_3366_ = v___y_3393_;
v___y_3367_ = v___y_3396_;
v___y_3368_ = v___y_3394_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3447_; 
lean_inc(v_a_3399_);
v___x_3447_ = l_Lean_Meta_mkEqRefl(v_a_3399_, v___y_3392_, v___y_3393_, v___y_3396_, v___y_3394_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3449_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref(v___x_3447_);
lean_inc(v_mvarId_3210_);
v___x_3449_ = l_Lean_MVarId_getType(v_mvarId_3210_, v___y_3392_, v___y_3393_, v___y_3396_, v___y_3394_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v_nargs_3451_; lean_object* v___x_3452_; lean_object* v_dummy_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
v_nargs_3451_ = l_Lean_Expr_getAppNumArgs(v_a_3399_);
v___x_3452_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_3453_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_3451_);
v___x_3454_ = lean_mk_array(v_nargs_3451_, v_dummy_3453_);
v___x_3455_ = lean_unsigned_to_nat(1u);
v___x_3456_ = lean_nat_sub(v_nargs_3451_, v___x_3455_);
lean_dec(v_nargs_3451_);
v___x_3457_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3399_, v___x_3454_, v___x_3456_);
v___x_3458_ = lean_array_push(v___x_3457_, v_a_3448_);
v___x_3459_ = l_Lean_mkAppN(v___x_3452_, v___x_3458_);
lean_dec_ref(v___x_3458_);
lean_inc(v_val_3241_);
v___x_3460_ = l_Lean_LocalDecl_toExpr(v_val_3241_);
v___x_3461_ = l_Lean_Meta_mkAbsurd(v_a_3450_, v___x_3460_, v___x_3459_, v___y_3392_, v___y_3393_, v___y_3396_, v___y_3394_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3481_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3481_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3481_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; 
lean_inc(v_mvarId_3210_);
v___x_3466_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3210_, v_a_3462_, v___y_3393_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref(v___x_3361_);
lean_dec(v_val_3241_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; 
v_unused_3479_ = lean_ctor_get(v___x_3466_, 0);
lean_dec(v_unused_3479_);
v___x_3468_ = v___x_3466_;
v_isShared_3469_ = v_isSharedCheck_3478_;
goto v_resetjp_3467_;
}
else
{
lean_dec(v___x_3466_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3478_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3470_ = lean_box(v___x_3220_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set_tag(v___x_3468_, 1);
lean_ctor_set(v___x_3468_, 0, v___x_3470_);
v___x_3472_ = v___x_3468_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
lean_ctor_set(v___x_3473_, 1, v___x_3245_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3473_);
v___x_3475_ = v___x_3464_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
v_a_3227_ = v___x_3475_;
goto v___jp_3226_;
}
}
}
}
else
{
lean_object* v_a_3480_; 
lean_del_object(v___x_3464_);
v_a_3480_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3480_);
lean_dec_ref(v___x_3466_);
v___y_3382_ = v___y_3392_;
v___y_3383_ = v___y_3393_;
v___y_3384_ = v___y_3394_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v_a_3388_ = v_a_3480_;
goto v___jp_3381_;
}
}
}
else
{
lean_object* v_a_3482_; 
v_a_3482_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3482_);
lean_dec_ref(v___x_3461_);
v___y_3382_ = v___y_3392_;
v___y_3383_ = v___y_3393_;
v___y_3384_ = v___y_3394_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v_a_3388_ = v_a_3482_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3483_; 
lean_dec(v_a_3448_);
lean_dec(v_a_3399_);
v_a_3483_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3483_);
lean_dec_ref(v___x_3449_);
v___y_3382_ = v___y_3392_;
v___y_3383_ = v___y_3393_;
v___y_3384_ = v___y_3394_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v_a_3388_ = v_a_3483_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3484_; 
lean_dec(v_a_3399_);
v_a_3484_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3484_);
lean_dec_ref(v___x_3447_);
v___y_3382_ = v___y_3392_;
v___y_3383_ = v___y_3393_;
v___y_3384_ = v___y_3394_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v_a_3388_ = v_a_3484_;
goto v___jp_3381_;
}
}
}
else
{
lean_object* v_a_3485_; 
lean_dec(v_a_3399_);
v_a_3485_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3485_);
lean_dec_ref(v___x_3443_);
v___y_3382_ = v___y_3392_;
v___y_3383_ = v___y_3393_;
v___y_3384_ = v___y_3394_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v_a_3388_ = v_a_3485_;
goto v___jp_3381_;
}
}
}
}
else
{
lean_object* v_a_3488_; 
v_a_3488_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3488_);
lean_dec_ref(v___x_3398_);
v___y_3382_ = v___y_3392_;
v___y_3383_ = v___y_3393_;
v___y_3384_ = v___y_3394_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v_a_3388_ = v_a_3488_;
goto v___jp_3381_;
}
}
v___jp_3489_:
{
if (v___y_3496_ == 0)
{
v___y_3363_ = v___y_3493_;
v___y_3364_ = v___y_3495_;
v___y_3365_ = v___y_3490_;
v___y_3366_ = v___y_3491_;
v___y_3367_ = v___y_3494_;
v___y_3368_ = v___y_3492_;
goto v___jp_3362_;
}
else
{
v___y_3392_ = v___y_3490_;
v___y_3393_ = v___y_3491_;
v___y_3394_ = v___y_3492_;
v___y_3395_ = v___y_3493_;
v___y_3396_ = v___y_3494_;
v___y_3397_ = v___y_3495_;
goto v___jp_3391_;
}
}
v___jp_3497_:
{
if (v___y_3505_ == 0)
{
lean_dec_ref(v___y_3504_);
v___y_3490_ = v___y_3498_;
v___y_3491_ = v___y_3499_;
v___y_3492_ = v___y_3500_;
v___y_3493_ = v___y_3501_;
v___y_3494_ = v___y_3502_;
v___y_3495_ = v___y_3503_;
v___y_3496_ = v___x_3316_;
goto v___jp_3489_;
}
else
{
uint8_t v___x_3506_; 
v___x_3506_ = l_Lean_Expr_hasFVar(v___y_3504_);
lean_dec_ref(v___y_3504_);
if (v___x_3506_ == 0)
{
v___y_3392_ = v___y_3498_;
v___y_3393_ = v___y_3499_;
v___y_3394_ = v___y_3500_;
v___y_3395_ = v___y_3501_;
v___y_3396_ = v___y_3502_;
v___y_3397_ = v___y_3503_;
goto v___jp_3391_;
}
else
{
v___y_3490_ = v___y_3498_;
v___y_3491_ = v___y_3499_;
v___y_3492_ = v___y_3500_;
v___y_3493_ = v___y_3501_;
v___y_3494_ = v___y_3502_;
v___y_3495_ = v___y_3503_;
v___y_3496_ = v___x_3316_;
goto v___jp_3489_;
}
}
}
v___jp_3507_:
{
lean_object* v___x_3515_; 
lean_inc_ref(v___x_3361_);
v___x_3515_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3361_, v___y_3509_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; uint8_t v___x_3517_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref(v___x_3515_);
v___x_3517_ = l_Lean_Expr_hasMVar(v_a_3516_);
if (v___x_3517_ == 0)
{
v___y_3498_ = v___y_3508_;
v___y_3499_ = v___y_3509_;
v___y_3500_ = v___y_3510_;
v___y_3501_ = v___y_3511_;
v___y_3502_ = v___y_3512_;
v___y_3503_ = v___y_3513_;
v___y_3504_ = v_a_3516_;
v___y_3505_ = v___y_3514_;
goto v___jp_3497_;
}
else
{
v___y_3498_ = v___y_3508_;
v___y_3499_ = v___y_3509_;
v___y_3500_ = v___y_3510_;
v___y_3501_ = v___y_3511_;
v___y_3502_ = v___y_3512_;
v___y_3503_ = v___y_3513_;
v___y_3504_ = v_a_3516_;
v___y_3505_ = v___x_3316_;
goto v___jp_3497_;
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v___x_3361_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3518_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3515_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3515_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
v___jp_3526_:
{
if (v___y_3533_ == 0)
{
v___y_3363_ = v___y_3530_;
v___y_3364_ = v___y_3532_;
v___y_3365_ = v___y_3527_;
v___y_3366_ = v___y_3528_;
v___y_3367_ = v___y_3531_;
v___y_3368_ = v___y_3529_;
goto v___jp_3362_;
}
else
{
v___y_3508_ = v___y_3527_;
v___y_3509_ = v___y_3528_;
v___y_3510_ = v___y_3529_;
v___y_3511_ = v___y_3530_;
v___y_3512_ = v___y_3531_;
v___y_3513_ = v___y_3532_;
v___y_3514_ = v___y_3533_;
goto v___jp_3507_;
}
}
v___jp_3534_:
{
uint8_t v_useDecide_3541_; 
v_useDecide_3541_ = lean_ctor_get_uint8(v_config_3209_, sizeof(void*)*1);
if (v_useDecide_3541_ == 0)
{
v___y_3527_ = v___y_3537_;
v___y_3528_ = v___y_3538_;
v___y_3529_ = v___y_3540_;
v___y_3530_ = v_isHEq_3536_;
v___y_3531_ = v___y_3539_;
v___y_3532_ = v___y_3535_;
v___y_3533_ = v___x_3316_;
goto v___jp_3526_;
}
else
{
uint8_t v___x_3542_; 
v___x_3542_ = l_Lean_Expr_hasFVar(v___x_3361_);
if (v___x_3542_ == 0)
{
v___y_3508_ = v___y_3537_;
v___y_3509_ = v___y_3538_;
v___y_3510_ = v___y_3540_;
v___y_3511_ = v_isHEq_3536_;
v___y_3512_ = v___y_3539_;
v___y_3513_ = v___y_3535_;
v___y_3514_ = v_useDecide_3541_;
goto v___jp_3507_;
}
else
{
v___y_3527_ = v___y_3537_;
v___y_3528_ = v___y_3538_;
v___y_3529_ = v___y_3540_;
v___y_3530_ = v_isHEq_3536_;
v___y_3531_ = v___y_3539_;
v___y_3532_ = v___y_3535_;
v___y_3533_ = v___x_3316_;
goto v___jp_3526_;
}
}
}
v___jp_3543_:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_Meta_isExprDefEq(v___y_3546_, v___y_3547_, v___y_3545_, v___y_3550_, v___y_3549_, v___y_3544_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; uint8_t v___x_3553_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref(v___x_3551_);
v___x_3553_ = lean_unbox(v_a_3552_);
lean_dec(v_a_3552_);
if (v___x_3553_ == 0)
{
v___y_3535_ = v___y_3548_;
v_isHEq_3536_ = v___x_3220_;
v___y_3537_ = v___y_3545_;
v___y_3538_ = v___y_3550_;
v___y_3539_ = v___y_3549_;
v___y_3540_ = v___y_3544_;
goto v___jp_3534_;
}
else
{
lean_object* v___x_3554_; 
lean_dec_ref(v___x_3361_);
lean_dec_ref(v_config_3209_);
lean_inc(v_mvarId_3210_);
v___x_3554_ = l_Lean_MVarId_getType(v_mvarId_3210_, v___y_3545_, v___y_3550_, v___y_3549_, v___y_3544_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref(v___x_3554_);
v___x_3556_ = l_Lean_LocalDecl_toExpr(v_val_3241_);
v___x_3557_ = l_Lean_Meta_mkEqOfHEq(v___x_3556_, v___x_3220_, v___y_3545_, v___y_3550_, v___y_3549_, v___y_3544_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref(v___x_3557_);
v___x_3559_ = l_Lean_Meta_mkNoConfusion(v_a_3555_, v_a_3558_, v___y_3545_, v___y_3550_, v___y_3549_, v___y_3544_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref(v___x_3559_);
v___x_3561_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3210_, v_a_3560_, v___y_3550_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_dec_ref(v___x_3561_);
v___x_3562_ = lean_box(v___x_3220_);
v___x_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v___x_3245_);
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
v_a_3227_ = v___x_3565_;
goto v___jp_3226_;
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
v_a_3566_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3561_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3561_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3574_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3559_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3559_);
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
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v_a_3555_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3582_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3557_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3557_);
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
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
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
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
lean_dec_ref(v___x_3361_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3598_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3551_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3551_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
v___jp_3606_:
{
lean_object* v___x_3612_; 
lean_inc_ref(v___x_3361_);
v___x_3612_ = l_Lean_Meta_matchHEq_x3f(v___x_3361_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref(v___x_3612_);
if (lean_obj_tag(v_a_3613_) == 1)
{
lean_object* v_val_3614_; lean_object* v_snd_3615_; lean_object* v_snd_3616_; lean_object* v_fst_3617_; lean_object* v_fst_3618_; lean_object* v_fst_3619_; lean_object* v_snd_3620_; lean_object* v___x_3621_; 
v_val_3614_ = lean_ctor_get(v_a_3613_, 0);
lean_inc(v_val_3614_);
lean_dec_ref(v_a_3613_);
v_snd_3615_ = lean_ctor_get(v_val_3614_, 1);
lean_inc(v_snd_3615_);
v_snd_3616_ = lean_ctor_get(v_snd_3615_, 1);
lean_inc(v_snd_3616_);
v_fst_3617_ = lean_ctor_get(v_val_3614_, 0);
lean_inc(v_fst_3617_);
lean_dec(v_val_3614_);
v_fst_3618_ = lean_ctor_get(v_snd_3615_, 0);
lean_inc(v_fst_3618_);
lean_dec(v_snd_3615_);
v_fst_3619_ = lean_ctor_get(v_snd_3616_, 0);
lean_inc(v_fst_3619_);
v_snd_3620_ = lean_ctor_get(v_snd_3616_, 1);
lean_inc(v_snd_3620_);
lean_dec(v_snd_3616_);
v___x_3621_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3618_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
lean_dec_ref(v___x_3621_);
if (lean_obj_tag(v_a_3622_) == 1)
{
lean_object* v_val_3623_; lean_object* v___x_3624_; 
v_val_3623_ = lean_ctor_get(v_a_3622_, 0);
lean_inc(v_val_3623_);
lean_dec_ref(v_a_3622_);
v___x_3624_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3620_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref(v___x_3624_);
if (lean_obj_tag(v_a_3625_) == 1)
{
lean_object* v_toConstantVal_3626_; lean_object* v_val_3627_; lean_object* v_toConstantVal_3628_; lean_object* v_name_3629_; lean_object* v_name_3630_; uint8_t v___x_3631_; 
v_toConstantVal_3626_ = lean_ctor_get(v_val_3623_, 0);
lean_inc_ref(v_toConstantVal_3626_);
lean_dec(v_val_3623_);
v_val_3627_ = lean_ctor_get(v_a_3625_, 0);
lean_inc(v_val_3627_);
lean_dec_ref(v_a_3625_);
v_toConstantVal_3628_ = lean_ctor_get(v_val_3627_, 0);
lean_inc_ref(v_toConstantVal_3628_);
lean_dec(v_val_3627_);
v_name_3629_ = lean_ctor_get(v_toConstantVal_3626_, 0);
lean_inc(v_name_3629_);
lean_dec_ref(v_toConstantVal_3626_);
v_name_3630_ = lean_ctor_get(v_toConstantVal_3628_, 0);
lean_inc(v_name_3630_);
lean_dec_ref(v_toConstantVal_3628_);
v___x_3631_ = lean_name_eq(v_name_3629_, v_name_3630_);
lean_dec(v_name_3630_);
lean_dec(v_name_3629_);
if (v___x_3631_ == 0)
{
v___y_3544_ = v___y_3611_;
v___y_3545_ = v___y_3608_;
v___y_3546_ = v_fst_3617_;
v___y_3547_ = v_fst_3619_;
v___y_3548_ = v_isEq_3607_;
v___y_3549_ = v___y_3610_;
v___y_3550_ = v___y_3609_;
goto v___jp_3543_;
}
else
{
if (v___x_3316_ == 0)
{
lean_dec(v_fst_3619_);
lean_dec(v_fst_3617_);
v___y_3535_ = v_isEq_3607_;
v_isHEq_3536_ = v___x_3220_;
v___y_3537_ = v___y_3608_;
v___y_3538_ = v___y_3609_;
v___y_3539_ = v___y_3610_;
v___y_3540_ = v___y_3611_;
goto v___jp_3534_;
}
else
{
v___y_3544_ = v___y_3611_;
v___y_3545_ = v___y_3608_;
v___y_3546_ = v_fst_3617_;
v___y_3547_ = v_fst_3619_;
v___y_3548_ = v_isEq_3607_;
v___y_3549_ = v___y_3610_;
v___y_3550_ = v___y_3609_;
goto v___jp_3543_;
}
}
}
else
{
lean_dec(v_a_3625_);
lean_dec(v_val_3623_);
lean_dec(v_fst_3619_);
lean_dec(v_fst_3617_);
v___y_3535_ = v_isEq_3607_;
v_isHEq_3536_ = v___x_3220_;
v___y_3537_ = v___y_3608_;
v___y_3538_ = v___y_3609_;
v___y_3539_ = v___y_3610_;
v___y_3540_ = v___y_3611_;
goto v___jp_3534_;
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_val_3623_);
lean_dec(v_fst_3619_);
lean_dec(v_fst_3617_);
lean_dec_ref(v___x_3361_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3632_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3624_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3624_);
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
else
{
lean_dec(v_a_3622_);
lean_dec(v_snd_3620_);
lean_dec(v_fst_3619_);
lean_dec(v_fst_3617_);
v___y_3535_ = v_isEq_3607_;
v_isHEq_3536_ = v___x_3220_;
v___y_3537_ = v___y_3608_;
v___y_3538_ = v___y_3609_;
v___y_3539_ = v___y_3610_;
v___y_3540_ = v___y_3611_;
goto v___jp_3534_;
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec(v_snd_3620_);
lean_dec(v_fst_3619_);
lean_dec(v_fst_3617_);
lean_dec_ref(v___x_3361_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3640_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3621_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3621_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_dec(v_a_3613_);
v___y_3535_ = v_isEq_3607_;
v_isHEq_3536_ = v___x_3316_;
v___y_3537_ = v___y_3608_;
v___y_3538_ = v___y_3609_;
v___y_3539_ = v___y_3610_;
v___y_3540_ = v___y_3611_;
goto v___jp_3534_;
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec_ref(v___x_3361_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3648_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3612_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3612_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
v___jp_3656_:
{
lean_object* v___x_3661_; 
lean_inc_ref(v___x_3361_);
v___x_3661_ = l_Lean_Meta_matchEq_x3f(v___x_3361_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
if (lean_obj_tag(v_a_3662_) == 1)
{
lean_object* v_val_3663_; lean_object* v_snd_3664_; lean_object* v_fst_3665_; lean_object* v_snd_3666_; lean_object* v___x_3667_; 
v_val_3663_ = lean_ctor_get(v_a_3662_, 0);
lean_inc(v_val_3663_);
lean_dec_ref(v_a_3662_);
v_snd_3664_ = lean_ctor_get(v_val_3663_, 1);
lean_inc(v_snd_3664_);
lean_dec(v_val_3663_);
v_fst_3665_ = lean_ctor_get(v_snd_3664_, 0);
lean_inc(v_fst_3665_);
v_snd_3666_ = lean_ctor_get(v_snd_3664_, 1);
lean_inc(v_snd_3666_);
lean_dec(v_snd_3664_);
v___x_3667_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3665_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref(v___x_3667_);
if (lean_obj_tag(v_a_3668_) == 1)
{
lean_object* v_val_3669_; lean_object* v___x_3670_; 
v_val_3669_ = lean_ctor_get(v_a_3668_, 0);
lean_inc(v_val_3669_);
lean_dec_ref(v_a_3668_);
v___x_3670_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3666_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref(v___x_3670_);
if (lean_obj_tag(v_a_3671_) == 1)
{
lean_object* v_toConstantVal_3672_; lean_object* v_val_3673_; lean_object* v_toConstantVal_3674_; lean_object* v_name_3675_; lean_object* v_name_3676_; uint8_t v___x_3677_; 
v_toConstantVal_3672_ = lean_ctor_get(v_val_3669_, 0);
lean_inc_ref(v_toConstantVal_3672_);
lean_dec(v_val_3669_);
v_val_3673_ = lean_ctor_get(v_a_3671_, 0);
lean_inc(v_val_3673_);
lean_dec_ref(v_a_3671_);
v_toConstantVal_3674_ = lean_ctor_get(v_val_3673_, 0);
lean_inc_ref(v_toConstantVal_3674_);
lean_dec(v_val_3673_);
v_name_3675_ = lean_ctor_get(v_toConstantVal_3672_, 0);
lean_inc(v_name_3675_);
lean_dec_ref(v_toConstantVal_3672_);
v_name_3676_ = lean_ctor_get(v_toConstantVal_3674_, 0);
lean_inc(v_name_3676_);
lean_dec_ref(v_toConstantVal_3674_);
v___x_3677_ = lean_name_eq(v_name_3675_, v_name_3676_);
lean_dec(v_name_3676_);
lean_dec(v_name_3675_);
if (v___x_3677_ == 0)
{
lean_dec_ref(v___x_3361_);
lean_dec_ref(v_config_3209_);
v___y_3247_ = v___y_3658_;
v___y_3248_ = v___y_3660_;
v___y_3249_ = v___y_3659_;
v___y_3250_ = v___y_3657_;
goto v___jp_3246_;
}
else
{
if (v___x_3316_ == 0)
{
lean_del_object(v___x_3243_);
v_isEq_3607_ = v___x_3220_;
v___y_3608_ = v___y_3657_;
v___y_3609_ = v___y_3658_;
v___y_3610_ = v___y_3659_;
v___y_3611_ = v___y_3660_;
goto v___jp_3606_;
}
else
{
lean_dec_ref(v___x_3361_);
lean_dec_ref(v_config_3209_);
v___y_3247_ = v___y_3658_;
v___y_3248_ = v___y_3660_;
v___y_3249_ = v___y_3659_;
v___y_3250_ = v___y_3657_;
goto v___jp_3246_;
}
}
}
else
{
lean_dec(v_a_3671_);
lean_dec(v_val_3669_);
lean_del_object(v___x_3243_);
v_isEq_3607_ = v___x_3220_;
v___y_3608_ = v___y_3657_;
v___y_3609_ = v___y_3658_;
v___y_3610_ = v___y_3659_;
v___y_3611_ = v___y_3660_;
goto v___jp_3606_;
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v_val_3669_);
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3678_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3670_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3670_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_dec(v_a_3668_);
lean_dec(v_snd_3666_);
lean_del_object(v___x_3243_);
v_isEq_3607_ = v___x_3220_;
v___y_3608_ = v___y_3657_;
v___y_3609_ = v___y_3658_;
v___y_3610_ = v___y_3659_;
v___y_3611_ = v___y_3660_;
goto v___jp_3606_;
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v_snd_3666_);
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3686_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3667_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3667_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_dec(v_a_3662_);
lean_del_object(v___x_3243_);
v_isEq_3607_ = v___x_3316_;
v___y_3608_ = v___y_3657_;
v___y_3609_ = v___y_3658_;
v___y_3610_ = v___y_3659_;
v___y_3611_ = v___y_3660_;
goto v___jp_3606_;
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3694_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3661_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3661_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
v___jp_3702_:
{
lean_object* v___x_3707_; 
lean_inc_ref(v___x_3361_);
v___x_3707_ = l_refutableHasNotBit_x3f(v___x_3361_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref(v___x_3707_);
if (lean_obj_tag(v_a_3708_) == 1)
{
lean_object* v_val_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec_ref(v_config_3209_);
v_val_3709_ = lean_ctor_get(v_a_3708_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_a_3708_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3711_ = v_a_3708_;
v_isShared_3712_ = v_isSharedCheck_3749_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_val_3709_);
lean_dec(v_a_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3749_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; 
lean_inc(v_mvarId_3210_);
v___x_3713_ = l_Lean_MVarId_getType(v_mvarId_3210_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref(v___x_3713_);
v___x_3715_ = l_Lean_LocalDecl_toExpr(v_val_3241_);
v___x_3716_ = l_Lean_Meta_mkAbsurd(v_a_3714_, v_val_3709_, v___x_3715_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3718_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref(v___x_3716_);
v___x_3718_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3210_, v_a_3717_, v___y_3704_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_dec_ref(v___x_3718_);
v___x_3719_ = lean_box(v___x_3220_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 0, v___x_3719_);
v___x_3721_ = v___x_3711_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v___x_3245_);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
v_a_3227_ = v___x_3723_;
goto v___jp_3226_;
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_del_object(v___x_3711_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
v_a_3725_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3718_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3718_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_del_object(v___x_3711_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3733_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3716_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3716_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_del_object(v___x_3711_);
lean_dec(v_val_3709_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3741_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3713_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3713_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
else
{
lean_object* v___x_3750_; 
lean_dec(v_a_3708_);
lean_inc_ref(v___x_3361_);
v___x_3750_ = l_Lean_Meta_matchNe_x3f(v___x_3361_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref(v___x_3750_);
if (lean_obj_tag(v_a_3751_) == 1)
{
lean_object* v_val_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3822_; 
v_val_3752_ = lean_ctor_get(v_a_3751_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_a_3751_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3754_ = v_a_3751_;
v_isShared_3755_ = v_isSharedCheck_3822_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_val_3752_);
lean_dec(v_a_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3822_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v_snd_3756_; lean_object* v_fst_3757_; lean_object* v_snd_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3821_; 
v_snd_3756_ = lean_ctor_get(v_val_3752_, 1);
lean_inc(v_snd_3756_);
lean_dec(v_val_3752_);
v_fst_3757_ = lean_ctor_get(v_snd_3756_, 0);
v_snd_3758_ = lean_ctor_get(v_snd_3756_, 1);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_snd_3756_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3760_ = v_snd_3756_;
v_isShared_3761_ = v_isSharedCheck_3821_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_snd_3758_);
lean_inc(v_fst_3757_);
lean_dec(v_snd_3756_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3821_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3762_; 
lean_inc(v_fst_3757_);
v___x_3762_ = l_Lean_Meta_isExprDefEq(v_fst_3757_, v_snd_3758_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; uint8_t v___x_3764_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref(v___x_3762_);
v___x_3764_ = lean_unbox(v_a_3763_);
lean_dec(v_a_3763_);
if (v___x_3764_ == 0)
{
lean_del_object(v___x_3760_);
lean_dec(v_fst_3757_);
lean_del_object(v___x_3754_);
v___y_3657_ = v___y_3703_;
v___y_3658_ = v___y_3704_;
v___y_3659_ = v___y_3705_;
v___y_3660_ = v___y_3706_;
goto v___jp_3656_;
}
else
{
lean_object* v___x_3765_; 
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec_ref(v_config_3209_);
lean_inc(v_mvarId_3210_);
v___x_3765_ = l_Lean_MVarId_getType(v_mvarId_3210_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3767_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = l_Lean_Meta_mkEqRefl(v_fst_3757_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = l_Lean_LocalDecl_toExpr(v_val_3241_);
v___x_3770_ = l_Lean_Meta_mkAbsurd(v_a_3766_, v_a_3768_, v___x_3769_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3772_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3210_, v_a_3771_, v___y_3704_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3775_; 
lean_dec_ref(v___x_3772_);
v___x_3773_ = lean_box(v___x_3220_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_3773_);
v___x_3775_ = v___x_3754_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 1, v___x_3245_);
lean_ctor_set(v___x_3760_, 0, v___x_3775_);
v___x_3777_ = v___x_3760_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v___x_3245_);
v___x_3777_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
v_a_3227_ = v___x_3778_;
goto v___jp_3226_;
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_del_object(v___x_3760_);
lean_del_object(v___x_3754_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
v_a_3781_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3772_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3772_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_del_object(v___x_3760_);
lean_del_object(v___x_3754_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3789_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3770_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3770_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_a_3766_);
lean_del_object(v___x_3760_);
lean_del_object(v___x_3754_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3797_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3767_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3767_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_del_object(v___x_3760_);
lean_dec(v_fst_3757_);
lean_del_object(v___x_3754_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3805_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3765_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3765_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_del_object(v___x_3760_);
lean_dec(v_fst_3757_);
lean_del_object(v___x_3754_);
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3813_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3762_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3762_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3751_);
v___y_3657_ = v___y_3703_;
v___y_3658_ = v___y_3704_;
v___y_3659_ = v___y_3705_;
v___y_3660_ = v___y_3706_;
goto v___jp_3656_;
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3823_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3750_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3750_);
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
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref(v___x_3361_);
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3831_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3707_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3707_);
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
}
else
{
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
v_a_3235_ = v___x_3287_;
goto v___jp_3234_;
}
v___jp_3246_:
{
lean_object* v___x_3251_; 
lean_inc(v_mvarId_3210_);
v___x_3251_ = l_Lean_MVarId_getType(v_mvarId_3210_, v___y_3250_, v___y_3247_, v___y_3249_, v___y_3248_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref(v___x_3251_);
v___x_3253_ = l_Lean_LocalDecl_toExpr(v_val_3241_);
v___x_3254_ = l_Lean_Meta_mkNoConfusion(v_a_3252_, v___x_3253_, v___y_3250_, v___y_3247_, v___y_3249_, v___y_3248_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3256_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref(v___x_3254_);
v___x_3256_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3210_, v_a_3255_, v___y_3247_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v___x_3257_; lean_object* v___x_3259_; 
lean_dec_ref(v___x_3256_);
v___x_3257_ = lean_box(v___x_3220_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3257_);
v___x_3259_ = v___x_3243_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v___x_3245_);
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
v_a_3227_ = v___x_3261_;
goto v___jp_3226_;
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_del_object(v___x_3243_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
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
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_del_object(v___x_3243_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3271_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3254_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3254_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_del_object(v___x_3243_);
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
v_a_3279_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3251_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3251_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
v___jp_3288_:
{
lean_object* v_searchFuel_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v_searchFuel_3293_ = lean_ctor_get(v_config_3209_, 0);
v___x_3294_ = l_Lean_LocalDecl_fvarId(v_val_3241_);
lean_dec(v_val_3241_);
lean_inc(v_searchFuel_3293_);
lean_inc(v_mvarId_3210_);
v___x_3295_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3210_, v___x_3294_, v_searchFuel_3293_, v___y_3289_, v___y_3291_, v___y_3290_, v___y_3292_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; uint8_t v___x_3297_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref(v___x_3295_);
v___x_3297_ = lean_unbox(v_a_3296_);
lean_dec(v_a_3296_);
if (v___x_3297_ == 0)
{
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
v_a_3235_ = v___x_3287_;
goto v___jp_3234_;
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v___x_3298_ = lean_box(v___x_3220_);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v___x_3245_);
v___x_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
v_a_3227_ = v___x_3301_;
goto v___jp_3226_;
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3302_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3295_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3295_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
v___jp_3310_:
{
if (v___y_3315_ == 0)
{
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
v_a_3235_ = v___x_3287_;
goto v___jp_3234_;
}
else
{
v___y_3289_ = v___y_3311_;
v___y_3290_ = v___y_3312_;
v___y_3291_ = v___y_3313_;
v___y_3292_ = v___y_3314_;
goto v___jp_3288_;
}
}
v___jp_3317_:
{
if (v___y_3321_ == 0)
{
v___y_3289_ = v___y_3318_;
v___y_3290_ = v___y_3319_;
v___y_3291_ = v___y_3320_;
v___y_3292_ = v___y_3322_;
goto v___jp_3288_;
}
else
{
v___y_3311_ = v___y_3318_;
v___y_3312_ = v___y_3319_;
v___y_3313_ = v___y_3320_;
v___y_3314_ = v___y_3322_;
v___y_3315_ = v___x_3316_;
goto v___jp_3310_;
}
}
v___jp_3323_:
{
if (v___y_3329_ == 0)
{
v___y_3311_ = v___y_3324_;
v___y_3312_ = v___y_3325_;
v___y_3313_ = v___y_3326_;
v___y_3314_ = v___y_3328_;
v___y_3315_ = v___x_3316_;
goto v___jp_3310_;
}
else
{
v___y_3318_ = v___y_3324_;
v___y_3319_ = v___y_3325_;
v___y_3320_ = v___y_3326_;
v___y_3321_ = v___y_3327_;
v___y_3322_ = v___y_3328_;
goto v___jp_3317_;
}
}
v___jp_3330_:
{
uint8_t v_emptyType_3337_; 
v_emptyType_3337_ = lean_ctor_get_uint8(v_config_3209_, sizeof(void*)*1 + 1);
if (v_emptyType_3337_ == 0)
{
v___y_3324_ = v___y_3333_;
v___y_3325_ = v___y_3335_;
v___y_3326_ = v___y_3334_;
v___y_3327_ = v___y_3331_;
v___y_3328_ = v___y_3336_;
v___y_3329_ = v___x_3316_;
goto v___jp_3323_;
}
else
{
if (v___y_3332_ == 0)
{
v___y_3318_ = v___y_3333_;
v___y_3319_ = v___y_3335_;
v___y_3320_ = v___y_3334_;
v___y_3321_ = v___y_3331_;
v___y_3322_ = v___y_3336_;
goto v___jp_3317_;
}
else
{
v___y_3324_ = v___y_3333_;
v___y_3325_ = v___y_3335_;
v___y_3326_ = v___y_3334_;
v___y_3327_ = v___y_3331_;
v___y_3328_ = v___y_3336_;
v___y_3329_ = v___x_3316_;
goto v___jp_3323_;
}
}
}
v___jp_3338_:
{
if (v___y_3345_ == 0)
{
v___y_3331_ = v___y_3340_;
v___y_3332_ = v___y_3343_;
v___y_3333_ = v___y_3339_;
v___y_3334_ = v___y_3341_;
v___y_3335_ = v___y_3342_;
v___y_3336_ = v___y_3344_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3346_; 
lean_inc(v_val_3241_);
lean_inc(v_mvarId_3210_);
v___x_3346_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3210_, v_val_3241_, v___y_3339_, v___y_3341_, v___y_3342_, v___y_3344_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; uint8_t v___x_3348_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = lean_unbox(v_a_3347_);
lean_dec(v_a_3347_);
if (v___x_3348_ == 0)
{
v___y_3331_ = v___y_3340_;
v___y_3332_ = v___y_3343_;
v___y_3333_ = v___y_3339_;
v___y_3334_ = v___y_3341_;
v___y_3335_ = v___y_3342_;
v___y_3336_ = v___y_3344_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_dec(v_val_3241_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v___x_3349_ = lean_box(v___x_3220_);
v___x_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v___x_3245_);
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
v_a_3227_ = v___x_3352_;
goto v___jp_3226_;
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec(v_val_3241_);
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
lean_dec(v_mvarId_3210_);
lean_dec_ref(v_config_3209_);
v_a_3353_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3346_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3346_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
}
}
v___jp_3226_:
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v_a_3227_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3228_);
v___x_3230_ = v___x_3224_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_snd_3222_);
v___x_3230_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
}
v___jp_3234_:
{
lean_object* v___x_3236_; size_t v___x_3237_; size_t v___x_3238_; 
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3233_);
lean_ctor_set(v___x_3236_, 1, v_a_3235_);
v___x_3237_ = ((size_t)1ULL);
v___x_3238_ = lean_usize_add(v_i_3213_, v___x_3237_);
v_i_3213_ = v___x_3238_;
v_b_3214_ = v___x_3236_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3912_, lean_object* v_mvarId_3913_, lean_object* v_as_3914_, lean_object* v_sz_3915_, lean_object* v_i_3916_, lean_object* v_b_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
size_t v_sz_boxed_3923_; size_t v_i_boxed_3924_; lean_object* v_res_3925_; 
v_sz_boxed_3923_ = lean_unbox_usize(v_sz_3915_);
lean_dec(v_sz_3915_);
v_i_boxed_3924_ = lean_unbox_usize(v_i_3916_);
lean_dec(v_i_3916_);
v_res_3925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3912_, v_mvarId_3913_, v_as_3914_, v_sz_boxed_3923_, v_i_boxed_3924_, v_b_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec_ref(v_as_3914_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3926_, lean_object* v_mvarId_3927_, lean_object* v_as_3928_, size_t v_sz_3929_, size_t v_i_3930_, lean_object* v_b_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
uint8_t v___x_3937_; 
v___x_3937_ = lean_usize_dec_lt(v_i_3930_, v_sz_3929_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; 
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v___x_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3938_, 0, v_b_3931_);
return v___x_3938_;
}
else
{
lean_object* v_snd_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_4627_; 
v_snd_3939_ = lean_ctor_get(v_b_3931_, 1);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_b_3931_);
if (v_isSharedCheck_4627_ == 0)
{
lean_object* v_unused_4628_; 
v_unused_4628_ = lean_ctor_get(v_b_3931_, 0);
lean_dec(v_unused_4628_);
v___x_3941_ = v_b_3931_;
v_isShared_3942_ = v_isSharedCheck_4627_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_snd_3939_);
lean_dec(v_b_3931_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_4627_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v_a_3944_; lean_object* v___x_3950_; lean_object* v_a_3952_; lean_object* v_a_3957_; 
v___x_3950_ = lean_box(0);
v_a_3957_ = lean_array_uget(v_as_3928_, v_i_3930_);
if (lean_obj_tag(v_a_3957_) == 0)
{
lean_del_object(v___x_3941_);
v_a_3952_ = v_snd_3939_;
goto v___jp_3951_;
}
else
{
lean_object* v_val_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_4626_; 
v_val_3958_ = lean_ctor_get(v_a_3957_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_a_3957_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_3960_ = v_a_3957_;
v_isShared_3961_ = v_isSharedCheck_4626_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_val_3958_);
lean_dec(v_a_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_4626_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3962_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___x_4004_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; uint8_t v___y_4032_; uint8_t v___x_4033_; uint8_t v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; uint8_t v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; uint8_t v___y_4046_; uint8_t v___y_4048_; uint8_t v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4056_; uint8_t v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; uint8_t v___y_4061_; uint8_t v___y_4062_; 
v___x_3962_ = lean_box(0);
v___x_4004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_4033_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3958_);
if (v___x_4033_ == 0)
{
lean_object* v___x_4078_; uint8_t v___y_4080_; uint8_t v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; uint8_t v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; uint8_t v___y_4095_; uint8_t v___y_4096_; uint8_t v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; uint8_t v___y_4104_; lean_object* v_a_4105_; uint8_t v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; uint8_t v___y_4114_; uint8_t v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; uint8_t v___y_4212_; uint8_t v___y_4213_; uint8_t v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; uint8_t v___y_4220_; lean_object* v___y_4221_; uint8_t v___y_4222_; uint8_t v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; uint8_t v___y_4230_; uint8_t v___y_4231_; uint8_t v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; uint8_t v___y_4249_; uint8_t v___y_4250_; uint8_t v___y_4252_; uint8_t v_isHEq_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; uint8_t v___y_4266_; lean_object* v___y_4267_; uint8_t v_isEq_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___x_4556_; 
v___x_4078_ = l_Lean_LocalDecl_type(v_val_3958_);
lean_inc_ref(v___x_4078_);
v___x_4556_ = l_Lean_Meta_matchNot_x3f(v___x_4078_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
lean_dec_ref(v___x_4556_);
if (lean_obj_tag(v_a_4557_) == 1)
{
lean_object* v_val_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4617_; 
v_val_4558_ = lean_ctor_get(v_a_4557_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v_a_4557_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4560_ = v_a_4557_;
v_isShared_4561_ = v_isSharedCheck_4617_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_val_4558_);
lean_dec(v_a_4557_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4617_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4562_; 
v___x_4562_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4558_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
lean_dec_ref(v___x_4562_);
if (lean_obj_tag(v_a_4563_) == 1)
{
lean_object* v_val_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4608_; 
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec_ref(v_config_3926_);
v_val_4564_ = lean_ctor_get(v_a_4563_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v_a_4563_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4566_ = v_a_4563_;
v_isShared_4567_ = v_isSharedCheck_4608_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_val_4564_);
lean_dec(v_a_4563_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4608_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4568_; 
lean_inc(v_mvarId_3927_);
v___x_4568_ = l_Lean_MVarId_getType(v_mvarId_3927_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v_a_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v_a_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_a_4569_);
lean_dec_ref(v___x_4568_);
v___x_4570_ = l_Lean_LocalDecl_toExpr(v_val_3958_);
v___x_4571_ = l_Lean_mkFVar(v_val_4564_);
v___x_4572_ = l_Lean_Expr_app___override(v___x_4570_, v___x_4571_);
v___x_4573_ = l_Lean_Meta_mkFalseElim(v_a_4569_, v___x_4572_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4575_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
lean_inc(v_a_4574_);
lean_dec_ref(v___x_4573_);
v___x_4575_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3927_, v_a_4574_, v___y_3933_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v___x_4576_; lean_object* v___x_4578_; 
lean_dec_ref(v___x_4575_);
v___x_4576_ = lean_box(v___x_3937_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4576_);
v___x_4578_ = v___x_4566_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4576_);
v___x_4578_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4579_; lean_object* v___x_4581_; 
v___x_4579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
lean_ctor_set(v___x_4579_, 1, v___x_3962_);
if (v_isShared_4561_ == 0)
{
lean_ctor_set_tag(v___x_4560_, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4579_);
v___x_4581_ = v___x_4560_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
v_a_3944_ = v___x_4581_;
goto v___jp_3943_;
}
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_del_object(v___x_4566_);
lean_del_object(v___x_4560_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
v_a_4584_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4575_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4575_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
lean_del_object(v___x_4566_);
lean_del_object(v___x_4560_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4592_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___x_4573_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4573_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_del_object(v___x_4566_);
lean_dec(v_val_4564_);
lean_del_object(v___x_4560_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4600_ = lean_ctor_get(v___x_4568_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4568_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4568_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
}
else
{
lean_dec(v_a_4563_);
lean_del_object(v___x_4560_);
v___y_4420_ = v___y_3932_;
v___y_4421_ = v___y_3933_;
v___y_4422_ = v___y_3934_;
v___y_4423_ = v___y_3935_;
goto v___jp_4419_;
}
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4616_; 
lean_del_object(v___x_4560_);
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4609_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4611_ = v___x_4562_;
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4562_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4614_; 
if (v_isShared_4612_ == 0)
{
v___x_4614_ = v___x_4611_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_a_4609_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
}
}
else
{
lean_dec(v_a_4557_);
v___y_4420_ = v___y_3932_;
v___y_4421_ = v___y_3933_;
v___y_4422_ = v___y_3934_;
v___y_4423_ = v___y_3935_;
goto v___jp_4419_;
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4618_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4556_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4556_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
v___jp_4079_:
{
uint8_t v_genDiseq_4086_; 
v_genDiseq_4086_ = lean_ctor_get_uint8(v_config_3926_, sizeof(void*)*1 + 2);
if (v_genDiseq_4086_ == 0)
{
lean_dec_ref(v___x_4078_);
v___y_4056_ = v___y_4083_;
v___y_4057_ = v___y_4080_;
v___y_4058_ = v___y_4085_;
v___y_4059_ = v___y_4082_;
v___y_4060_ = v___y_4084_;
v___y_4061_ = v___y_4081_;
v___y_4062_ = v___x_4033_;
goto v___jp_4055_;
}
else
{
uint8_t v___x_4087_; 
v___x_4087_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4078_);
v___y_4056_ = v___y_4083_;
v___y_4057_ = v___y_4080_;
v___y_4058_ = v___y_4085_;
v___y_4059_ = v___y_4082_;
v___y_4060_ = v___y_4084_;
v___y_4061_ = v___y_4081_;
v___y_4062_ = v___x_4087_;
goto v___jp_4055_;
}
}
v___jp_4088_:
{
if (v___y_4096_ == 0)
{
lean_dec_ref(v___y_4094_);
v___y_4080_ = v___y_4089_;
v___y_4081_ = v___y_4095_;
v___y_4082_ = v___y_4092_;
v___y_4083_ = v___y_4093_;
v___y_4084_ = v___y_4090_;
v___y_4085_ = v___y_4091_;
goto v___jp_4079_;
}
else
{
lean_object* v___x_4097_; 
lean_dec_ref(v___x_4078_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___y_4094_);
return v___x_4097_;
}
}
v___jp_4098_:
{
uint8_t v___x_4106_; 
v___x_4106_ = l_Lean_Exception_isInterrupt(v_a_4105_);
if (v___x_4106_ == 0)
{
uint8_t v___x_4107_; 
lean_inc_ref(v_a_4105_);
v___x_4107_ = l_Lean_Exception_isRuntime(v_a_4105_);
v___y_4089_ = v___y_4099_;
v___y_4090_ = v___y_4100_;
v___y_4091_ = v___y_4101_;
v___y_4092_ = v___y_4102_;
v___y_4093_ = v___y_4103_;
v___y_4094_ = v_a_4105_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___x_4107_;
goto v___jp_4088_;
}
else
{
v___y_4089_ = v___y_4099_;
v___y_4090_ = v___y_4100_;
v___y_4091_ = v___y_4101_;
v___y_4092_ = v___y_4102_;
v___y_4093_ = v___y_4103_;
v___y_4094_ = v_a_4105_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___x_4106_;
goto v___jp_4088_;
}
}
v___jp_4108_:
{
lean_object* v___x_4115_; 
lean_inc_ref(v___x_4078_);
v___x_4115_ = l_Lean_Meta_mkDecide(v___x_4078_, v___y_4112_, v___y_4113_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4117_; uint8_t v_foApprox_4118_; uint8_t v_ctxApprox_4119_; uint8_t v_quasiPatternApprox_4120_; uint8_t v_constApprox_4121_; uint8_t v_isDefEqStuckEx_4122_; uint8_t v_unificationHints_4123_; uint8_t v_proofIrrelevance_4124_; uint8_t v_assignSyntheticOpaque_4125_; uint8_t v_offsetCnstrs_4126_; uint8_t v_etaStruct_4127_; uint8_t v_univApprox_4128_; uint8_t v_iota_4129_; uint8_t v_beta_4130_; uint8_t v_proj_4131_; uint8_t v_zeta_4132_; uint8_t v_zetaDelta_4133_; uint8_t v_zetaUnused_4134_; uint8_t v_zetaHave_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4204_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_a_4116_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = l_Lean_Meta_Context_config(v___y_4112_);
v_foApprox_4118_ = lean_ctor_get_uint8(v___x_4117_, 0);
v_ctxApprox_4119_ = lean_ctor_get_uint8(v___x_4117_, 1);
v_quasiPatternApprox_4120_ = lean_ctor_get_uint8(v___x_4117_, 2);
v_constApprox_4121_ = lean_ctor_get_uint8(v___x_4117_, 3);
v_isDefEqStuckEx_4122_ = lean_ctor_get_uint8(v___x_4117_, 4);
v_unificationHints_4123_ = lean_ctor_get_uint8(v___x_4117_, 5);
v_proofIrrelevance_4124_ = lean_ctor_get_uint8(v___x_4117_, 6);
v_assignSyntheticOpaque_4125_ = lean_ctor_get_uint8(v___x_4117_, 7);
v_offsetCnstrs_4126_ = lean_ctor_get_uint8(v___x_4117_, 8);
v_etaStruct_4127_ = lean_ctor_get_uint8(v___x_4117_, 10);
v_univApprox_4128_ = lean_ctor_get_uint8(v___x_4117_, 11);
v_iota_4129_ = lean_ctor_get_uint8(v___x_4117_, 12);
v_beta_4130_ = lean_ctor_get_uint8(v___x_4117_, 13);
v_proj_4131_ = lean_ctor_get_uint8(v___x_4117_, 14);
v_zeta_4132_ = lean_ctor_get_uint8(v___x_4117_, 15);
v_zetaDelta_4133_ = lean_ctor_get_uint8(v___x_4117_, 16);
v_zetaUnused_4134_ = lean_ctor_get_uint8(v___x_4117_, 17);
v_zetaHave_4135_ = lean_ctor_get_uint8(v___x_4117_, 18);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4137_ = v___x_4117_;
v_isShared_4138_ = v_isSharedCheck_4204_;
goto v_resetjp_4136_;
}
else
{
lean_dec(v___x_4117_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4204_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
uint8_t v_trackZetaDelta_4139_; lean_object* v_zetaDeltaSet_4140_; lean_object* v_lctx_4141_; lean_object* v_localInstances_4142_; lean_object* v_defEqCtx_x3f_4143_; lean_object* v_synthPendingDepth_4144_; lean_object* v_canUnfold_x3f_4145_; uint8_t v_univApprox_4146_; uint8_t v_inTypeClassResolution_4147_; uint8_t v_cacheInferType_4148_; uint8_t v___x_4149_; lean_object* v_config_4151_; 
v_trackZetaDelta_4139_ = lean_ctor_get_uint8(v___y_4112_, sizeof(void*)*7);
v_zetaDeltaSet_4140_ = lean_ctor_get(v___y_4112_, 1);
v_lctx_4141_ = lean_ctor_get(v___y_4112_, 2);
v_localInstances_4142_ = lean_ctor_get(v___y_4112_, 3);
v_defEqCtx_x3f_4143_ = lean_ctor_get(v___y_4112_, 4);
v_synthPendingDepth_4144_ = lean_ctor_get(v___y_4112_, 5);
v_canUnfold_x3f_4145_ = lean_ctor_get(v___y_4112_, 6);
v_univApprox_4146_ = lean_ctor_get_uint8(v___y_4112_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4147_ = lean_ctor_get_uint8(v___y_4112_, sizeof(void*)*7 + 2);
v_cacheInferType_4148_ = lean_ctor_get_uint8(v___y_4112_, sizeof(void*)*7 + 3);
v___x_4149_ = 1;
if (v_isShared_4138_ == 0)
{
v_config_4151_ = v___x_4137_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 0, v_foApprox_4118_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 1, v_ctxApprox_4119_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 2, v_quasiPatternApprox_4120_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 3, v_constApprox_4121_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 4, v_isDefEqStuckEx_4122_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 5, v_unificationHints_4123_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 6, v_proofIrrelevance_4124_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 7, v_assignSyntheticOpaque_4125_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 8, v_offsetCnstrs_4126_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 10, v_etaStruct_4127_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 11, v_univApprox_4128_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 12, v_iota_4129_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 13, v_beta_4130_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 14, v_proj_4131_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 15, v_zeta_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 16, v_zetaDelta_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 17, v_zetaUnused_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 18, v_zetaHave_4135_);
v_config_4151_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
uint64_t v___x_4152_; uint64_t v___x_4153_; uint64_t v___x_4154_; uint64_t v___x_4155_; uint64_t v___x_4156_; uint64_t v_key_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_ctor_set_uint8(v_config_4151_, 9, v___x_4149_);
v___x_4152_ = l_Lean_Meta_Context_configKey(v___y_4112_);
v___x_4153_ = 2ULL;
v___x_4154_ = lean_uint64_shift_right(v___x_4152_, v___x_4153_);
v___x_4155_ = lean_uint64_shift_left(v___x_4154_, v___x_4153_);
v___x_4156_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_4157_ = lean_uint64_lor(v___x_4155_, v___x_4156_);
v___x_4158_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4158_, 0, v_config_4151_);
lean_ctor_set_uint64(v___x_4158_, sizeof(void*)*1, v_key_4157_);
lean_inc(v_canUnfold_x3f_4145_);
lean_inc(v_synthPendingDepth_4144_);
lean_inc(v_defEqCtx_x3f_4143_);
lean_inc_ref(v_localInstances_4142_);
lean_inc_ref(v_lctx_4141_);
lean_inc(v_zetaDeltaSet_4140_);
v___x_4159_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
lean_ctor_set(v___x_4159_, 1, v_zetaDeltaSet_4140_);
lean_ctor_set(v___x_4159_, 2, v_lctx_4141_);
lean_ctor_set(v___x_4159_, 3, v_localInstances_4142_);
lean_ctor_set(v___x_4159_, 4, v_defEqCtx_x3f_4143_);
lean_ctor_set(v___x_4159_, 5, v_synthPendingDepth_4144_);
lean_ctor_set(v___x_4159_, 6, v_canUnfold_x3f_4145_);
lean_ctor_set_uint8(v___x_4159_, sizeof(void*)*7, v_trackZetaDelta_4139_);
lean_ctor_set_uint8(v___x_4159_, sizeof(void*)*7 + 1, v_univApprox_4146_);
lean_ctor_set_uint8(v___x_4159_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4147_);
lean_ctor_set_uint8(v___x_4159_, sizeof(void*)*7 + 3, v_cacheInferType_4148_);
lean_inc(v___y_4111_);
lean_inc_ref(v___y_4110_);
lean_inc(v___y_4113_);
lean_inc(v_a_4116_);
v___x_4160_ = lean_whnf(v_a_4116_, v___x_4159_, v___y_4113_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref(v___x_4160_);
v___x_4162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_4163_ = l_Lean_Expr_isConstOf(v_a_4161_, v___x_4162_);
lean_dec(v_a_4161_);
if (v___x_4163_ == 0)
{
lean_dec(v_a_4116_);
v___y_4080_ = v___y_4109_;
v___y_4081_ = v___y_4114_;
v___y_4082_ = v___y_4112_;
v___y_4083_ = v___y_4113_;
v___y_4084_ = v___y_4110_;
v___y_4085_ = v___y_4111_;
goto v___jp_4079_;
}
else
{
lean_object* v___x_4164_; 
lean_inc(v_a_4116_);
v___x_4164_ = l_Lean_Meta_mkEqRefl(v_a_4116_, v___y_4112_, v___y_4113_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref(v___x_4164_);
lean_inc(v_mvarId_3927_);
v___x_4166_ = l_Lean_MVarId_getType(v_mvarId_3927_, v___y_4112_, v___y_4113_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v_nargs_4168_; lean_object* v___x_4169_; lean_object* v_dummy_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref(v___x_4166_);
v_nargs_4168_ = l_Lean_Expr_getAppNumArgs(v_a_4116_);
v___x_4169_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_4170_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_4168_);
v___x_4171_ = lean_mk_array(v_nargs_4168_, v_dummy_4170_);
v___x_4172_ = lean_unsigned_to_nat(1u);
v___x_4173_ = lean_nat_sub(v_nargs_4168_, v___x_4172_);
lean_dec(v_nargs_4168_);
v___x_4174_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4116_, v___x_4171_, v___x_4173_);
v___x_4175_ = lean_array_push(v___x_4174_, v_a_4165_);
v___x_4176_ = l_Lean_mkAppN(v___x_4169_, v___x_4175_);
lean_dec_ref(v___x_4175_);
lean_inc(v_val_3958_);
v___x_4177_ = l_Lean_LocalDecl_toExpr(v_val_3958_);
v___x_4178_ = l_Lean_Meta_mkAbsurd(v_a_4167_, v___x_4177_, v___x_4176_, v___y_4112_, v___y_4113_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4198_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4181_ = v___x_4178_;
v_isShared_4182_ = v_isSharedCheck_4198_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4178_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4198_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4183_; 
lean_inc(v_mvarId_3927_);
v___x_4183_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3927_, v_a_4179_, v___y_4113_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4195_; 
lean_dec_ref(v___x_4078_);
lean_dec(v_val_3958_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4195_ == 0)
{
lean_object* v_unused_4196_; 
v_unused_4196_ = lean_ctor_get(v___x_4183_, 0);
lean_dec(v_unused_4196_);
v___x_4185_ = v___x_4183_;
v_isShared_4186_ = v_isSharedCheck_4195_;
goto v_resetjp_4184_;
}
else
{
lean_dec(v___x_4183_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4195_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4189_; 
v___x_4187_ = lean_box(v___x_3937_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set_tag(v___x_4185_, 1);
lean_ctor_set(v___x_4185_, 0, v___x_4187_);
v___x_4189_ = v___x_4185_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4190_; lean_object* v___x_4192_; 
v___x_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set(v___x_4190_, 1, v___x_3962_);
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 0, v___x_4190_);
v___x_4192_ = v___x_4181_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
v_a_3944_ = v___x_4192_;
goto v___jp_3943_;
}
}
}
}
else
{
lean_object* v_a_4197_; 
lean_del_object(v___x_4181_);
v_a_4197_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4197_);
lean_dec_ref(v___x_4183_);
v___y_4099_ = v___y_4109_;
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v_a_4105_ = v_a_4197_;
goto v___jp_4098_;
}
}
}
else
{
lean_object* v_a_4199_; 
v_a_4199_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4199_);
lean_dec_ref(v___x_4178_);
v___y_4099_ = v___y_4109_;
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v_a_4105_ = v_a_4199_;
goto v___jp_4098_;
}
}
else
{
lean_object* v_a_4200_; 
lean_dec(v_a_4165_);
lean_dec(v_a_4116_);
v_a_4200_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4200_);
lean_dec_ref(v___x_4166_);
v___y_4099_ = v___y_4109_;
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v_a_4105_ = v_a_4200_;
goto v___jp_4098_;
}
}
else
{
lean_object* v_a_4201_; 
lean_dec(v_a_4116_);
v_a_4201_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4201_);
lean_dec_ref(v___x_4164_);
v___y_4099_ = v___y_4109_;
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v_a_4105_ = v_a_4201_;
goto v___jp_4098_;
}
}
}
else
{
lean_object* v_a_4202_; 
lean_dec(v_a_4116_);
v_a_4202_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4202_);
lean_dec_ref(v___x_4160_);
v___y_4099_ = v___y_4109_;
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v_a_4105_ = v_a_4202_;
goto v___jp_4098_;
}
}
}
}
else
{
lean_object* v_a_4205_; 
v_a_4205_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_a_4205_);
lean_dec_ref(v___x_4115_);
v___y_4099_ = v___y_4109_;
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v_a_4105_ = v_a_4205_;
goto v___jp_4098_;
}
}
v___jp_4206_:
{
if (v___y_4213_ == 0)
{
v___y_4080_ = v___y_4207_;
v___y_4081_ = v___y_4212_;
v___y_4082_ = v___y_4210_;
v___y_4083_ = v___y_4211_;
v___y_4084_ = v___y_4208_;
v___y_4085_ = v___y_4209_;
goto v___jp_4079_;
}
else
{
v___y_4109_ = v___y_4207_;
v___y_4110_ = v___y_4208_;
v___y_4111_ = v___y_4209_;
v___y_4112_ = v___y_4210_;
v___y_4113_ = v___y_4211_;
v___y_4114_ = v___y_4212_;
goto v___jp_4108_;
}
}
v___jp_4214_:
{
if (v___y_4222_ == 0)
{
lean_dec_ref(v___y_4221_);
v___y_4207_ = v___y_4215_;
v___y_4208_ = v___y_4216_;
v___y_4209_ = v___y_4217_;
v___y_4210_ = v___y_4218_;
v___y_4211_ = v___y_4219_;
v___y_4212_ = v___y_4220_;
v___y_4213_ = v___x_4033_;
goto v___jp_4206_;
}
else
{
uint8_t v___x_4223_; 
v___x_4223_ = l_Lean_Expr_hasFVar(v___y_4221_);
lean_dec_ref(v___y_4221_);
if (v___x_4223_ == 0)
{
v___y_4109_ = v___y_4215_;
v___y_4110_ = v___y_4216_;
v___y_4111_ = v___y_4217_;
v___y_4112_ = v___y_4218_;
v___y_4113_ = v___y_4219_;
v___y_4114_ = v___y_4220_;
goto v___jp_4108_;
}
else
{
v___y_4207_ = v___y_4215_;
v___y_4208_ = v___y_4216_;
v___y_4209_ = v___y_4217_;
v___y_4210_ = v___y_4218_;
v___y_4211_ = v___y_4219_;
v___y_4212_ = v___y_4220_;
v___y_4213_ = v___x_4033_;
goto v___jp_4206_;
}
}
}
v___jp_4224_:
{
lean_object* v___x_4232_; 
lean_inc_ref(v___x_4078_);
v___x_4232_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4078_, v___y_4229_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; uint8_t v___x_4234_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref(v___x_4232_);
v___x_4234_ = l_Lean_Expr_hasMVar(v_a_4233_);
if (v___x_4234_ == 0)
{
v___y_4215_ = v___y_4225_;
v___y_4216_ = v___y_4226_;
v___y_4217_ = v___y_4227_;
v___y_4218_ = v___y_4228_;
v___y_4219_ = v___y_4229_;
v___y_4220_ = v___y_4230_;
v___y_4221_ = v_a_4233_;
v___y_4222_ = v___y_4231_;
goto v___jp_4214_;
}
else
{
v___y_4215_ = v___y_4225_;
v___y_4216_ = v___y_4226_;
v___y_4217_ = v___y_4227_;
v___y_4218_ = v___y_4228_;
v___y_4219_ = v___y_4229_;
v___y_4220_ = v___y_4230_;
v___y_4221_ = v_a_4233_;
v___y_4222_ = v___x_4033_;
goto v___jp_4214_;
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v___x_4078_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4235_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4232_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4232_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
v___jp_4243_:
{
if (v___y_4250_ == 0)
{
v___y_4080_ = v___y_4244_;
v___y_4081_ = v___y_4249_;
v___y_4082_ = v___y_4247_;
v___y_4083_ = v___y_4248_;
v___y_4084_ = v___y_4245_;
v___y_4085_ = v___y_4246_;
goto v___jp_4079_;
}
else
{
v___y_4225_ = v___y_4244_;
v___y_4226_ = v___y_4245_;
v___y_4227_ = v___y_4246_;
v___y_4228_ = v___y_4247_;
v___y_4229_ = v___y_4248_;
v___y_4230_ = v___y_4249_;
v___y_4231_ = v___y_4250_;
goto v___jp_4224_;
}
}
v___jp_4251_:
{
uint8_t v_useDecide_4258_; 
v_useDecide_4258_ = lean_ctor_get_uint8(v_config_3926_, sizeof(void*)*1);
if (v_useDecide_4258_ == 0)
{
v___y_4244_ = v_isHEq_4253_;
v___y_4245_ = v___y_4256_;
v___y_4246_ = v___y_4257_;
v___y_4247_ = v___y_4254_;
v___y_4248_ = v___y_4255_;
v___y_4249_ = v___y_4252_;
v___y_4250_ = v___x_4033_;
goto v___jp_4243_;
}
else
{
uint8_t v___x_4259_; 
v___x_4259_ = l_Lean_Expr_hasFVar(v___x_4078_);
if (v___x_4259_ == 0)
{
v___y_4225_ = v_isHEq_4253_;
v___y_4226_ = v___y_4256_;
v___y_4227_ = v___y_4257_;
v___y_4228_ = v___y_4254_;
v___y_4229_ = v___y_4255_;
v___y_4230_ = v___y_4252_;
v___y_4231_ = v_useDecide_4258_;
goto v___jp_4224_;
}
else
{
v___y_4244_ = v_isHEq_4253_;
v___y_4245_ = v___y_4256_;
v___y_4246_ = v___y_4257_;
v___y_4247_ = v___y_4254_;
v___y_4248_ = v___y_4255_;
v___y_4249_ = v___y_4252_;
v___y_4250_ = v___x_4033_;
goto v___jp_4243_;
}
}
}
v___jp_4260_:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_Meta_isExprDefEq(v___y_4262_, v___y_4267_, v___y_4265_, v___y_4264_, v___y_4261_, v___y_4263_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; uint8_t v___x_4270_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
lean_dec_ref(v___x_4268_);
v___x_4270_ = lean_unbox(v_a_4269_);
lean_dec(v_a_4269_);
if (v___x_4270_ == 0)
{
v___y_4252_ = v___y_4266_;
v_isHEq_4253_ = v___x_3937_;
v___y_4254_ = v___y_4265_;
v___y_4255_ = v___y_4264_;
v___y_4256_ = v___y_4261_;
v___y_4257_ = v___y_4263_;
goto v___jp_4251_;
}
else
{
lean_object* v___x_4271_; 
lean_dec_ref(v___x_4078_);
lean_dec_ref(v_config_3926_);
lean_inc(v_mvarId_3927_);
v___x_4271_ = l_Lean_MVarId_getType(v_mvarId_3927_, v___y_4265_, v___y_4264_, v___y_4261_, v___y_4263_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_object* v_a_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
lean_inc(v_a_4272_);
lean_dec_ref(v___x_4271_);
v___x_4273_ = l_Lean_LocalDecl_toExpr(v_val_3958_);
v___x_4274_ = l_Lean_Meta_mkEqOfHEq(v___x_4273_, v___x_3937_, v___y_4265_, v___y_4264_, v___y_4261_, v___y_4263_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v___x_4276_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
lean_dec_ref(v___x_4274_);
v___x_4276_ = l_Lean_Meta_mkNoConfusion(v_a_4272_, v_a_4275_, v___y_4265_, v___y_4264_, v___y_4261_, v___y_4263_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4278_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref(v___x_4276_);
v___x_4278_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3927_, v_a_4277_, v___y_4264_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
lean_dec_ref(v___x_4278_);
v___x_4279_ = lean_box(v___x_3937_);
v___x_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
v___x_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
lean_ctor_set(v___x_4281_, 1, v___x_3962_);
v___x_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
v_a_3944_ = v___x_4282_;
goto v___jp_3943_;
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
v_a_4283_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4278_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4278_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4291_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4276_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4276_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec(v_a_4272_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4299_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4274_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4274_);
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
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4307_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4271_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4271_);
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
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec_ref(v___x_4078_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4315_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4268_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4268_);
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
v___jp_4323_:
{
lean_object* v___x_4329_; 
lean_inc_ref(v___x_4078_);
v___x_4329_ = l_Lean_Meta_matchHEq_x3f(v___x_4078_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4330_; 
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
lean_inc(v_a_4330_);
lean_dec_ref(v___x_4329_);
if (lean_obj_tag(v_a_4330_) == 1)
{
lean_object* v_val_4331_; lean_object* v_snd_4332_; lean_object* v_snd_4333_; lean_object* v_fst_4334_; lean_object* v_fst_4335_; lean_object* v_fst_4336_; lean_object* v_snd_4337_; lean_object* v___x_4338_; 
v_val_4331_ = lean_ctor_get(v_a_4330_, 0);
lean_inc(v_val_4331_);
lean_dec_ref(v_a_4330_);
v_snd_4332_ = lean_ctor_get(v_val_4331_, 1);
lean_inc(v_snd_4332_);
v_snd_4333_ = lean_ctor_get(v_snd_4332_, 1);
lean_inc(v_snd_4333_);
v_fst_4334_ = lean_ctor_get(v_val_4331_, 0);
lean_inc(v_fst_4334_);
lean_dec(v_val_4331_);
v_fst_4335_ = lean_ctor_get(v_snd_4332_, 0);
lean_inc(v_fst_4335_);
lean_dec(v_snd_4332_);
v_fst_4336_ = lean_ctor_get(v_snd_4333_, 0);
lean_inc(v_fst_4336_);
v_snd_4337_ = lean_ctor_get(v_snd_4333_, 1);
lean_inc(v_snd_4337_);
lean_dec(v_snd_4333_);
v___x_4338_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4335_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4339_);
lean_dec_ref(v___x_4338_);
if (lean_obj_tag(v_a_4339_) == 1)
{
lean_object* v_val_4340_; lean_object* v___x_4341_; 
v_val_4340_ = lean_ctor_get(v_a_4339_, 0);
lean_inc(v_val_4340_);
lean_dec_ref(v_a_4339_);
v___x_4341_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4337_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v_a_4342_; 
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
lean_inc(v_a_4342_);
lean_dec_ref(v___x_4341_);
if (lean_obj_tag(v_a_4342_) == 1)
{
lean_object* v_toConstantVal_4343_; lean_object* v_val_4344_; lean_object* v_toConstantVal_4345_; lean_object* v_name_4346_; lean_object* v_name_4347_; uint8_t v___x_4348_; 
v_toConstantVal_4343_ = lean_ctor_get(v_val_4340_, 0);
lean_inc_ref(v_toConstantVal_4343_);
lean_dec(v_val_4340_);
v_val_4344_ = lean_ctor_get(v_a_4342_, 0);
lean_inc(v_val_4344_);
lean_dec_ref(v_a_4342_);
v_toConstantVal_4345_ = lean_ctor_get(v_val_4344_, 0);
lean_inc_ref(v_toConstantVal_4345_);
lean_dec(v_val_4344_);
v_name_4346_ = lean_ctor_get(v_toConstantVal_4343_, 0);
lean_inc(v_name_4346_);
lean_dec_ref(v_toConstantVal_4343_);
v_name_4347_ = lean_ctor_get(v_toConstantVal_4345_, 0);
lean_inc(v_name_4347_);
lean_dec_ref(v_toConstantVal_4345_);
v___x_4348_ = lean_name_eq(v_name_4346_, v_name_4347_);
lean_dec(v_name_4347_);
lean_dec(v_name_4346_);
if (v___x_4348_ == 0)
{
v___y_4261_ = v___y_4327_;
v___y_4262_ = v_fst_4334_;
v___y_4263_ = v___y_4328_;
v___y_4264_ = v___y_4326_;
v___y_4265_ = v___y_4325_;
v___y_4266_ = v_isEq_4324_;
v___y_4267_ = v_fst_4336_;
goto v___jp_4260_;
}
else
{
if (v___x_4033_ == 0)
{
lean_dec(v_fst_4336_);
lean_dec(v_fst_4334_);
v___y_4252_ = v_isEq_4324_;
v_isHEq_4253_ = v___x_3937_;
v___y_4254_ = v___y_4325_;
v___y_4255_ = v___y_4326_;
v___y_4256_ = v___y_4327_;
v___y_4257_ = v___y_4328_;
goto v___jp_4251_;
}
else
{
v___y_4261_ = v___y_4327_;
v___y_4262_ = v_fst_4334_;
v___y_4263_ = v___y_4328_;
v___y_4264_ = v___y_4326_;
v___y_4265_ = v___y_4325_;
v___y_4266_ = v_isEq_4324_;
v___y_4267_ = v_fst_4336_;
goto v___jp_4260_;
}
}
}
else
{
lean_dec(v_a_4342_);
lean_dec(v_val_4340_);
lean_dec(v_fst_4336_);
lean_dec(v_fst_4334_);
v___y_4252_ = v_isEq_4324_;
v_isHEq_4253_ = v___x_3937_;
v___y_4254_ = v___y_4325_;
v___y_4255_ = v___y_4326_;
v___y_4256_ = v___y_4327_;
v___y_4257_ = v___y_4328_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_dec(v_val_4340_);
lean_dec(v_fst_4336_);
lean_dec(v_fst_4334_);
lean_dec_ref(v___x_4078_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4349_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4341_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4341_);
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
else
{
lean_dec(v_a_4339_);
lean_dec(v_snd_4337_);
lean_dec(v_fst_4336_);
lean_dec(v_fst_4334_);
v___y_4252_ = v_isEq_4324_;
v_isHEq_4253_ = v___x_3937_;
v___y_4254_ = v___y_4325_;
v___y_4255_ = v___y_4326_;
v___y_4256_ = v___y_4327_;
v___y_4257_ = v___y_4328_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v_snd_4337_);
lean_dec(v_fst_4336_);
lean_dec(v_fst_4334_);
lean_dec_ref(v___x_4078_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4357_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4338_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4338_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
else
{
lean_dec(v_a_4330_);
v___y_4252_ = v_isEq_4324_;
v_isHEq_4253_ = v___x_4033_;
v___y_4254_ = v___y_4325_;
v___y_4255_ = v___y_4326_;
v___y_4256_ = v___y_4327_;
v___y_4257_ = v___y_4328_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec_ref(v___x_4078_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4365_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4329_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4329_);
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
v___jp_4373_:
{
lean_object* v___x_4378_; 
lean_inc_ref(v___x_4078_);
v___x_4378_ = l_Lean_Meta_matchEq_x3f(v___x_4078_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref(v___x_4378_);
if (lean_obj_tag(v_a_4379_) == 1)
{
lean_object* v_val_4380_; lean_object* v_snd_4381_; lean_object* v_fst_4382_; lean_object* v_snd_4383_; lean_object* v___x_4384_; 
v_val_4380_ = lean_ctor_get(v_a_4379_, 0);
lean_inc(v_val_4380_);
lean_dec_ref(v_a_4379_);
v_snd_4381_ = lean_ctor_get(v_val_4380_, 1);
lean_inc(v_snd_4381_);
lean_dec(v_val_4380_);
v_fst_4382_ = lean_ctor_get(v_snd_4381_, 0);
lean_inc(v_fst_4382_);
v_snd_4383_ = lean_ctor_get(v_snd_4381_, 1);
lean_inc(v_snd_4383_);
lean_dec(v_snd_4381_);
v___x_4384_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4382_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref(v___x_4384_);
if (lean_obj_tag(v_a_4385_) == 1)
{
lean_object* v_val_4386_; lean_object* v___x_4387_; 
v_val_4386_ = lean_ctor_get(v_a_4385_, 0);
lean_inc(v_val_4386_);
lean_dec_ref(v_a_4385_);
v___x_4387_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4383_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4388_);
lean_dec_ref(v___x_4387_);
if (lean_obj_tag(v_a_4388_) == 1)
{
lean_object* v_toConstantVal_4389_; lean_object* v_val_4390_; lean_object* v_toConstantVal_4391_; lean_object* v_name_4392_; lean_object* v_name_4393_; uint8_t v___x_4394_; 
v_toConstantVal_4389_ = lean_ctor_get(v_val_4386_, 0);
lean_inc_ref(v_toConstantVal_4389_);
lean_dec(v_val_4386_);
v_val_4390_ = lean_ctor_get(v_a_4388_, 0);
lean_inc(v_val_4390_);
lean_dec_ref(v_a_4388_);
v_toConstantVal_4391_ = lean_ctor_get(v_val_4390_, 0);
lean_inc_ref(v_toConstantVal_4391_);
lean_dec(v_val_4390_);
v_name_4392_ = lean_ctor_get(v_toConstantVal_4389_, 0);
lean_inc(v_name_4392_);
lean_dec_ref(v_toConstantVal_4389_);
v_name_4393_ = lean_ctor_get(v_toConstantVal_4391_, 0);
lean_inc(v_name_4393_);
lean_dec_ref(v_toConstantVal_4391_);
v___x_4394_ = lean_name_eq(v_name_4392_, v_name_4393_);
lean_dec(v_name_4393_);
lean_dec(v_name_4392_);
if (v___x_4394_ == 0)
{
lean_dec_ref(v___x_4078_);
lean_dec_ref(v_config_3926_);
v___y_3964_ = v___y_4374_;
v___y_3965_ = v___y_4376_;
v___y_3966_ = v___y_4375_;
v___y_3967_ = v___y_4377_;
goto v___jp_3963_;
}
else
{
if (v___x_4033_ == 0)
{
lean_del_object(v___x_3960_);
v_isEq_4324_ = v___x_3937_;
v___y_4325_ = v___y_4374_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4376_;
v___y_4328_ = v___y_4377_;
goto v___jp_4323_;
}
else
{
lean_dec_ref(v___x_4078_);
lean_dec_ref(v_config_3926_);
v___y_3964_ = v___y_4374_;
v___y_3965_ = v___y_4376_;
v___y_3966_ = v___y_4375_;
v___y_3967_ = v___y_4377_;
goto v___jp_3963_;
}
}
}
else
{
lean_dec(v_a_4388_);
lean_dec(v_val_4386_);
lean_del_object(v___x_3960_);
v_isEq_4324_ = v___x_3937_;
v___y_4325_ = v___y_4374_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4376_;
v___y_4328_ = v___y_4377_;
goto v___jp_4323_;
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
lean_dec(v_val_4386_);
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4395_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4387_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4387_);
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
lean_dec(v_a_4385_);
lean_dec(v_snd_4383_);
lean_del_object(v___x_3960_);
v_isEq_4324_ = v___x_3937_;
v___y_4325_ = v___y_4374_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4376_;
v___y_4328_ = v___y_4377_;
goto v___jp_4323_;
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_snd_4383_);
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
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
lean_dec(v_a_4379_);
lean_del_object(v___x_3960_);
v_isEq_4324_ = v___x_4033_;
v___y_4325_ = v___y_4374_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4376_;
v___y_4328_ = v___y_4377_;
goto v___jp_4323_;
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4411_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4378_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4378_);
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
v___jp_4419_:
{
lean_object* v___x_4424_; 
lean_inc_ref(v___x_4078_);
v___x_4424_ = l_refutableHasNotBit_x3f(v___x_4078_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref(v___x_4424_);
if (lean_obj_tag(v_a_4425_) == 1)
{
lean_object* v_val_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4466_; 
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec_ref(v_config_3926_);
v_val_4426_ = lean_ctor_get(v_a_4425_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_a_4425_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4428_ = v_a_4425_;
v_isShared_4429_ = v_isSharedCheck_4466_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_val_4426_);
lean_dec(v_a_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4466_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; 
lean_inc(v_mvarId_3927_);
v___x_4430_ = l_Lean_MVarId_getType(v_mvarId_3927_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_a_4431_);
lean_dec_ref(v___x_4430_);
v___x_4432_ = l_Lean_LocalDecl_toExpr(v_val_3958_);
v___x_4433_ = l_Lean_Meta_mkAbsurd(v_a_4431_, v_val_4426_, v___x_4432_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4435_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref(v___x_4433_);
v___x_4435_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3927_, v_a_4434_, v___y_4421_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v___x_4436_; lean_object* v___x_4438_; 
lean_dec_ref(v___x_4435_);
v___x_4436_ = lean_box(v___x_3937_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___x_4436_);
v___x_4438_ = v___x_4428_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4438_);
lean_ctor_set(v___x_4439_, 1, v___x_3962_);
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
v_a_3944_ = v___x_4440_;
goto v___jp_3943_;
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_del_object(v___x_4428_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
v_a_4442_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4435_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4435_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_del_object(v___x_4428_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4450_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4433_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4433_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_del_object(v___x_4428_);
lean_dec(v_val_4426_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4458_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4430_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4430_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
else
{
lean_object* v___x_4467_; 
lean_dec(v_a_4425_);
lean_inc_ref(v___x_4078_);
v___x_4467_ = l_Lean_Meta_matchNe_x3f(v___x_4078_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc(v_a_4468_);
lean_dec_ref(v___x_4467_);
if (lean_obj_tag(v_a_4468_) == 1)
{
lean_object* v_val_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4539_; 
v_val_4469_ = lean_ctor_get(v_a_4468_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_a_4468_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4471_ = v_a_4468_;
v_isShared_4472_ = v_isSharedCheck_4539_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_val_4469_);
lean_dec(v_a_4468_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4539_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v_snd_4473_; lean_object* v_fst_4474_; lean_object* v_snd_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4538_; 
v_snd_4473_ = lean_ctor_get(v_val_4469_, 1);
lean_inc(v_snd_4473_);
lean_dec(v_val_4469_);
v_fst_4474_ = lean_ctor_get(v_snd_4473_, 0);
v_snd_4475_ = lean_ctor_get(v_snd_4473_, 1);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_snd_4473_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4477_ = v_snd_4473_;
v_isShared_4478_ = v_isSharedCheck_4538_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_snd_4475_);
lean_inc(v_fst_4474_);
lean_dec(v_snd_4473_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4538_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4479_; 
lean_inc(v_fst_4474_);
v___x_4479_ = l_Lean_Meta_isExprDefEq(v_fst_4474_, v_snd_4475_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; uint8_t v___x_4481_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref(v___x_4479_);
v___x_4481_ = lean_unbox(v_a_4480_);
lean_dec(v_a_4480_);
if (v___x_4481_ == 0)
{
lean_del_object(v___x_4477_);
lean_dec(v_fst_4474_);
lean_del_object(v___x_4471_);
v___y_4374_ = v___y_4420_;
v___y_4375_ = v___y_4421_;
v___y_4376_ = v___y_4422_;
v___y_4377_ = v___y_4423_;
goto v___jp_4373_;
}
else
{
lean_object* v___x_4482_; 
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec_ref(v_config_3926_);
lean_inc(v_mvarId_3927_);
v___x_4482_ = l_Lean_MVarId_getType(v_mvarId_3927_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v___x_4484_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
lean_dec_ref(v___x_4482_);
v___x_4484_ = l_Lean_Meta_mkEqRefl(v_fst_4474_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref(v___x_4484_);
v___x_4486_ = l_Lean_LocalDecl_toExpr(v_val_3958_);
v___x_4487_ = l_Lean_Meta_mkAbsurd(v_a_4483_, v_a_4485_, v___x_4486_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4489_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4488_);
lean_dec_ref(v___x_4487_);
v___x_4489_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3927_, v_a_4488_, v___y_4421_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v___x_4490_; lean_object* v___x_4492_; 
lean_dec_ref(v___x_4489_);
v___x_4490_ = lean_box(v___x_3937_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v___x_4490_);
v___x_4492_ = v___x_4471_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4494_; 
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 1, v___x_3962_);
lean_ctor_set(v___x_4477_, 0, v___x_4492_);
v___x_4494_ = v___x_4477_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4492_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v___x_3962_);
v___x_4494_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
v_a_3944_ = v___x_4495_;
goto v___jp_3943_;
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_del_object(v___x_4477_);
lean_del_object(v___x_4471_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
v_a_4498_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4489_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4489_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_del_object(v___x_4477_);
lean_del_object(v___x_4471_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4506_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4487_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4487_);
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
lean_dec(v_a_4483_);
lean_del_object(v___x_4477_);
lean_del_object(v___x_4471_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4514_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4484_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4484_);
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
lean_del_object(v___x_4477_);
lean_dec(v_fst_4474_);
lean_del_object(v___x_4471_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_4522_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4482_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4482_);
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
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
lean_del_object(v___x_4477_);
lean_dec(v_fst_4474_);
lean_del_object(v___x_4471_);
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4530_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4479_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4479_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4468_);
v___y_4374_ = v___y_4420_;
v___y_4375_ = v___y_4421_;
v___y_4376_ = v___y_4422_;
v___y_4377_ = v___y_4423_;
goto v___jp_4373_;
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4540_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4467_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4467_);
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
}
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4555_; 
lean_dec_ref(v___x_4078_);
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4548_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4550_ = v___x_4424_;
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4424_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
}
else
{
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
v_a_3952_ = v___x_4004_;
goto v___jp_3951_;
}
v___jp_3963_:
{
lean_object* v___x_3968_; 
lean_inc(v_mvarId_3927_);
v___x_3968_ = l_Lean_MVarId_getType(v_mvarId_3927_, v___y_3964_, v___y_3966_, v___y_3965_, v___y_3967_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref(v___x_3968_);
v___x_3970_ = l_Lean_LocalDecl_toExpr(v_val_3958_);
v___x_3971_ = l_Lean_Meta_mkNoConfusion(v_a_3969_, v___x_3970_, v___y_3964_, v___y_3966_, v___y_3965_, v___y_3967_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3973_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref(v___x_3971_);
v___x_3973_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3927_, v_a_3972_, v___y_3966_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
lean_dec_ref(v___x_3973_);
v___x_3974_ = lean_box(v___x_3937_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3974_);
v___x_3976_ = v___x_3960_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
lean_ctor_set(v___x_3977_, 1, v___x_3962_);
v___x_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
v_a_3944_ = v___x_3978_;
goto v___jp_3943_;
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_del_object(v___x_3960_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
v_a_3980_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3973_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3973_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_del_object(v___x_3960_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_3988_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3971_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3971_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
v_a_3996_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3968_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3968_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
v___jp_4005_:
{
lean_object* v_searchFuel_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v_searchFuel_4010_ = lean_ctor_get(v_config_3926_, 0);
v___x_4011_ = l_Lean_LocalDecl_fvarId(v_val_3958_);
lean_dec(v_val_3958_);
lean_inc(v_searchFuel_4010_);
lean_inc(v_mvarId_3927_);
v___x_4012_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3927_, v___x_4011_, v_searchFuel_4010_, v___y_4009_, v___y_4007_, v___y_4006_, v___y_4008_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; uint8_t v___x_4014_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref(v___x_4012_);
v___x_4014_ = lean_unbox(v_a_4013_);
lean_dec(v_a_4013_);
if (v___x_4014_ == 0)
{
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
v_a_3952_ = v___x_4004_;
goto v___jp_3951_;
}
else
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v___x_4015_ = lean_box(v___x_3937_);
v___x_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
v___x_4017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
lean_ctor_set(v___x_4017_, 1, v___x_3962_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
v_a_3944_ = v___x_4018_;
goto v___jp_3943_;
}
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4019_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4012_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4012_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
v___jp_4027_:
{
if (v___y_4032_ == 0)
{
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
v_a_3952_ = v___x_4004_;
goto v___jp_3951_;
}
else
{
v___y_4006_ = v___y_4028_;
v___y_4007_ = v___y_4029_;
v___y_4008_ = v___y_4031_;
v___y_4009_ = v___y_4030_;
goto v___jp_4005_;
}
}
v___jp_4034_:
{
if (v___y_4035_ == 0)
{
v___y_4006_ = v___y_4036_;
v___y_4007_ = v___y_4037_;
v___y_4008_ = v___y_4039_;
v___y_4009_ = v___y_4038_;
goto v___jp_4005_;
}
else
{
v___y_4028_ = v___y_4036_;
v___y_4029_ = v___y_4037_;
v___y_4030_ = v___y_4038_;
v___y_4031_ = v___y_4039_;
v___y_4032_ = v___x_4033_;
goto v___jp_4027_;
}
}
v___jp_4040_:
{
if (v___y_4046_ == 0)
{
v___y_4028_ = v___y_4042_;
v___y_4029_ = v___y_4043_;
v___y_4030_ = v___y_4045_;
v___y_4031_ = v___y_4044_;
v___y_4032_ = v___x_4033_;
goto v___jp_4027_;
}
else
{
v___y_4035_ = v___y_4041_;
v___y_4036_ = v___y_4042_;
v___y_4037_ = v___y_4043_;
v___y_4038_ = v___y_4045_;
v___y_4039_ = v___y_4044_;
goto v___jp_4034_;
}
}
v___jp_4047_:
{
uint8_t v_emptyType_4054_; 
v_emptyType_4054_ = lean_ctor_get_uint8(v_config_3926_, sizeof(void*)*1 + 1);
if (v_emptyType_4054_ == 0)
{
v___y_4041_ = v___y_4048_;
v___y_4042_ = v___y_4052_;
v___y_4043_ = v___y_4051_;
v___y_4044_ = v___y_4053_;
v___y_4045_ = v___y_4050_;
v___y_4046_ = v___x_4033_;
goto v___jp_4040_;
}
else
{
if (v___y_4049_ == 0)
{
v___y_4035_ = v___y_4048_;
v___y_4036_ = v___y_4052_;
v___y_4037_ = v___y_4051_;
v___y_4038_ = v___y_4050_;
v___y_4039_ = v___y_4053_;
goto v___jp_4034_;
}
else
{
v___y_4041_ = v___y_4048_;
v___y_4042_ = v___y_4052_;
v___y_4043_ = v___y_4051_;
v___y_4044_ = v___y_4053_;
v___y_4045_ = v___y_4050_;
v___y_4046_ = v___x_4033_;
goto v___jp_4040_;
}
}
}
v___jp_4055_:
{
if (v___y_4062_ == 0)
{
v___y_4048_ = v___y_4057_;
v___y_4049_ = v___y_4061_;
v___y_4050_ = v___y_4059_;
v___y_4051_ = v___y_4056_;
v___y_4052_ = v___y_4060_;
v___y_4053_ = v___y_4058_;
goto v___jp_4047_;
}
else
{
lean_object* v___x_4063_; 
lean_inc(v_val_3958_);
lean_inc(v_mvarId_3927_);
v___x_4063_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3927_, v_val_3958_, v___y_4059_, v___y_4056_, v___y_4060_, v___y_4058_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; uint8_t v___x_4065_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref(v___x_4063_);
v___x_4065_ = lean_unbox(v_a_4064_);
lean_dec(v_a_4064_);
if (v___x_4065_ == 0)
{
v___y_4048_ = v___y_4057_;
v___y_4049_ = v___y_4061_;
v___y_4050_ = v___y_4059_;
v___y_4051_ = v___y_4056_;
v___y_4052_ = v___y_4060_;
v___y_4053_ = v___y_4058_;
goto v___jp_4047_;
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
lean_dec(v_val_3958_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v___x_4066_ = lean_box(v___x_3937_);
v___x_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
v___x_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
lean_ctor_set(v___x_4068_, 1, v___x_3962_);
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
v_a_3944_ = v___x_4069_;
goto v___jp_3943_;
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec(v_val_3958_);
lean_del_object(v___x_3941_);
lean_dec(v_snd_3939_);
lean_dec(v_mvarId_3927_);
lean_dec_ref(v_config_3926_);
v_a_4070_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4063_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4063_);
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
}
}
}
v___jp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3947_; 
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v_a_3944_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3945_);
v___x_3947_ = v___x_3941_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3945_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_snd_3939_);
v___x_3947_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
return v___x_3948_;
}
}
v___jp_3951_:
{
lean_object* v___x_3953_; size_t v___x_3954_; size_t v___x_3955_; lean_object* v___x_3956_; 
v___x_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3950_);
lean_ctor_set(v___x_3953_, 1, v_a_3952_);
v___x_3954_ = ((size_t)1ULL);
v___x_3955_ = lean_usize_add(v_i_3930_, v___x_3954_);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3926_, v_mvarId_3927_, v_as_3928_, v_sz_3929_, v___x_3955_, v___x_3953_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
return v___x_3956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4629_, lean_object* v_mvarId_4630_, lean_object* v_as_4631_, lean_object* v_sz_4632_, lean_object* v_i_4633_, lean_object* v_b_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_){
_start:
{
size_t v_sz_boxed_4640_; size_t v_i_boxed_4641_; lean_object* v_res_4642_; 
v_sz_boxed_4640_ = lean_unbox_usize(v_sz_4632_);
lean_dec(v_sz_4632_);
v_i_boxed_4641_ = lean_unbox_usize(v_i_4633_);
lean_dec(v_i_4633_);
v_res_4642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4629_, v_mvarId_4630_, v_as_4631_, v_sz_boxed_4640_, v_i_boxed_4641_, v_b_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec_ref(v_as_4631_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4643_, lean_object* v_config_4644_, lean_object* v_mvarId_4645_, lean_object* v_n_4646_, lean_object* v_b_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
if (lean_obj_tag(v_n_4646_) == 0)
{
lean_object* v_cs_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4687_; 
v_cs_4653_ = lean_ctor_get(v_n_4646_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v_n_4646_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4655_ = v_n_4646_;
v_isShared_4656_ = v_isSharedCheck_4687_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_cs_4653_);
lean_dec(v_n_4646_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4687_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; size_t v_sz_4659_; size_t v___x_4660_; lean_object* v___x_4661_; 
v___x_4657_ = lean_box(0);
v___x_4658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
lean_ctor_set(v___x_4658_, 1, v_b_4647_);
v_sz_4659_ = lean_array_size(v_cs_4653_);
v___x_4660_ = ((size_t)0ULL);
v___x_4661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4643_, v_config_4644_, v_mvarId_4645_, v_cs_4653_, v_sz_4659_, v___x_4660_, v___x_4658_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
lean_dec_ref(v_cs_4653_);
if (lean_obj_tag(v___x_4661_) == 0)
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4678_; 
v_a_4662_ = lean_ctor_get(v___x_4661_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4661_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4664_ = v___x_4661_;
v_isShared_4665_ = v_isSharedCheck_4678_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4661_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4678_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v_fst_4666_; 
v_fst_4666_ = lean_ctor_get(v_a_4662_, 0);
if (lean_obj_tag(v_fst_4666_) == 0)
{
lean_object* v_snd_4667_; lean_object* v___x_4669_; 
v_snd_4667_ = lean_ctor_get(v_a_4662_, 1);
lean_inc(v_snd_4667_);
lean_dec(v_a_4662_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set_tag(v___x_4655_, 1);
lean_ctor_set(v___x_4655_, 0, v_snd_4667_);
v___x_4669_ = v___x_4655_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_snd_4667_);
v___x_4669_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
lean_object* v___x_4671_; 
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 0, v___x_4669_);
v___x_4671_ = v___x_4664_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4669_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
else
{
lean_object* v_val_4674_; lean_object* v___x_4676_; 
lean_inc_ref(v_fst_4666_);
lean_dec(v_a_4662_);
lean_del_object(v___x_4655_);
v_val_4674_ = lean_ctor_get(v_fst_4666_, 0);
lean_inc(v_val_4674_);
lean_dec_ref(v_fst_4666_);
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 0, v_val_4674_);
v___x_4676_ = v___x_4664_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_val_4674_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
lean_del_object(v___x_4655_);
v_a_4679_ = lean_ctor_get(v___x_4661_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4661_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4661_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4661_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
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
}
else
{
lean_object* v_vs_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4722_; 
v_vs_4688_ = lean_ctor_get(v_n_4646_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v_n_4646_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4690_ = v_n_4646_;
v_isShared_4691_ = v_isSharedCheck_4722_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_vs_4688_);
lean_dec(v_n_4646_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4722_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; size_t v_sz_4694_; size_t v___x_4695_; lean_object* v___x_4696_; 
v___x_4692_ = lean_box(0);
v___x_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
lean_ctor_set(v___x_4693_, 1, v_b_4647_);
v_sz_4694_ = lean_array_size(v_vs_4688_);
v___x_4695_ = ((size_t)0ULL);
v___x_4696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4644_, v_mvarId_4645_, v_vs_4688_, v_sz_4694_, v___x_4695_, v___x_4693_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
lean_dec_ref(v_vs_4688_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4713_; 
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4699_ = v___x_4696_;
v_isShared_4700_ = v_isSharedCheck_4713_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4696_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4713_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v_fst_4701_; 
v_fst_4701_ = lean_ctor_get(v_a_4697_, 0);
if (lean_obj_tag(v_fst_4701_) == 0)
{
lean_object* v_snd_4702_; lean_object* v___x_4704_; 
v_snd_4702_ = lean_ctor_get(v_a_4697_, 1);
lean_inc(v_snd_4702_);
lean_dec(v_a_4697_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 0, v_snd_4702_);
v___x_4704_ = v___x_4690_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_snd_4702_);
v___x_4704_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
lean_object* v___x_4706_; 
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 0, v___x_4704_);
v___x_4706_ = v___x_4699_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4704_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
else
{
lean_object* v_val_4709_; lean_object* v___x_4711_; 
lean_inc_ref(v_fst_4701_);
lean_dec(v_a_4697_);
lean_del_object(v___x_4690_);
v_val_4709_ = lean_ctor_get(v_fst_4701_, 0);
lean_inc(v_val_4709_);
lean_dec_ref(v_fst_4701_);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 0, v_val_4709_);
v___x_4711_ = v___x_4699_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_val_4709_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
lean_del_object(v___x_4690_);
v_a_4714_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4696_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4696_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4723_, lean_object* v_config_4724_, lean_object* v_mvarId_4725_, lean_object* v_as_4726_, size_t v_sz_4727_, size_t v_i_4728_, lean_object* v_b_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
uint8_t v___x_4735_; 
v___x_4735_ = lean_usize_dec_lt(v_i_4728_, v_sz_4727_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; 
lean_dec(v_mvarId_4725_);
lean_dec_ref(v_config_4724_);
v___x_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4736_, 0, v_b_4729_);
return v___x_4736_;
}
else
{
lean_object* v_snd_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4771_; 
v_snd_4737_ = lean_ctor_get(v_b_4729_, 1);
v_isSharedCheck_4771_ = !lean_is_exclusive(v_b_4729_);
if (v_isSharedCheck_4771_ == 0)
{
lean_object* v_unused_4772_; 
v_unused_4772_ = lean_ctor_get(v_b_4729_, 0);
lean_dec(v_unused_4772_);
v___x_4739_ = v_b_4729_;
v_isShared_4740_ = v_isSharedCheck_4771_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_snd_4737_);
lean_dec(v_b_4729_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4771_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v_a_4741_; lean_object* v___x_4742_; 
v_a_4741_ = lean_array_uget_borrowed(v_as_4726_, v_i_4728_);
lean_inc(v_snd_4737_);
lean_inc(v_a_4741_);
lean_inc(v_mvarId_4725_);
lean_inc_ref(v_config_4724_);
v___x_4742_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4723_, v_config_4724_, v_mvarId_4725_, v_a_4741_, v_snd_4737_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
if (lean_obj_tag(v___x_4742_) == 0)
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4762_; 
v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4745_ = v___x_4742_;
v_isShared_4746_ = v_isSharedCheck_4762_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4742_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4762_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
if (lean_obj_tag(v_a_4743_) == 0)
{
lean_object* v___x_4747_; lean_object* v___x_4749_; 
lean_dec(v_mvarId_4725_);
lean_dec_ref(v_config_4724_);
v___x_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4747_, 0, v_a_4743_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v___x_4747_);
v___x_4749_ = v___x_4739_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4747_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_snd_4737_);
v___x_4749_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4751_; 
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 0, v___x_4749_);
v___x_4751_ = v___x_4745_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4749_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4755_; lean_object* v___x_4757_; 
lean_del_object(v___x_4745_);
lean_dec(v_snd_4737_);
v_a_4754_ = lean_ctor_get(v_a_4743_, 0);
lean_inc(v_a_4754_);
lean_dec_ref(v_a_4743_);
v___x_4755_ = lean_box(0);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 1, v_a_4754_);
lean_ctor_set(v___x_4739_, 0, v___x_4755_);
v___x_4757_ = v___x_4739_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4761_, 1, v_a_4754_);
v___x_4757_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
size_t v___x_4758_; size_t v___x_4759_; 
v___x_4758_ = ((size_t)1ULL);
v___x_4759_ = lean_usize_add(v_i_4728_, v___x_4758_);
v_i_4728_ = v___x_4759_;
v_b_4729_ = v___x_4757_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_del_object(v___x_4739_);
lean_dec(v_snd_4737_);
lean_dec(v_mvarId_4725_);
lean_dec_ref(v_config_4724_);
v_a_4763_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4742_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4742_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4773_, lean_object* v_config_4774_, lean_object* v_mvarId_4775_, lean_object* v_as_4776_, lean_object* v_sz_4777_, lean_object* v_i_4778_, lean_object* v_b_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
size_t v_sz_boxed_4785_; size_t v_i_boxed_4786_; lean_object* v_res_4787_; 
v_sz_boxed_4785_ = lean_unbox_usize(v_sz_4777_);
lean_dec(v_sz_4777_);
v_i_boxed_4786_ = lean_unbox_usize(v_i_4778_);
lean_dec(v_i_4778_);
v_res_4787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4773_, v_config_4774_, v_mvarId_4775_, v_as_4776_, v_sz_boxed_4785_, v_i_boxed_4786_, v_b_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec_ref(v_as_4776_);
lean_dec_ref(v_init_4773_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4788_, lean_object* v_config_4789_, lean_object* v_mvarId_4790_, lean_object* v_n_4791_, lean_object* v_b_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v_res_4798_; 
v_res_4798_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4788_, v_config_4789_, v_mvarId_4790_, v_n_4791_, v_b_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_);
lean_dec(v___y_4796_);
lean_dec_ref(v___y_4795_);
lean_dec(v___y_4794_);
lean_dec_ref(v___y_4793_);
lean_dec_ref(v_init_4788_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4799_, lean_object* v_mvarId_4800_, lean_object* v_t_4801_, lean_object* v_init_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
lean_object* v_root_4808_; lean_object* v_tail_4809_; lean_object* v___x_4810_; 
v_root_4808_ = lean_ctor_get(v_t_4801_, 0);
lean_inc_ref(v_root_4808_);
v_tail_4809_ = lean_ctor_get(v_t_4801_, 1);
lean_inc_ref(v_tail_4809_);
lean_dec_ref(v_t_4801_);
lean_inc(v_mvarId_4800_);
lean_inc_ref(v_config_4799_);
lean_inc_ref(v_init_4802_);
v___x_4810_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4802_, v_config_4799_, v_mvarId_4800_, v_root_4808_, v_init_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
lean_dec_ref(v_init_4802_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4847_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4847_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4847_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
if (lean_obj_tag(v_a_4811_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4817_; 
lean_dec_ref(v_tail_4809_);
lean_dec(v_mvarId_4800_);
lean_dec_ref(v_config_4799_);
v_a_4815_ = lean_ctor_get(v_a_4811_, 0);
lean_inc(v_a_4815_);
lean_dec_ref(v_a_4811_);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v_a_4815_);
v___x_4817_ = v___x_4813_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4815_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; size_t v_sz_4822_; size_t v___x_4823_; lean_object* v___x_4824_; 
lean_del_object(v___x_4813_);
v_a_4819_ = lean_ctor_get(v_a_4811_, 0);
lean_inc(v_a_4819_);
lean_dec_ref(v_a_4811_);
v___x_4820_ = lean_box(0);
v___x_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
lean_ctor_set(v___x_4821_, 1, v_a_4819_);
v_sz_4822_ = lean_array_size(v_tail_4809_);
v___x_4823_ = ((size_t)0ULL);
v___x_4824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4799_, v_mvarId_4800_, v_tail_4809_, v_sz_4822_, v___x_4823_, v___x_4821_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
lean_dec_ref(v_tail_4809_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4838_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4827_ = v___x_4824_;
v_isShared_4828_ = v_isSharedCheck_4838_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4824_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4838_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v_fst_4829_; 
v_fst_4829_ = lean_ctor_get(v_a_4825_, 0);
if (lean_obj_tag(v_fst_4829_) == 0)
{
lean_object* v_snd_4830_; lean_object* v___x_4832_; 
v_snd_4830_ = lean_ctor_get(v_a_4825_, 1);
lean_inc(v_snd_4830_);
lean_dec(v_a_4825_);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 0, v_snd_4830_);
v___x_4832_ = v___x_4827_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_snd_4830_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
else
{
lean_object* v_val_4834_; lean_object* v___x_4836_; 
lean_inc_ref(v_fst_4829_);
lean_dec(v_a_4825_);
v_val_4834_ = lean_ctor_get(v_fst_4829_, 0);
lean_inc(v_val_4834_);
lean_dec_ref(v_fst_4829_);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 0, v_val_4834_);
v___x_4836_ = v___x_4827_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_val_4834_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
v_a_4839_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4824_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4824_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
lean_dec_ref(v_tail_4809_);
lean_dec(v_mvarId_4800_);
lean_dec_ref(v_config_4799_);
v_a_4848_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4810_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4810_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4856_, lean_object* v_mvarId_4857_, lean_object* v_t_4858_, lean_object* v_init_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4856_, v_mvarId_4857_, v_t_4858_, v_init_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4866_, lean_object* v___x_4867_, lean_object* v_config_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v___x_4874_; 
lean_inc(v_mvarId_4866_);
v___x_4874_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4866_, v___x_4867_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v___x_4875_; 
lean_dec_ref(v___x_4874_);
lean_inc(v_mvarId_4866_);
v___x_4875_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4866_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4909_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4878_ = v___x_4875_;
v_isShared_4879_ = v_isSharedCheck_4909_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4875_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4909_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
uint8_t v___x_4880_; 
v___x_4880_ = lean_unbox(v_a_4876_);
if (v___x_4880_ == 0)
{
lean_object* v_lctx_4881_; lean_object* v_decls_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
lean_del_object(v___x_4878_);
v_lctx_4881_ = lean_ctor_get(v___y_4869_, 2);
v_decls_4882_ = lean_ctor_get(v_lctx_4881_, 1);
lean_inc_ref(v_decls_4882_);
v___x_4883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4884_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4868_, v_mvarId_4866_, v_decls_4882_, v___x_4883_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
lean_dec_ref(v___y_4869_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4897_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4887_ = v___x_4884_;
v_isShared_4888_ = v_isSharedCheck_4897_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4884_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4897_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v_fst_4889_; 
v_fst_4889_ = lean_ctor_get(v_a_4885_, 0);
lean_inc(v_fst_4889_);
lean_dec(v_a_4885_);
if (lean_obj_tag(v_fst_4889_) == 0)
{
lean_object* v___x_4891_; 
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 0, v_a_4876_);
v___x_4891_ = v___x_4887_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4876_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
else
{
lean_object* v_val_4893_; lean_object* v___x_4895_; 
lean_dec(v_a_4876_);
v_val_4893_ = lean_ctor_get(v_fst_4889_, 0);
lean_inc(v_val_4893_);
lean_dec_ref(v_fst_4889_);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 0, v_val_4893_);
v___x_4895_ = v___x_4887_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_val_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
}
else
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4905_; 
lean_dec(v_a_4876_);
v_a_4898_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4900_ = v___x_4884_;
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4884_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4901_ == 0)
{
v___x_4903_ = v___x_4900_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_a_4898_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
}
else
{
lean_object* v___x_4907_; 
lean_dec_ref(v___y_4869_);
lean_dec_ref(v_config_4868_);
lean_dec(v_mvarId_4866_);
if (v_isShared_4879_ == 0)
{
v___x_4907_ = v___x_4878_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4876_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
else
{
lean_dec_ref(v___y_4869_);
lean_dec_ref(v_config_4868_);
lean_dec(v_mvarId_4866_);
return v___x_4875_;
}
}
else
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
lean_dec_ref(v___y_4869_);
lean_dec_ref(v_config_4868_);
lean_dec(v_mvarId_4866_);
v_a_4910_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4874_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4874_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4918_, lean_object* v___x_4919_, lean_object* v_config_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4918_, v___x_4919_, v_config_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec(v___y_4922_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4929_, lean_object* v_config_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v___x_4936_; lean_object* v___f_4937_; lean_object* v___x_4938_; 
v___x_4936_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4929_);
v___f_4937_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4937_, 0, v_mvarId_4929_);
lean_closure_set(v___f_4937_, 1, v___x_4936_);
lean_closure_set(v___f_4937_, 2, v_config_4930_);
v___x_4938_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4929_, v___f_4937_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4939_, lean_object* v_config_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_MVarId_contradictionCore(v_mvarId_4939_, v_config_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4947_, lean_object* v_config_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_){
_start:
{
lean_object* v___x_4954_; 
lean_inc(v_mvarId_4947_);
v___x_4954_ = l_Lean_MVarId_contradictionCore(v_mvarId_4947_, v_config_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4967_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4957_ = v___x_4954_;
v_isShared_4958_ = v_isSharedCheck_4967_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_a_4955_);
lean_dec(v___x_4954_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4967_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
uint8_t v___x_4959_; 
v___x_4959_ = lean_unbox(v_a_4955_);
lean_dec(v_a_4955_);
if (v___x_4959_ == 0)
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
lean_del_object(v___x_4957_);
v___x_4960_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4961_ = lean_box(0);
v___x_4962_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4960_, v_mvarId_4947_, v___x_4961_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
return v___x_4962_;
}
else
{
lean_object* v___x_4963_; lean_object* v___x_4965_; 
lean_dec(v_mvarId_4947_);
v___x_4963_ = lean_box(0);
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 0, v___x_4963_);
v___x_4965_ = v___x_4957_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4963_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
else
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
lean_dec(v_mvarId_4947_);
v_a_4968_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4954_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4954_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4976_, lean_object* v_config_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Lean_MVarId_contradiction(v_mvarId_4976_, v_config_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5046_; uint8_t v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5046_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_5047_ = 0;
v___x_5048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_5049_ = l_Lean_registerTraceClass(v___x_5046_, v___x_5047_, v___x_5048_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_5051_;
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
