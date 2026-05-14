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
lean_dec_ref(v___y_509_);
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
lean_ctor_set(v___x_514_, 0, v___y_510_);
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___y_510_);
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
lean_dec_ref(v___y_510_);
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
lean_dec_ref(v___y_510_);
lean_dec(v_a_507_);
return v___y_509_;
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
v___y_509_ = v___y_530_;
v___y_510_ = v_a_531_;
v___y_511_ = v___x_533_;
goto v___jp_508_;
}
else
{
v___y_509_ = v___y_530_;
v___y_510_ = v_a_531_;
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
lean_object* v_ref_605_; lean_object* v___x_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_652_; 
v_ref_605_ = lean_ctor_get(v___y_602_, 5);
v___x_606_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_652_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_652_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_652_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v_traceState_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_cache_617_; lean_object* v_messages_618_; lean_object* v_infoState_619_; lean_object* v_snapshotTasks_620_; lean_object* v_newDecls_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_651_; 
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
v_newDecls_621_ = lean_ctor_get(v___x_611_, 9);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_651_ == 0)
{
v___x_623_ = v___x_611_;
v_isShared_624_ = v_isSharedCheck_651_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_newDecls_621_);
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
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_651_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint64_t v_tid_625_; lean_object* v_traces_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_650_; 
v_tid_625_ = lean_ctor_get_uint64(v_traceState_612_, sizeof(void*)*1);
v_traces_626_ = lean_ctor_get(v_traceState_612_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_traceState_612_);
if (v_isSharedCheck_650_ == 0)
{
v___x_628_ = v_traceState_612_;
v_isShared_629_ = v_isSharedCheck_650_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_traces_626_);
lean_dec(v_traceState_612_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_650_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; double v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_630_ = lean_box(0);
v___x_631_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_632_ = 0;
v___x_633_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_634_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_634_, 0, v_cls_598_);
lean_ctor_set(v___x_634_, 1, v___x_630_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_ctor_set_float(v___x_634_, sizeof(void*)*3, v___x_631_);
lean_ctor_set_float(v___x_634_, sizeof(void*)*3 + 8, v___x_631_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*3 + 16, v___x_632_);
v___x_635_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_636_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v_a_607_);
lean_ctor_set(v___x_636_, 2, v___x_635_);
lean_inc(v_ref_605_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v_ref_605_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = l_Lean_PersistentArray_push___redArg(v_traces_626_, v___x_637_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_638_);
v___x_640_ = v___x_628_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_638_);
lean_ctor_set_uint64(v_reuseFailAlloc_649_, sizeof(void*)*1, v_tid_625_);
v___x_640_ = v_reuseFailAlloc_649_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 4, v___x_640_);
v___x_642_ = v___x_623_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_env_613_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_648_, 5, v_cache_617_);
lean_ctor_set(v_reuseFailAlloc_648_, 6, v_messages_618_);
lean_ctor_set(v_reuseFailAlloc_648_, 7, v_infoState_619_);
lean_ctor_set(v_reuseFailAlloc_648_, 8, v_snapshotTasks_620_);
lean_ctor_set(v_reuseFailAlloc_648_, 9, v_newDecls_621_);
v___x_642_ = v_reuseFailAlloc_648_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_643_ = lean_st_ref_set(v___y_603_, v___x_642_);
v___x_644_ = lean_box(0);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_644_);
v___x_646_ = v___x_609_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_653_, lean_object* v_msg_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_653_, v_msg_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_668_, lean_object* v_mvarId_669_, lean_object* v_fields_670_, lean_object* v_sz_671_, lean_object* v___x_672_, lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
size_t v_sz_boxed_681_; size_t v___x_18122__boxed_682_; uint8_t v___x_18124__boxed_683_; lean_object* v_res_684_; 
v_sz_boxed_681_ = lean_unbox_usize(v_sz_671_);
lean_dec(v_sz_671_);
v___x_18122__boxed_682_ = lean_unbox_usize(v___x_672_);
lean_dec(v___x_672_);
v___x_18124__boxed_683_ = lean_unbox(v___x_674_);
v_res_684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_668_, v_mvarId_669_, v_fields_670_, v_sz_boxed_681_, v___x_18122__boxed_682_, v___x_673_, v___x_18124__boxed_683_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v_fields_670_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_685_, lean_object* v_as_686_, size_t v_sz_687_, size_t v_i_688_, lean_object* v_b_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v___x_696_; 
v___x_696_ = lean_usize_dec_lt(v_i_688_, v_sz_687_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v_b_689_);
return v___x_697_;
}
else
{
lean_object* v_a_698_; lean_object* v_toInductionSubgoal_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v_b_689_);
v_a_698_ = lean_array_uget(v_as_686_, v_i_688_);
v_toInductionSubgoal_699_ = lean_ctor_get(v_a_698_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v_a_698_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_a_698_, 1);
lean_dec(v_unused_741_);
v___x_701_ = v_a_698_;
v_isShared_702_ = v_isSharedCheck_740_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_toInductionSubgoal_699_);
lean_dec(v_a_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_740_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_mvarId_703_; lean_object* v_fields_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; size_t v_sz_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___f_713_; lean_object* v___x_714_; 
v_mvarId_703_ = lean_ctor_get(v_toInductionSubgoal_699_, 0);
lean_inc_n(v_mvarId_703_, 2);
v_fields_704_ = lean_ctor_get(v_toInductionSubgoal_699_, 1);
lean_inc_ref(v_fields_704_);
v___x_705_ = lean_box(0);
v___x_706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_nat_dec_eq(v_val_685_, v___x_707_);
v_sz_709_ = lean_array_size(v_fields_704_);
v___x_710_ = lean_box_usize(v_sz_709_);
v___x_711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_712_ = lean_box(v___x_708_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_713_, 0, v_toInductionSubgoal_699_);
lean_closure_set(v___f_713_, 1, v_mvarId_703_);
lean_closure_set(v___f_713_, 2, v_fields_704_);
lean_closure_set(v___f_713_, 3, v___x_710_);
lean_closure_set(v___f_713_, 4, v___x_711_);
lean_closure_set(v___f_713_, 5, v___x_706_);
lean_closure_set(v___f_713_, 6, v___x_712_);
v___x_714_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_703_, v___f_713_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_731_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_731_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_731_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_731_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
uint8_t v___x_719_; 
v___x_719_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_720_ = lean_box(v___x_708_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_705_);
lean_ctor_set(v___x_701_, 0, v___x_721_);
v___x_723_ = v___x_701_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_705_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_723_);
v___x_725_ = v___x_717_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
size_t v___x_728_; size_t v___x_729_; 
lean_del_object(v___x_717_);
lean_del_object(v___x_701_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_688_, v___x_728_);
v_i_688_ = v___x_729_;
v_b_689_ = v___x_706_;
goto _start;
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_del_object(v___x_701_);
v_a_732_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_714_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_714_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
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
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_753_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_754_ = l_Lean_Name_append(v___x_753_, v___x_752_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_758_, lean_object* v_fvarId_759_, lean_object* v___x_760_, uint8_t v___x_761_, lean_object* v___x_762_, lean_object* v_val_763_, uint8_t v___x_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_MVarId_cases(v_mvarId_758_, v_fvarId_759_, v___x_760_, v___x_761_, v___x_762_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v_options_805_; uint8_t v_hasTrace_806_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref(v___x_771_);
v_options_805_ = lean_ctor_get(v___y_768_, 2);
v_hasTrace_806_ = lean_ctor_get_uint8(v_options_805_, sizeof(void*)*1);
if (v_hasTrace_806_ == 0)
{
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
v___y_776_ = v___y_767_;
v___y_777_ = v___y_768_;
v___y_778_ = v___y_769_;
goto v___jp_773_;
}
else
{
lean_object* v_inheritedTraceOptions_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_inheritedTraceOptions_807_ = lean_ctor_get(v___y_768_, 13);
v___x_808_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_809_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_810_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_807_, v_options_805_, v___x_809_);
if (v___x_810_ == 0)
{
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
v___y_776_ = v___y_767_;
v___y_777_ = v___y_768_;
v___y_778_ = v___y_769_;
goto v___jp_773_;
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_811_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_812_ = lean_array_get_size(v_a_772_);
v___x_813_ = l_Nat_reprFast(v___x_812_);
v___x_814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = l_Lean_MessageData_ofFormat(v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_811_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_808_, v___x_816_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_dec_ref(v___x_817_);
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
v___y_776_ = v___y_767_;
v___y_777_ = v___y_768_;
v___y_778_ = v___y_769_;
goto v___jp_773_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_a_772_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
v___jp_773_:
{
lean_object* v___x_779_; size_t v_sz_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_780_ = lean_array_size(v_a_772_);
v___x_781_ = ((size_t)0ULL);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_763_, v_a_772_, v_sz_780_, v___x_781_, v___x_779_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v_a_772_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_796_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_796_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_796_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_796_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_fst_787_; 
v_fst_787_ = lean_ctor_get(v_a_783_, 0);
lean_inc(v_fst_787_);
lean_dec(v_a_783_);
if (lean_obj_tag(v_fst_787_) == 0)
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_box(v___x_764_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_788_);
v___x_790_ = v___x_785_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
else
{
lean_object* v_val_792_; lean_object* v___x_794_; 
v_val_792_ = lean_ctor_get(v_fst_787_, 0);
lean_inc(v_val_792_);
lean_dec_ref(v_fst_787_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_val_792_);
v___x_794_ = v___x_785_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_val_792_);
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
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_782_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_782_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_870_; 
v_a_826_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_870_ == 0)
{
v___x_828_ = v___x_771_;
v_isShared_829_ = v_isSharedCheck_870_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_771_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_870_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
uint8_t v___y_831_; uint8_t v___x_868_; 
v___x_868_ = l_Lean_Exception_isInterrupt(v_a_826_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
lean_inc(v_a_826_);
v___x_869_ = l_Lean_Exception_isRuntime(v_a_826_);
v___y_831_ = v___x_869_;
goto v___jp_830_;
}
else
{
v___y_831_ = v___x_868_;
goto v___jp_830_;
}
v___jp_830_:
{
if (v___y_831_ == 0)
{
lean_object* v_options_832_; uint8_t v_hasTrace_833_; 
v_options_832_ = lean_ctor_get(v___y_768_, 2);
v_hasTrace_833_ = lean_ctor_get_uint8(v_options_832_, sizeof(void*)*1);
if (v_hasTrace_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_dec(v_a_826_);
v___x_834_ = lean_box(v___x_761_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_834_);
v___x_836_ = v___x_828_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v_inheritedTraceOptions_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_inheritedTraceOptions_838_ = lean_ctor_get(v___y_768_, 13);
v___x_839_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_840_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_841_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_838_, v_options_832_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_dec(v_a_826_);
v___x_842_ = lean_box(v___x_761_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_842_);
v___x_844_ = v___x_828_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_del_object(v___x_828_);
v___x_846_ = l_Lean_Exception_toMessageData(v_a_826_);
v___x_847_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_839_, v___x_846_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v___x_847_, 0);
lean_dec(v_unused_856_);
v___x_849_ = v___x_847_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_dec(v___x_847_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_box(v___x_761_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_a_857_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_847_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_847_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
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
else
{
lean_object* v___x_866_; 
if (v_isShared_829_ == 0)
{
v___x_866_ = v___x_828_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_826_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_871_, lean_object* v_fvarId_872_, lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v___x_875_, lean_object* v_val_876_, lean_object* v___x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v___x_18244__boxed_884_; uint8_t v___x_18247__boxed_885_; lean_object* v_res_886_; 
v___x_18244__boxed_884_ = lean_unbox(v___x_874_);
v___x_18247__boxed_885_ = lean_unbox(v___x_877_);
v_res_886_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_871_, v_fvarId_872_, v___x_873_, v___x_18244__boxed_884_, v___x_875_, v_val_876_, v___x_18247__boxed_885_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec(v_val_876_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_890_, lean_object* v_fvarId_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_st_ref_get(v_a_892_);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_nat_dec_eq(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___f_914_; lean_object* v___x_915_; 
v___x_905_ = lean_st_ref_take(v_a_892_);
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_nat_sub(v___x_905_, v___x_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_st_ref_set(v_a_892_, v___x_907_);
v___x_909_ = 1;
v___x_910_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_911_ = lean_box(0);
v___x_912_ = lean_box(v___x_904_);
v___x_913_ = lean_box(v___x_909_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_914_, 0, v_mvarId_890_);
lean_closure_set(v___f_914_, 1, v_fvarId_891_);
lean_closure_set(v___f_914_, 2, v___x_910_);
lean_closure_set(v___f_914_, 3, v___x_912_);
lean_closure_set(v___f_914_, 4, v___x_911_);
lean_closure_set(v___f_914_, 5, v___x_902_);
lean_closure_set(v___f_914_, 6, v___x_913_);
v___x_915_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_914_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
return v___x_915_;
}
else
{
lean_object* v_options_916_; uint8_t v_hasTrace_917_; 
lean_dec(v___x_902_);
lean_dec(v_fvarId_891_);
lean_dec(v_mvarId_890_);
v_options_916_ = lean_ctor_get(v_a_895_, 2);
v_hasTrace_917_ = lean_ctor_get_uint8(v_options_916_, sizeof(void*)*1);
if (v_hasTrace_917_ == 0)
{
goto v___jp_898_;
}
else
{
lean_object* v_inheritedTraceOptions_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_inheritedTraceOptions_918_ = lean_ctor_get(v_a_895_, 13);
v___x_919_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_920_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_921_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_918_, v_options_916_, v___x_920_);
if (v___x_921_ == 0)
{
goto v___jp_898_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_923_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_919_, v___x_922_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_dec_ref(v___x_923_);
goto v___jp_898_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
v___jp_898_:
{
uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = 0;
v___x_900_ = lean_box(v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_932_, lean_object* v___x_933_, lean_object* v_as_934_, size_t v_sz_935_, size_t v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_a_945_; uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_lt(v_i_936_, v_sz_935_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_b_937_);
return v___x_950_;
}
else
{
lean_object* v_subst_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_a_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
lean_dec_ref(v_b_937_);
v_subst_951_ = lean_ctor_get(v___x_932_, 2);
v___x_952_ = lean_box(0);
v___x_953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_954_ = lean_array_uget_borrowed(v_as_934_, v_i_936_);
lean_inc(v_subst_951_);
v___x_955_ = l_Lean_Meta_FVarSubst_apply(v_subst_951_, v_a_954_);
v___x_956_ = l_Lean_Expr_isFVar(v___x_955_);
if (v___x_956_ == 0)
{
lean_dec_ref(v___x_955_);
v_a_945_ = v___x_953_;
goto v___jp_944_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = l_Lean_Expr_fvarId_x21(v___x_955_);
lean_dec_ref(v___x_955_);
lean_inc(v___x_957_);
v___x_958_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_957_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; uint8_t v___x_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_958_);
v___x_960_ = lean_unbox(v_a_959_);
lean_dec(v_a_959_);
if (v___x_960_ == 0)
{
lean_dec(v___x_957_);
v_a_945_ = v___x_953_;
goto v___jp_944_;
}
else
{
lean_object* v___x_961_; 
lean_inc(v___x_933_);
v___x_961_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_933_, v___x_957_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_972_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_972_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_972_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_972_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
uint8_t v___x_966_; 
v___x_966_ = lean_unbox(v_a_962_);
if (v___x_966_ == 0)
{
lean_del_object(v___x_964_);
lean_dec(v_a_962_);
v_a_945_ = v___x_953_;
goto v___jp_944_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v_a_962_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_952_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_968_);
v___x_970_ = v___x_964_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
v_a_973_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_961_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_961_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v___x_957_);
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
v_a_981_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_958_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_958_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
v___jp_944_:
{
size_t v___x_946_; size_t v___x_947_; 
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_add(v_i_936_, v___x_946_);
lean_inc_ref(v_a_945_);
v_i_936_ = v___x_947_;
v_b_937_ = v_a_945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_989_, lean_object* v_mvarId_990_, lean_object* v_fields_991_, size_t v_sz_992_, size_t v___x_993_, lean_object* v___x_994_, uint8_t v___x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_989_, v_mvarId_990_, v_fields_991_, v_sz_992_, v___x_993_, v___x_994_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1016_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1016_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1016_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_fst_1007_; 
v_fst_1007_ = lean_ctor_get(v_a_1003_, 0);
lean_inc(v_fst_1007_);
lean_dec(v_a_1003_);
if (lean_obj_tag(v_fst_1007_) == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(v___x_995_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1008_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1014_; 
v_val_1012_ = lean_ctor_get(v_fst_1007_, 0);
lean_inc(v_val_1012_);
lean_dec_ref(v_fst_1007_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_val_1012_);
v___x_1014_ = v___x_1005_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_val_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1002_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1002_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1025_, lean_object* v_as_1026_, lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
size_t v_sz_boxed_1036_; size_t v_i_boxed_1037_; lean_object* v_res_1038_; 
v_sz_boxed_1036_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1037_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1025_, v_as_1026_, v_sz_boxed_1036_, v_i_boxed_1037_, v_b_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v_as_1026_);
lean_dec(v_val_1025_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
size_t v_sz_boxed_1051_; size_t v_i_boxed_1052_; lean_object* v_res_1053_; 
v_sz_boxed_1051_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1052_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1039_, v___x_1040_, v_as_1041_, v_sz_boxed_1051_, v_i_boxed_1052_, v_b_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v_as_1041_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1054_, lean_object* v_fvarId_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1054_, v_fvarId_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1063_, v_msg_1064_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1072_, lean_object* v_msg_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1072_, v_msg_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Meta_saveState___redArg(v___y_1083_, v___y_1085_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___y_1090_; lean_object* v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1111_; lean_object* v_a_1112_; lean_object* v___x_1115_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref(v___x_1087_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
v___x_1115_ = lean_apply_5(v_x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, lean_box(0));
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; uint8_t v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
v___x_1117_ = lean_unbox(v_a_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v___x_1115_);
v___x_1118_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1088_, v___y_1083_, v___y_1085_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_a_1088_);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1126_);
v___x_1120_ = v___x_1118_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v___x_1118_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v_a_1116_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1116_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1116_);
v_a_1127_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1118_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1118_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
lean_inc(v_a_1127_);
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
v___y_1111_ = v___x_1132_;
v_a_1112_ = v_a_1127_;
goto v___jp_1110_;
}
}
}
}
else
{
lean_dec(v_a_1116_);
lean_dec(v_a_1088_);
return v___x_1115_;
}
}
else
{
lean_object* v_a_1135_; 
v_a_1135_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1135_);
v___y_1111_ = v___x_1115_;
v_a_1112_ = v_a_1135_;
goto v___jp_1110_;
}
v___jp_1089_:
{
if (v___y_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec_ref(v___y_1090_);
v___x_1093_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1088_, v___y_1083_, v___y_1085_);
lean_dec(v_a_1088_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1101_);
v___x_1095_ = v___x_1093_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v___x_1093_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 1);
lean_ctor_set(v___x_1095_, 0, v___y_1091_);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___y_1091_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v___y_1091_);
v_a_1102_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1093_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1093_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_dec_ref(v___y_1091_);
lean_dec(v_a_1088_);
return v___y_1090_;
}
}
v___jp_1110_:
{
uint8_t v___x_1113_; 
v___x_1113_ = l_Lean_Exception_isInterrupt(v_a_1112_);
if (v___x_1113_ == 0)
{
uint8_t v___x_1114_; 
lean_inc_ref(v_a_1112_);
v___x_1114_ = l_Lean_Exception_isRuntime(v_a_1112_);
v___y_1090_ = v___y_1111_;
v___y_1091_ = v_a_1112_;
v___y_1092_ = v___x_1114_;
goto v___jp_1089_;
}
else
{
v___y_1090_ = v___y_1111_;
v___y_1091_ = v_a_1112_;
v___y_1092_ = v___x_1113_;
goto v___jp_1089_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v_x_1081_);
v_a_1136_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1087_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1087_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1151_, lean_object* v_x_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1151_, v_x_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
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
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1158_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1175_, v_x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1183_, lean_object* v_mvarId_1184_, lean_object* v_x_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1184_, v_x_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_mvarId_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1192_, v_mvarId_1193_, v_x_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1201_, lean_object* v_fuel_1202_, lean_object* v_fvarId_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_MVarId_exfalso(v_mvarId_1201_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = lean_st_mk_ref(v_fuel_1202_);
v___x_1212_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1210_, v_fvarId_1203_, v___x_1211_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_st_ref_get(v___x_1211_);
lean_dec(v___x_1211_);
lean_dec(v___x_1217_);
if (v_isShared_1216_ == 0)
{
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1213_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_dec(v___x_1211_);
return v___x_1212_;
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_fvarId_1203_);
lean_dec(v_fuel_1202_);
v_a_1222_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1209_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1209_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1230_, lean_object* v_fuel_1231_, lean_object* v_fvarId_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1230_, v_fuel_1231_, v_fvarId_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1239_, lean_object* v___f_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1239_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; uint8_t v___x_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
v___x_1248_ = lean_unbox(v_a_1247_);
lean_dec(v_a_1247_);
if (v___x_1248_ == 0)
{
lean_dec_ref(v___f_1240_);
return v___x_1246_;
}
else
{
lean_object* v___x_1249_; 
lean_dec_ref(v___x_1246_);
v___x_1249_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1249_;
}
}
else
{
lean_dec_ref(v___f_1240_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1250_, lean_object* v___f_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1250_, v___f_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1258_, lean_object* v_fvarId_1259_, lean_object* v_fuel_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; 
lean_inc(v_fvarId_1259_);
lean_inc(v_mvarId_1258_);
v___f_1266_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1266_, 0, v_mvarId_1258_);
lean_closure_set(v___f_1266_, 1, v_fuel_1260_);
lean_closure_set(v___f_1266_, 2, v_fvarId_1259_);
v___f_1267_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1267_, 0, v_fvarId_1259_);
lean_closure_set(v___f_1267_, 1, v___f_1266_);
v___x_1268_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1258_, v___f_1267_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1269_, lean_object* v_fvarId_1270_, lean_object* v_fuel_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1269_, v_fvarId_1270_, v_fuel_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
return v_res_1277_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1278_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1280_){
_start:
{
uint8_t v_res_1281_; lean_object* v_r_1282_; 
v_res_1281_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1280_);
v_r_1282_ = lean_box(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1283_, lean_object* v_acc_1284_){
_start:
{
if (lean_obj_tag(v_e_1283_) == 7)
{
lean_object* v_binderType_1285_; lean_object* v_body_1286_; uint8_t v___y_1288_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_binderType_1285_ = lean_ctor_get(v_e_1283_, 1);
v_body_1286_ = lean_ctor_get(v_e_1283_, 2);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_expr_has_loose_bvar(v_body_1286_, v___x_1292_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Expr_isEq(v_binderType_1285_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Expr_isHEq(v_binderType_1285_);
v___y_1288_ = v___x_1295_;
goto v___jp_1287_;
}
else
{
v___y_1288_ = v___x_1294_;
goto v___jp_1287_;
}
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = 0;
v___y_1288_ = v___x_1296_;
goto v___jp_1287_;
}
v___jp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_box(v___y_1288_);
v___x_1290_ = lean_array_push(v_acc_1284_, v___x_1289_);
v_e_1283_ = v_body_1286_;
v_acc_1284_ = v___x_1290_;
goto _start;
}
}
else
{
return v_acc_1284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1297_, lean_object* v_acc_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1297_, v_acc_1298_);
lean_dec_ref(v_e_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1302_){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1304_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1302_, v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Meta_mkGenDiseqMask(v_e_1305_);
lean_dec_ref(v_e_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___f_1314_; lean_object* v___x_5509__overap_1315_; lean_object* v___x_1316_; 
v___f_1314_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_5509__overap_1315_ = lean_panic_fn_borrowed(v___f_1314_, v_msg_1308_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
v___x_1316_ = lean_apply_5(v___x_5509__overap_1315_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, lean_box(0));
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = l_Lean_Expr_hasMVar(v_e_1324_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_e_1324_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; lean_object* v_mctx_1330_; lean_object* v___x_1331_; lean_object* v_fst_1332_; lean_object* v_snd_1333_; lean_object* v___x_1334_; lean_object* v_cache_1335_; lean_object* v_zetaDeltaFVarIds_1336_; lean_object* v_postponed_1337_; lean_object* v_diag_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1347_; 
v___x_1329_ = lean_st_ref_get(v___y_1325_);
v_mctx_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc_ref(v_mctx_1330_);
lean_dec(v___x_1329_);
v___x_1331_ = l_Lean_instantiateMVarsCore(v_mctx_1330_, v_e_1324_);
v_fst_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_fst_1332_);
v_snd_1333_ = lean_ctor_get(v___x_1331_, 1);
lean_inc(v_snd_1333_);
lean_dec_ref(v___x_1331_);
v___x_1334_ = lean_st_ref_take(v___y_1325_);
v_cache_1335_ = lean_ctor_get(v___x_1334_, 1);
v_zetaDeltaFVarIds_1336_ = lean_ctor_get(v___x_1334_, 2);
v_postponed_1337_ = lean_ctor_get(v___x_1334_, 3);
v_diag_1338_ = lean_ctor_get(v___x_1334_, 4);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1334_, 0);
lean_dec(v_unused_1348_);
v___x_1340_ = v___x_1334_;
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_diag_1338_);
lean_inc(v_postponed_1337_);
lean_inc(v_zetaDeltaFVarIds_1336_);
lean_inc(v_cache_1335_);
lean_dec(v___x_1334_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_snd_1333_);
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_snd_1333_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_cache_1335_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_zetaDeltaFVarIds_1336_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_postponed_1337_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_diag_1338_);
v___x_1343_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_st_ref_set(v___y_1325_, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v_fst_1332_);
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1349_, v___y_1350_);
lean_dec(v___y_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1353_, v___y_1355_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1367_, uint8_t v_allowLevelAssignments_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1368_, v_k_1367_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
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
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_a_1383_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1374_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1374_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1391_, lean_object* v_allowLevelAssignments_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1398_; lean_object* v_res_1399_; 
v_allowLevelAssignments_boxed_1398_ = lean_unbox(v_allowLevelAssignments_1392_);
v_res_1399_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1391_, v_allowLevelAssignments_boxed_1398_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1400_, lean_object* v_k_1401_, uint8_t v_allowLevelAssignments_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1401_, v_allowLevelAssignments_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_k_1410_, lean_object* v_allowLevelAssignments_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1417_; lean_object* v_res_1418_; 
v_allowLevelAssignments_boxed_1417_ = lean_unbox(v_allowLevelAssignments_1411_);
v_res_1418_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1409_, v_k_1410_, v_allowLevelAssignments_boxed_1417_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1421_, size_t v_sz_1422_, size_t v_i_1423_, lean_object* v_b_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_a_1431_; uint8_t v___x_1435_; 
v___x_1435_ = lean_usize_dec_lt(v_i_1423_, v_sz_1422_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_b_1424_);
return v___x_1436_;
}
else
{
lean_object* v_snd_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1599_; 
v_snd_1437_ = lean_ctor_get(v_b_1424_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_b_1424_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v_b_1424_, 0);
lean_dec(v_unused_1600_);
v___x_1439_ = v_b_1424_;
v_isShared_1440_ = v_isSharedCheck_1599_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_snd_1437_);
lean_dec(v_b_1424_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1599_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_array_1441_; lean_object* v_start_1442_; lean_object* v_stop_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_array_1441_ = lean_ctor_get(v_snd_1437_, 0);
v_start_1442_ = lean_ctor_get(v_snd_1437_, 1);
v_stop_1443_ = lean_ctor_get(v_snd_1437_, 2);
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_nat_dec_lt(v_start_1442_, v_stop_1443_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1447_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1447_ = v___x_1439_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_snd_1437_);
v___x_1447_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
else
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1595_; 
lean_inc(v_stop_1443_);
lean_inc(v_start_1442_);
lean_inc_ref(v_array_1441_);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_snd_1437_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; lean_object* v_unused_1597_; lean_object* v_unused_1598_; 
v_unused_1596_ = lean_ctor_get(v_snd_1437_, 2);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_snd_1437_, 1);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_snd_1437_, 0);
lean_dec(v_unused_1598_);
v___x_1451_ = v_snd_1437_;
v_isShared_1452_ = v_isSharedCheck_1595_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v_snd_1437_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1595_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1453_ = lean_array_fget(v_array_1441_, v_start_1442_);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = lean_nat_add(v_start_1442_, v___x_1454_);
lean_dec(v_start_1442_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1455_);
v___x_1457_ = v___x_1451_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_array_1441_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_stop_1443_);
v___x_1457_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
uint8_t v___x_1458_; 
v___x_1458_ = lean_unbox(v___x_1453_);
lean_dec(v___x_1453_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1460_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1457_);
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1460_ = v___x_1439_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1457_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
v_a_1431_ = v___x_1460_;
goto v___jp_1430_;
}
}
else
{
lean_object* v_a_1462_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___x_1534_; 
v_a_1462_ = lean_array_uget_borrowed(v_as_1421_, v_i_1423_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v_a_1462_);
v___x_1534_ = lean_infer_type(v_a_1462_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1536_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = l_Lean_Meta_matchEq_x3f(v_a_1535_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___x_1536_);
if (lean_obj_tag(v_a_1537_) == 1)
{
lean_object* v_val_1538_; lean_object* v_snd_1539_; lean_object* v_fst_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1576_; 
v_val_1538_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_val_1538_);
lean_dec_ref(v_a_1537_);
v_snd_1539_ = lean_ctor_get(v_val_1538_, 1);
lean_inc(v_snd_1539_);
lean_dec(v_val_1538_);
v_fst_1540_ = lean_ctor_get(v_snd_1539_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_snd_1539_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v_snd_1539_, 1);
lean_dec(v_unused_1577_);
v___x_1542_ = v_snd_1539_;
v_isShared_1543_ = v_isSharedCheck_1576_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_fst_1540_);
lean_dec(v_snd_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1576_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Meta_mkEqRefl(v_fst_1540_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
lean_inc(v_a_1462_);
v___x_1546_ = l_Lean_Meta_isExprDefEq(v_a_1462_, v_a_1545_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1559_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1559_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1559_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_unbox(v_a_1547_);
lean_dec(v_a_1547_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_del_object(v___x_1439_);
v___x_1552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v___x_1457_);
lean_ctor_set(v___x_1542_, 0, v___x_1552_);
v___x_1554_ = v___x_1542_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1457_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1554_);
v___x_1556_ = v___x_1549_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
lean_del_object(v___x_1549_);
lean_del_object(v___x_1542_);
v___y_1464_ = v___y_1425_;
v___y_1465_ = v___y_1426_;
v___y_1466_ = v___y_1427_;
v___y_1467_ = v___y_1428_;
goto v___jp_1463_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1542_);
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1560_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1546_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1546_);
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
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_del_object(v___x_1542_);
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1568_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1544_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1544_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
else
{
lean_dec(v_a_1537_);
v___y_1464_ = v___y_1425_;
v___y_1465_ = v___y_1426_;
v___y_1466_ = v___y_1427_;
v___y_1467_ = v___y_1428_;
goto v___jp_1463_;
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1578_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1536_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1536_);
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
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1586_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1534_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1534_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
v___jp_1463_:
{
lean_object* v___x_1468_; 
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v_a_1462_);
v___x_1468_ = lean_infer_type(v_a_1462_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = l_Lean_Meta_matchHEq_x3f(v_a_1469_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref(v___x_1470_);
if (lean_obj_tag(v_a_1471_) == 1)
{
lean_object* v_val_1472_; lean_object* v_snd_1473_; lean_object* v_fst_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1513_; 
lean_del_object(v___x_1439_);
v_val_1472_ = lean_ctor_get(v_a_1471_, 0);
lean_inc(v_val_1472_);
lean_dec_ref(v_a_1471_);
v_snd_1473_ = lean_ctor_get(v_val_1472_, 1);
lean_inc(v_snd_1473_);
lean_dec(v_val_1472_);
v_fst_1474_ = lean_ctor_get(v_snd_1473_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_snd_1473_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v_snd_1473_, 1);
lean_dec(v_unused_1514_);
v___x_1476_ = v_snd_1473_;
v_isShared_1477_ = v_isSharedCheck_1513_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_fst_1474_);
lean_dec(v_snd_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1513_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Meta_mkHEqRefl(v_fst_1474_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
lean_inc(v_a_1462_);
v___x_1480_ = l_Lean_Meta_isExprDefEq(v_a_1462_, v_a_1479_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1496_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1496_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1496_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_unbox(v_a_1481_);
lean_dec(v_a_1481_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v___x_1457_);
lean_ctor_set(v___x_1476_, 0, v___x_1486_);
v___x_1488_ = v___x_1476_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1457_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1488_);
v___x_1490_ = v___x_1483_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_object* v___x_1494_; 
lean_del_object(v___x_1483_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v___x_1457_);
lean_ctor_set(v___x_1476_, 0, v___x_1444_);
v___x_1494_ = v___x_1476_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___x_1457_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
v_a_1431_ = v___x_1494_;
goto v___jp_1430_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_del_object(v___x_1476_);
lean_dec_ref(v___x_1457_);
v_a_1497_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1480_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1480_);
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
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_del_object(v___x_1476_);
lean_dec_ref(v___x_1457_);
v_a_1505_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1478_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1478_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
lean_object* v___x_1516_; 
lean_dec(v_a_1471_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1457_);
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1516_ = v___x_1439_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1457_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
v_a_1431_ = v___x_1516_;
goto v___jp_1430_;
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1518_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1470_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1470_);
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
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1526_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1468_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1468_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
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
v___jp_1430_:
{
size_t v___x_1432_; size_t v___x_1433_; 
v___x_1432_ = ((size_t)1ULL);
v___x_1433_ = lean_usize_add(v_i_1423_, v___x_1432_);
v_i_1423_ = v___x_1433_;
v_b_1424_ = v_a_1431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1601_, lean_object* v_sz_1602_, lean_object* v_i_1603_, lean_object* v_b_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
size_t v_sz_boxed_1610_; size_t v_i_boxed_1611_; lean_object* v_res_1612_; 
v_sz_boxed_1610_ = lean_unbox_usize(v_sz_1602_);
lean_dec(v_sz_1602_);
v_i_boxed_1611_ = lean_unbox_usize(v_i_1603_);
lean_dec(v_i_1603_);
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1601_, v_sz_boxed_1610_, v_i_boxed_1611_, v_b_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v_as_1601_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1613_, uint8_t v___x_1614_, lean_object* v_localDecl_1615_, lean_object* v_mvarId_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
lean_inc_ref(v___x_1613_);
v___x_1622_ = l_Lean_Meta_forallMetaTelescope(v___x_1613_, v___x_1614_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v_fst_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1713_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref(v___x_1622_);
v_fst_1624_ = lean_ctor_get(v_a_1623_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_a_1623_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; 
v_unused_1714_ = lean_ctor_get(v_a_1623_, 1);
lean_dec(v_unused_1714_);
v___x_1626_ = v_a_1623_;
v_isShared_1627_ = v_isSharedCheck_1713_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_fst_1624_);
lean_dec(v_a_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1713_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1628_ = l_Lean_Meta_mkGenDiseqMask(v___x_1613_);
lean_dec_ref(v___x_1613_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_array_get_size(v___x_1628_);
v___x_1631_ = l_Array_toSubarray___redArg(v___x_1628_, v___x_1629_, v___x_1630_);
v___x_1632_ = lean_box(0);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 1, v___x_1631_);
lean_ctor_set(v___x_1626_, 0, v___x_1632_);
v___x_1634_ = v___x_1626_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1631_);
v___x_1634_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
size_t v_sz_1635_; size_t v___x_1636_; lean_object* v___x_1637_; 
v_sz_1635_ = lean_array_size(v_fst_1624_);
v___x_1636_ = ((size_t)0ULL);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1624_, v_sz_1635_, v___x_1636_, v___x_1634_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1703_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1703_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1703_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_fst_1642_; 
v_fst_1642_ = lean_ctor_get(v_a_1638_, 0);
lean_inc(v_fst_1642_);
lean_dec(v_a_1638_);
if (lean_obj_tag(v_fst_1642_) == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1698_; 
lean_del_object(v___x_1640_);
v___x_1643_ = l_Lean_LocalDecl_toExpr(v_localDecl_1615_);
v___x_1644_ = l_Lean_mkAppN(v___x_1643_, v_fst_1624_);
lean_dec(v_fst_1624_);
v___x_1645_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1644_, v___y_1618_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1698_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1698_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; 
lean_inc(v_a_1646_);
v___x_1650_ = l_Lean_Meta_hasAssignableMVar(v_a_1646_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1689_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1689_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1689_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_unbox(v_a_1651_);
lean_dec(v_a_1651_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_del_object(v___x_1653_);
v___x_1656_ = l_Lean_MVarId_getType(v_mvarId_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
v___x_1658_ = l_Lean_Meta_mkFalseElim(v_a_1657_, v_a_1646_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1669_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 1);
lean_ctor_set(v___x_1648_, 0, v_a_1659_);
v___x_1664_ = v___x_1648_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1664_);
v___x_1666_ = v___x_1661_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1648_);
v_a_1670_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1658_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1658_);
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
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_del_object(v___x_1648_);
lean_dec(v_a_1646_);
v_a_1678_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1656_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1656_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
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
lean_object* v___x_1687_; 
lean_del_object(v___x_1648_);
lean_dec(v_a_1646_);
lean_dec(v_mvarId_1616_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1632_);
v___x_1687_ = v___x_1653_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1632_);
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
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_del_object(v___x_1648_);
lean_dec(v_a_1646_);
lean_dec(v_mvarId_1616_);
v_a_1690_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1650_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1650_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
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
}
else
{
lean_object* v_val_1699_; lean_object* v___x_1701_; 
lean_dec(v_fst_1624_);
lean_dec(v_mvarId_1616_);
lean_dec_ref(v_localDecl_1615_);
v_val_1699_ = lean_ctor_get(v_fst_1642_, 0);
lean_inc(v_val_1699_);
lean_dec_ref(v_fst_1642_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v_val_1699_);
v___x_1701_ = v___x_1640_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_val_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_fst_1624_);
lean_dec(v_mvarId_1616_);
lean_dec_ref(v_localDecl_1615_);
v_a_1704_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1637_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1637_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_mvarId_1616_);
lean_dec_ref(v_localDecl_1615_);
lean_dec_ref(v___x_1613_);
v_a_1715_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1622_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1622_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1723_, lean_object* v___x_1724_, lean_object* v_localDecl_1725_, lean_object* v_mvarId_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_7190__boxed_1732_; lean_object* v_res_1733_; 
v___x_7190__boxed_1732_ = lean_unbox(v___x_1724_);
v_res_1733_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1723_, v___x_7190__boxed_1732_, v_localDecl_1725_, v_mvarId_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v_res_1733_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1738_ = lean_unsigned_to_nat(2u);
v___x_1739_ = lean_unsigned_to_nat(120u);
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1742_ = l_mkPanicMessageWithDecl(v___x_1741_, v___x_1740_, v___x_1739_, v___x_1738_, v___x_1737_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1743_, lean_object* v_localDecl_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = l_Lean_LocalDecl_type(v_localDecl_1744_);
lean_inc_ref(v___x_1750_);
v___x_1751_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref(v___x_1750_);
lean_dec_ref(v_localDecl_1744_);
lean_dec(v_mvarId_1743_);
v___x_1752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1753_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1752_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
return v___x_1753_;
}
else
{
uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___f_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1754_ = 0;
v___x_1755_ = lean_box(v___x_1754_);
lean_inc(v_mvarId_1743_);
v___f_1756_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1756_, 0, v___x_1750_);
lean_closure_set(v___f_1756_, 1, v___x_1755_);
lean_closure_set(v___f_1756_, 2, v_localDecl_1744_);
lean_closure_set(v___f_1756_, 3, v_mvarId_1743_);
v___x_1757_ = 0;
v___x_1758_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1756_, v___x_1757_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1778_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1778_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1778_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
if (lean_obj_tag(v_a_1759_) == 1)
{
lean_object* v_val_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1772_; 
lean_del_object(v___x_1761_);
v_val_1763_ = lean_ctor_get(v_a_1759_, 0);
lean_inc(v_val_1763_);
lean_dec_ref(v_a_1759_);
v___x_1764_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1743_, v_val_1763_, v_a_1746_);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v___x_1764_, 0);
lean_dec(v_unused_1773_);
v___x_1766_ = v___x_1764_;
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v___x_1764_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_box(v___x_1751_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1770_ = v___x_1766_;
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
else
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
lean_dec(v_a_1759_);
lean_dec(v_mvarId_1743_);
v___x_1774_ = lean_box(v___x_1757_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1774_);
v___x_1776_ = v___x_1761_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_mvarId_1743_);
v_a_1779_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1758_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1758_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1787_, lean_object* v_localDecl_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1787_, v_localDecl_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
return v_res_1794_;
}
}
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1(void){
_start:
{
uint8_t v___x_1798_; uint64_t v___x_1799_; 
v___x_1798_ = 1;
v___x_1799_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_box(0);
v___x_1809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6));
v___x_1810_ = l_Lean_mkConst(v___x_1809_, v___x_1808_);
return v___x_1810_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8(void){
_start:
{
lean_object* v___x_1811_; lean_object* v_dummy_1812_; 
v___x_1811_ = lean_box(0);
v_dummy_1812_ = l_Lean_Expr_sort___override(v___x_1811_);
return v_dummy_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1813_, lean_object* v_mvarId_1814_, lean_object* v_as_1815_, size_t v_sz_1816_, size_t v_i_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_lt(v_i_1817_, v_sz_1816_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; 
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_b_1818_);
return v___x_1825_;
}
else
{
lean_object* v_snd_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_2494_; 
v_snd_1826_ = lean_ctor_get(v_b_1818_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_b_1818_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v_b_1818_, 0);
lean_dec(v_unused_2495_);
v___x_1828_ = v_b_1818_;
v_isShared_1829_ = v_isSharedCheck_2494_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_snd_1826_);
lean_dec(v_b_1818_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_2494_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_a_1831_; lean_object* v___x_1837_; lean_object* v_a_1839_; lean_object* v_a_1844_; 
v___x_1837_ = lean_box(0);
v_a_1844_ = lean_array_uget(v_as_1815_, v_i_1817_);
if (lean_obj_tag(v_a_1844_) == 0)
{
lean_del_object(v___x_1828_);
v_a_1839_ = v_snd_1826_;
goto v___jp_1838_;
}
else
{
lean_object* v_val_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_2493_; 
v_val_1845_ = lean_ctor_get(v_a_1844_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_a_1844_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_1847_ = v_a_1844_;
v_isShared_1848_ = v_isSharedCheck_2493_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_val_1845_);
lean_dec(v_a_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_2493_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___x_1890_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; uint8_t v___y_1917_; uint8_t v___x_1918_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; uint8_t v___y_1924_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; uint8_t v___y_1929_; lean_object* v___y_1930_; uint8_t v___y_1931_; uint8_t v___y_1933_; uint8_t v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; uint8_t v___y_1941_; uint8_t v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; uint8_t v___y_1947_; 
v___x_1849_ = lean_box(0);
v___x_1890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1918_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1845_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1962_; uint8_t v___y_1964_; uint8_t v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; uint8_t v___y_1973_; lean_object* v___y_1974_; uint8_t v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; uint8_t v___y_1980_; uint8_t v___y_1983_; lean_object* v___y_1984_; uint8_t v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v_a_1989_; uint8_t v___y_1993_; lean_object* v___y_1994_; uint8_t v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; uint8_t v___y_2084_; lean_object* v___y_2085_; uint8_t v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; uint8_t v___y_2090_; uint8_t v___y_2092_; lean_object* v___y_2093_; uint8_t v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; uint8_t v___y_2099_; uint8_t v___y_2102_; lean_object* v___y_2103_; uint8_t v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; uint8_t v___y_2108_; uint8_t v___y_2121_; lean_object* v___y_2122_; uint8_t v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; uint8_t v___y_2127_; uint8_t v___y_2129_; uint8_t v_isHEq_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2138_; lean_object* v___y_2139_; uint8_t v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; uint8_t v_isEq_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___x_2430_; 
v___x_1962_ = l_Lean_LocalDecl_type(v_val_1845_);
lean_inc_ref(v___x_1962_);
v___x_2430_ = l_Lean_Meta_matchNot_x3f(v___x_1962_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref(v___x_2430_);
if (lean_obj_tag(v_a_2431_) == 1)
{
lean_object* v_val_2432_; lean_object* v___x_2433_; 
v_val_2432_ = lean_ctor_get(v_a_2431_, 0);
lean_inc(v_val_2432_);
lean_dec_ref(v_a_2431_);
v___x_2433_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2432_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref(v___x_2433_);
if (lean_obj_tag(v_a_2434_) == 1)
{
lean_object* v_val_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec_ref(v_config_1813_);
v_val_2435_ = lean_ctor_get(v_a_2434_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_a_2434_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2437_ = v_a_2434_;
v_isShared_2438_ = v_isSharedCheck_2476_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_val_2435_);
lean_dec(v_a_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2476_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; 
lean_inc(v_mvarId_1814_);
v___x_2439_ = l_Lean_MVarId_getType(v_mvarId_1814_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___x_2439_);
v___x_2441_ = l_Lean_LocalDecl_toExpr(v_val_1845_);
v___x_2442_ = l_Lean_mkFVar(v_val_2435_);
v___x_2443_ = l_Lean_Expr_app___override(v___x_2441_, v___x_2442_);
v___x_2444_ = l_Lean_Meta_mkFalseElim(v_a_2440_, v___x_2443_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2446_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref(v___x_2444_);
v___x_2446_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1814_, v_a_2445_, v___y_1820_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
lean_dec_ref(v___x_2446_);
v___x_2447_ = lean_box(v___x_1824_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2447_);
v___x_2449_ = v___x_2437_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
lean_ctor_set(v___x_2450_, 1, v___x_1849_);
v_a_1831_ = v___x_2450_;
goto v___jp_1830_;
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_del_object(v___x_2437_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
v_a_2452_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2446_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2446_);
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
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_del_object(v___x_2437_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2460_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2444_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2444_);
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
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_del_object(v___x_2437_);
lean_dec(v_val_2435_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2468_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2439_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2439_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
else
{
lean_dec(v_a_2434_);
v___y_2296_ = v___y_1819_;
v___y_2297_ = v___y_1820_;
v___y_2298_ = v___y_1821_;
v___y_2299_ = v___y_1822_;
goto v___jp_2295_;
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2477_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2433_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2433_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_dec(v_a_2431_);
v___y_2296_ = v___y_1819_;
v___y_2297_ = v___y_1820_;
v___y_2298_ = v___y_1821_;
v___y_2299_ = v___y_1822_;
goto v___jp_2295_;
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2485_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2430_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2430_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
v___jp_1963_:
{
uint8_t v_genDiseq_1970_; 
v_genDiseq_1970_ = lean_ctor_get_uint8(v_config_1813_, sizeof(void*)*1 + 2);
if (v_genDiseq_1970_ == 0)
{
lean_dec_ref(v___x_1962_);
v___y_1941_ = v___y_1964_;
v___y_1942_ = v___y_1965_;
v___y_1943_ = v___y_1969_;
v___y_1944_ = v___y_1967_;
v___y_1945_ = v___y_1968_;
v___y_1946_ = v___y_1966_;
v___y_1947_ = v___x_1918_;
goto v___jp_1940_;
}
else
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1962_);
v___y_1941_ = v___y_1964_;
v___y_1942_ = v___y_1965_;
v___y_1943_ = v___y_1969_;
v___y_1944_ = v___y_1967_;
v___y_1945_ = v___y_1968_;
v___y_1946_ = v___y_1966_;
v___y_1947_ = v___x_1971_;
goto v___jp_1940_;
}
}
v___jp_1972_:
{
if (v___y_1980_ == 0)
{
lean_dec_ref(v___y_1976_);
v___y_1964_ = v___y_1973_;
v___y_1965_ = v___y_1975_;
v___y_1966_ = v___y_1974_;
v___y_1967_ = v___y_1979_;
v___y_1968_ = v___y_1977_;
v___y_1969_ = v___y_1978_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_1981_; 
lean_dec_ref(v___x_1962_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___y_1976_);
return v___x_1981_;
}
}
v___jp_1982_:
{
uint8_t v___x_1990_; 
v___x_1990_ = l_Lean_Exception_isInterrupt(v_a_1989_);
if (v___x_1990_ == 0)
{
uint8_t v___x_1991_; 
lean_inc_ref(v_a_1989_);
v___x_1991_ = l_Lean_Exception_isRuntime(v_a_1989_);
v___y_1973_ = v___y_1983_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1985_;
v___y_1976_ = v_a_1989_;
v___y_1977_ = v___y_1986_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1987_;
v___y_1980_ = v___x_1991_;
goto v___jp_1972_;
}
else
{
v___y_1973_ = v___y_1983_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1985_;
v___y_1976_ = v_a_1989_;
v___y_1977_ = v___y_1986_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1987_;
v___y_1980_ = v___x_1990_;
goto v___jp_1972_;
}
}
v___jp_1992_:
{
lean_object* v___x_1999_; 
lean_inc_ref(v___x_1962_);
v___x_1999_ = l_Lean_Meta_mkDecide(v___x_1962_, v___y_1994_, v___y_1998_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; uint8_t v_foApprox_2002_; uint8_t v_ctxApprox_2003_; uint8_t v_quasiPatternApprox_2004_; uint8_t v_constApprox_2005_; uint8_t v_isDefEqStuckEx_2006_; uint8_t v_unificationHints_2007_; uint8_t v_proofIrrelevance_2008_; uint8_t v_assignSyntheticOpaque_2009_; uint8_t v_offsetCnstrs_2010_; uint8_t v_etaStruct_2011_; uint8_t v_univApprox_2012_; uint8_t v_iota_2013_; uint8_t v_beta_2014_; uint8_t v_proj_2015_; uint8_t v_zeta_2016_; uint8_t v_zetaDelta_2017_; uint8_t v_zetaUnused_2018_; uint8_t v_zetaHave_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2081_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v___x_1999_);
v___x_2001_ = l_Lean_Meta_Context_config(v___y_1994_);
v_foApprox_2002_ = lean_ctor_get_uint8(v___x_2001_, 0);
v_ctxApprox_2003_ = lean_ctor_get_uint8(v___x_2001_, 1);
v_quasiPatternApprox_2004_ = lean_ctor_get_uint8(v___x_2001_, 2);
v_constApprox_2005_ = lean_ctor_get_uint8(v___x_2001_, 3);
v_isDefEqStuckEx_2006_ = lean_ctor_get_uint8(v___x_2001_, 4);
v_unificationHints_2007_ = lean_ctor_get_uint8(v___x_2001_, 5);
v_proofIrrelevance_2008_ = lean_ctor_get_uint8(v___x_2001_, 6);
v_assignSyntheticOpaque_2009_ = lean_ctor_get_uint8(v___x_2001_, 7);
v_offsetCnstrs_2010_ = lean_ctor_get_uint8(v___x_2001_, 8);
v_etaStruct_2011_ = lean_ctor_get_uint8(v___x_2001_, 10);
v_univApprox_2012_ = lean_ctor_get_uint8(v___x_2001_, 11);
v_iota_2013_ = lean_ctor_get_uint8(v___x_2001_, 12);
v_beta_2014_ = lean_ctor_get_uint8(v___x_2001_, 13);
v_proj_2015_ = lean_ctor_get_uint8(v___x_2001_, 14);
v_zeta_2016_ = lean_ctor_get_uint8(v___x_2001_, 15);
v_zetaDelta_2017_ = lean_ctor_get_uint8(v___x_2001_, 16);
v_zetaUnused_2018_ = lean_ctor_get_uint8(v___x_2001_, 17);
v_zetaHave_2019_ = lean_ctor_get_uint8(v___x_2001_, 18);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2021_ = v___x_2001_;
v_isShared_2022_ = v_isSharedCheck_2081_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v___x_2001_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2081_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
uint8_t v_trackZetaDelta_2023_; lean_object* v_zetaDeltaSet_2024_; lean_object* v_lctx_2025_; lean_object* v_localInstances_2026_; lean_object* v_defEqCtx_x3f_2027_; lean_object* v_synthPendingDepth_2028_; lean_object* v_canUnfold_x3f_2029_; uint8_t v_univApprox_2030_; uint8_t v_inTypeClassResolution_2031_; uint8_t v_cacheInferType_2032_; uint8_t v___x_2033_; lean_object* v_config_2035_; 
v_trackZetaDelta_2023_ = lean_ctor_get_uint8(v___y_1994_, sizeof(void*)*7);
v_zetaDeltaSet_2024_ = lean_ctor_get(v___y_1994_, 1);
v_lctx_2025_ = lean_ctor_get(v___y_1994_, 2);
v_localInstances_2026_ = lean_ctor_get(v___y_1994_, 3);
v_defEqCtx_x3f_2027_ = lean_ctor_get(v___y_1994_, 4);
v_synthPendingDepth_2028_ = lean_ctor_get(v___y_1994_, 5);
v_canUnfold_x3f_2029_ = lean_ctor_get(v___y_1994_, 6);
v_univApprox_2030_ = lean_ctor_get_uint8(v___y_1994_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2031_ = lean_ctor_get_uint8(v___y_1994_, sizeof(void*)*7 + 2);
v_cacheInferType_2032_ = lean_ctor_get_uint8(v___y_1994_, sizeof(void*)*7 + 3);
v___x_2033_ = 1;
if (v_isShared_2022_ == 0)
{
v_config_2035_ = v___x_2021_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 0, v_foApprox_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 1, v_ctxApprox_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 2, v_quasiPatternApprox_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 3, v_constApprox_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 4, v_isDefEqStuckEx_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 5, v_unificationHints_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 6, v_proofIrrelevance_2008_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 7, v_assignSyntheticOpaque_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 8, v_offsetCnstrs_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 10, v_etaStruct_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 11, v_univApprox_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 12, v_iota_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 13, v_beta_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 14, v_proj_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 15, v_zeta_2016_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 16, v_zetaDelta_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 17, v_zetaUnused_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, 18, v_zetaHave_2019_);
v_config_2035_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
uint64_t v___x_2036_; uint64_t v___x_2037_; uint64_t v___x_2038_; uint64_t v___x_2039_; uint64_t v___x_2040_; uint64_t v_key_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_ctor_set_uint8(v_config_2035_, 9, v___x_2033_);
v___x_2036_ = l_Lean_Meta_Context_configKey(v___y_1994_);
v___x_2037_ = 2ULL;
v___x_2038_ = lean_uint64_shift_right(v___x_2036_, v___x_2037_);
v___x_2039_ = lean_uint64_shift_left(v___x_2038_, v___x_2037_);
v___x_2040_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_2041_ = lean_uint64_lor(v___x_2039_, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2042_, 0, v_config_2035_);
lean_ctor_set_uint64(v___x_2042_, sizeof(void*)*1, v_key_2041_);
lean_inc(v_canUnfold_x3f_2029_);
lean_inc(v_synthPendingDepth_2028_);
lean_inc(v_defEqCtx_x3f_2027_);
lean_inc_ref(v_localInstances_2026_);
lean_inc_ref(v_lctx_2025_);
lean_inc(v_zetaDeltaSet_2024_);
v___x_2043_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
lean_ctor_set(v___x_2043_, 1, v_zetaDeltaSet_2024_);
lean_ctor_set(v___x_2043_, 2, v_lctx_2025_);
lean_ctor_set(v___x_2043_, 3, v_localInstances_2026_);
lean_ctor_set(v___x_2043_, 4, v_defEqCtx_x3f_2027_);
lean_ctor_set(v___x_2043_, 5, v_synthPendingDepth_2028_);
lean_ctor_set(v___x_2043_, 6, v_canUnfold_x3f_2029_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*7, v_trackZetaDelta_2023_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*7 + 1, v_univApprox_2030_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2031_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*7 + 3, v_cacheInferType_2032_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
lean_inc(v___y_1998_);
lean_inc(v_a_2000_);
v___x_2044_ = lean_whnf(v_a_2000_, v___x_2043_, v___y_1998_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v___x_2046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_2047_ = l_Lean_Expr_isConstOf(v_a_2045_, v___x_2046_);
lean_dec(v_a_2045_);
if (v___x_2047_ == 0)
{
lean_dec(v_a_2000_);
v___y_1964_ = v___y_1993_;
v___y_1965_ = v___y_1995_;
v___y_1966_ = v___y_1994_;
v___y_1967_ = v___y_1998_;
v___y_1968_ = v___y_1996_;
v___y_1969_ = v___y_1997_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_2048_; 
lean_inc(v_a_2000_);
v___x_2048_ = l_Lean_Meta_mkEqRefl(v_a_2000_, v___y_1994_, v___y_1998_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2048_);
lean_inc(v_mvarId_1814_);
v___x_2050_ = l_Lean_MVarId_getType(v_mvarId_1814_, v___y_1994_, v___y_1998_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v_nargs_2052_; lean_object* v___x_2053_; lean_object* v_dummy_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v_nargs_2052_ = l_Lean_Expr_getAppNumArgs(v_a_2000_);
v___x_2053_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2052_);
v___x_2055_ = lean_mk_array(v_nargs_2052_, v_dummy_2054_);
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = lean_nat_sub(v_nargs_2052_, v___x_2056_);
lean_dec(v_nargs_2052_);
v___x_2058_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2000_, v___x_2055_, v___x_2057_);
v___x_2059_ = lean_array_push(v___x_2058_, v_a_2049_);
v___x_2060_ = l_Lean_mkAppN(v___x_2053_, v___x_2059_);
lean_dec_ref(v___x_2059_);
lean_inc(v_val_1845_);
v___x_2061_ = l_Lean_LocalDecl_toExpr(v_val_1845_);
v___x_2062_ = l_Lean_Meta_mkAbsurd(v_a_2051_, v___x_2061_, v___x_2060_, v___y_1994_, v___y_1998_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref(v___x_2062_);
lean_inc(v_mvarId_1814_);
v___x_2064_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1814_, v_a_2063_, v___y_1998_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v___x_1962_);
lean_dec(v_val_1845_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v___x_2064_, 0);
lean_dec(v_unused_2074_);
v___x_2066_ = v___x_2064_;
v_isShared_2067_ = v_isSharedCheck_2073_;
goto v_resetjp_2065_;
}
else
{
lean_dec(v___x_2064_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2073_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_box(v___x_1824_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 1);
lean_ctor_set(v___x_2066_, 0, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___x_1849_);
v_a_1831_ = v___x_2071_;
goto v___jp_1830_;
}
}
}
else
{
lean_object* v_a_2075_; 
v_a_2075_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2064_);
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1997_;
v_a_1989_ = v_a_2075_;
goto v___jp_1982_;
}
}
else
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2076_);
lean_dec_ref(v___x_2062_);
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1997_;
v_a_1989_ = v_a_2076_;
goto v___jp_1982_;
}
}
else
{
lean_object* v_a_2077_; 
lean_dec(v_a_2049_);
lean_dec(v_a_2000_);
v_a_2077_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2050_);
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1997_;
v_a_1989_ = v_a_2077_;
goto v___jp_1982_;
}
}
else
{
lean_object* v_a_2078_; 
lean_dec(v_a_2000_);
v_a_2078_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2048_);
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1997_;
v_a_1989_ = v_a_2078_;
goto v___jp_1982_;
}
}
}
else
{
lean_object* v_a_2079_; 
lean_dec(v_a_2000_);
v_a_2079_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2079_);
lean_dec_ref(v___x_2044_);
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1997_;
v_a_1989_ = v_a_2079_;
goto v___jp_1982_;
}
}
}
}
else
{
lean_object* v_a_2082_; 
v_a_2082_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_1999_);
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1998_;
v___y_1988_ = v___y_1997_;
v_a_1989_ = v_a_2082_;
goto v___jp_1982_;
}
}
v___jp_2083_:
{
if (v___y_2090_ == 0)
{
v___y_1964_ = v___y_2084_;
v___y_1965_ = v___y_2086_;
v___y_1966_ = v___y_2085_;
v___y_1967_ = v___y_2089_;
v___y_1968_ = v___y_2087_;
v___y_1969_ = v___y_2088_;
goto v___jp_1963_;
}
else
{
v___y_1993_ = v___y_2084_;
v___y_1994_ = v___y_2085_;
v___y_1995_ = v___y_2086_;
v___y_1996_ = v___y_2087_;
v___y_1997_ = v___y_2088_;
v___y_1998_ = v___y_2089_;
goto v___jp_1992_;
}
}
v___jp_2091_:
{
if (v___y_2099_ == 0)
{
lean_dec_ref(v___y_2098_);
v___y_2084_ = v___y_2092_;
v___y_2085_ = v___y_2093_;
v___y_2086_ = v___y_2094_;
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___y_2097_;
v___y_2089_ = v___y_2096_;
v___y_2090_ = v___x_1918_;
goto v___jp_2083_;
}
else
{
uint8_t v___x_2100_; 
v___x_2100_ = l_Lean_Expr_hasFVar(v___y_2098_);
lean_dec_ref(v___y_2098_);
if (v___x_2100_ == 0)
{
v___y_1993_ = v___y_2092_;
v___y_1994_ = v___y_2093_;
v___y_1995_ = v___y_2094_;
v___y_1996_ = v___y_2095_;
v___y_1997_ = v___y_2097_;
v___y_1998_ = v___y_2096_;
goto v___jp_1992_;
}
else
{
v___y_2084_ = v___y_2092_;
v___y_2085_ = v___y_2093_;
v___y_2086_ = v___y_2094_;
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___y_2097_;
v___y_2089_ = v___y_2096_;
v___y_2090_ = v___x_1918_;
goto v___jp_2083_;
}
}
}
v___jp_2101_:
{
lean_object* v___x_2109_; 
lean_inc_ref(v___x_1962_);
v___x_2109_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1962_, v___y_2107_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; uint8_t v___x_2111_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = l_Lean_Expr_hasMVar(v_a_2110_);
if (v___x_2111_ == 0)
{
v___y_2092_ = v___y_2102_;
v___y_2093_ = v___y_2103_;
v___y_2094_ = v___y_2104_;
v___y_2095_ = v___y_2105_;
v___y_2096_ = v___y_2107_;
v___y_2097_ = v___y_2106_;
v___y_2098_ = v_a_2110_;
v___y_2099_ = v___y_2108_;
goto v___jp_2091_;
}
else
{
v___y_2092_ = v___y_2102_;
v___y_2093_ = v___y_2103_;
v___y_2094_ = v___y_2104_;
v___y_2095_ = v___y_2105_;
v___y_2096_ = v___y_2107_;
v___y_2097_ = v___y_2106_;
v___y_2098_ = v_a_2110_;
v___y_2099_ = v___x_1918_;
goto v___jp_2091_;
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v___x_1962_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2112_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2109_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2109_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
v___jp_2120_:
{
if (v___y_2127_ == 0)
{
v___y_1964_ = v___y_2121_;
v___y_1965_ = v___y_2123_;
v___y_1966_ = v___y_2122_;
v___y_1967_ = v___y_2126_;
v___y_1968_ = v___y_2124_;
v___y_1969_ = v___y_2125_;
goto v___jp_1963_;
}
else
{
v___y_2102_ = v___y_2121_;
v___y_2103_ = v___y_2122_;
v___y_2104_ = v___y_2123_;
v___y_2105_ = v___y_2124_;
v___y_2106_ = v___y_2125_;
v___y_2107_ = v___y_2126_;
v___y_2108_ = v___y_2127_;
goto v___jp_2101_;
}
}
v___jp_2128_:
{
uint8_t v_useDecide_2135_; 
v_useDecide_2135_ = lean_ctor_get_uint8(v_config_1813_, sizeof(void*)*1);
if (v_useDecide_2135_ == 0)
{
v___y_2121_ = v___y_2129_;
v___y_2122_ = v___y_2131_;
v___y_2123_ = v_isHEq_2130_;
v___y_2124_ = v___y_2133_;
v___y_2125_ = v___y_2134_;
v___y_2126_ = v___y_2132_;
v___y_2127_ = v___x_1918_;
goto v___jp_2120_;
}
else
{
uint8_t v___x_2136_; 
v___x_2136_ = l_Lean_Expr_hasFVar(v___x_1962_);
if (v___x_2136_ == 0)
{
v___y_2102_ = v___y_2129_;
v___y_2103_ = v___y_2131_;
v___y_2104_ = v_isHEq_2130_;
v___y_2105_ = v___y_2133_;
v___y_2106_ = v___y_2134_;
v___y_2107_ = v___y_2132_;
v___y_2108_ = v_useDecide_2135_;
goto v___jp_2101_;
}
else
{
v___y_2121_ = v___y_2129_;
v___y_2122_ = v___y_2131_;
v___y_2123_ = v_isHEq_2130_;
v___y_2124_ = v___y_2133_;
v___y_2125_ = v___y_2134_;
v___y_2126_ = v___y_2132_;
v___y_2127_ = v___x_1918_;
goto v___jp_2120_;
}
}
}
v___jp_2137_:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_Meta_isExprDefEq(v___y_2144_, v___y_2143_, v___y_2142_, v___y_2139_, v___y_2138_, v___y_2141_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; uint8_t v___x_2147_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref(v___x_2145_);
v___x_2147_ = lean_unbox(v_a_2146_);
lean_dec(v_a_2146_);
if (v___x_2147_ == 0)
{
v___y_2129_ = v___y_2140_;
v_isHEq_2130_ = v___x_1824_;
v___y_2131_ = v___y_2142_;
v___y_2132_ = v___y_2139_;
v___y_2133_ = v___y_2138_;
v___y_2134_ = v___y_2141_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2148_; 
lean_dec_ref(v___x_1962_);
lean_dec_ref(v_config_1813_);
lean_inc(v_mvarId_1814_);
v___x_2148_ = l_Lean_MVarId_getType(v_mvarId_1814_, v___y_2142_, v___y_2139_, v___y_2138_, v___y_2141_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v___x_2150_ = l_Lean_LocalDecl_toExpr(v_val_1845_);
v___x_2151_ = l_Lean_Meta_mkEqOfHEq(v___x_2150_, v___x_1824_, v___y_2142_, v___y_2139_, v___y_2138_, v___y_2141_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref(v___x_2151_);
v___x_2153_ = l_Lean_Meta_mkNoConfusion(v_a_2149_, v_a_2152_, v___y_2142_, v___y_2139_, v___y_2138_, v___y_2141_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2153_);
v___x_2155_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1814_, v_a_2154_, v___y_2139_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref(v___x_2155_);
v___x_2156_ = lean_box(v___x_1824_);
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v___x_1849_);
v_a_1831_ = v___x_2158_;
goto v___jp_1830_;
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
v_a_2159_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2155_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2155_);
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
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2167_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2153_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2153_);
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
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_a_2149_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2175_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2151_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2151_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2183_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2148_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2148_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v___x_1962_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2191_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2145_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2145_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
v___jp_2199_:
{
lean_object* v___x_2205_; 
lean_inc_ref(v___x_1962_);
v___x_2205_ = l_Lean_Meta_matchHEq_x3f(v___x_1962_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref(v___x_2205_);
if (lean_obj_tag(v_a_2206_) == 1)
{
lean_object* v_val_2207_; lean_object* v_snd_2208_; lean_object* v_snd_2209_; lean_object* v_fst_2210_; lean_object* v_fst_2211_; lean_object* v_fst_2212_; lean_object* v_snd_2213_; lean_object* v___x_2214_; 
v_val_2207_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_val_2207_);
lean_dec_ref(v_a_2206_);
v_snd_2208_ = lean_ctor_get(v_val_2207_, 1);
lean_inc(v_snd_2208_);
v_snd_2209_ = lean_ctor_get(v_snd_2208_, 1);
lean_inc(v_snd_2209_);
v_fst_2210_ = lean_ctor_get(v_val_2207_, 0);
lean_inc(v_fst_2210_);
lean_dec(v_val_2207_);
v_fst_2211_ = lean_ctor_get(v_snd_2208_, 0);
lean_inc(v_fst_2211_);
lean_dec(v_snd_2208_);
v_fst_2212_ = lean_ctor_get(v_snd_2209_, 0);
lean_inc(v_fst_2212_);
v_snd_2213_ = lean_ctor_get(v_snd_2209_, 1);
lean_inc(v_snd_2213_);
lean_dec(v_snd_2209_);
v___x_2214_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2211_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref(v___x_2214_);
if (lean_obj_tag(v_a_2215_) == 1)
{
lean_object* v_val_2216_; lean_object* v___x_2217_; 
v_val_2216_ = lean_ctor_get(v_a_2215_, 0);
lean_inc(v_val_2216_);
lean_dec_ref(v_a_2215_);
v___x_2217_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2213_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref(v___x_2217_);
if (lean_obj_tag(v_a_2218_) == 1)
{
lean_object* v_toConstantVal_2219_; lean_object* v_val_2220_; lean_object* v_toConstantVal_2221_; lean_object* v_name_2222_; lean_object* v_name_2223_; uint8_t v___x_2224_; 
v_toConstantVal_2219_ = lean_ctor_get(v_val_2216_, 0);
lean_inc_ref(v_toConstantVal_2219_);
lean_dec(v_val_2216_);
v_val_2220_ = lean_ctor_get(v_a_2218_, 0);
lean_inc(v_val_2220_);
lean_dec_ref(v_a_2218_);
v_toConstantVal_2221_ = lean_ctor_get(v_val_2220_, 0);
lean_inc_ref(v_toConstantVal_2221_);
lean_dec(v_val_2220_);
v_name_2222_ = lean_ctor_get(v_toConstantVal_2219_, 0);
lean_inc(v_name_2222_);
lean_dec_ref(v_toConstantVal_2219_);
v_name_2223_ = lean_ctor_get(v_toConstantVal_2221_, 0);
lean_inc(v_name_2223_);
lean_dec_ref(v_toConstantVal_2221_);
v___x_2224_ = lean_name_eq(v_name_2222_, v_name_2223_);
lean_dec(v_name_2223_);
lean_dec(v_name_2222_);
if (v___x_2224_ == 0)
{
v___y_2138_ = v___y_2203_;
v___y_2139_ = v___y_2202_;
v___y_2140_ = v_isEq_2200_;
v___y_2141_ = v___y_2204_;
v___y_2142_ = v___y_2201_;
v___y_2143_ = v_fst_2212_;
v___y_2144_ = v_fst_2210_;
goto v___jp_2137_;
}
else
{
if (v___x_1918_ == 0)
{
lean_dec(v_fst_2212_);
lean_dec(v_fst_2210_);
v___y_2129_ = v_isEq_2200_;
v_isHEq_2130_ = v___x_1824_;
v___y_2131_ = v___y_2201_;
v___y_2132_ = v___y_2202_;
v___y_2133_ = v___y_2203_;
v___y_2134_ = v___y_2204_;
goto v___jp_2128_;
}
else
{
v___y_2138_ = v___y_2203_;
v___y_2139_ = v___y_2202_;
v___y_2140_ = v_isEq_2200_;
v___y_2141_ = v___y_2204_;
v___y_2142_ = v___y_2201_;
v___y_2143_ = v_fst_2212_;
v___y_2144_ = v_fst_2210_;
goto v___jp_2137_;
}
}
}
else
{
lean_dec(v_a_2218_);
lean_dec(v_val_2216_);
lean_dec(v_fst_2212_);
lean_dec(v_fst_2210_);
v___y_2129_ = v_isEq_2200_;
v_isHEq_2130_ = v___x_1824_;
v___y_2131_ = v___y_2201_;
v___y_2132_ = v___y_2202_;
v___y_2133_ = v___y_2203_;
v___y_2134_ = v___y_2204_;
goto v___jp_2128_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_val_2216_);
lean_dec(v_fst_2212_);
lean_dec(v_fst_2210_);
lean_dec_ref(v___x_1962_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2225_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2217_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2217_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_dec(v_a_2215_);
lean_dec(v_snd_2213_);
lean_dec(v_fst_2212_);
lean_dec(v_fst_2210_);
v___y_2129_ = v_isEq_2200_;
v_isHEq_2130_ = v___x_1824_;
v___y_2131_ = v___y_2201_;
v___y_2132_ = v___y_2202_;
v___y_2133_ = v___y_2203_;
v___y_2134_ = v___y_2204_;
goto v___jp_2128_;
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_snd_2213_);
lean_dec(v_fst_2212_);
lean_dec(v_fst_2210_);
lean_dec_ref(v___x_1962_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2233_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2214_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2214_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_dec(v_a_2206_);
v___y_2129_ = v_isEq_2200_;
v_isHEq_2130_ = v___x_1918_;
v___y_2131_ = v___y_2201_;
v___y_2132_ = v___y_2202_;
v___y_2133_ = v___y_2203_;
v___y_2134_ = v___y_2204_;
goto v___jp_2128_;
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec_ref(v___x_1962_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2241_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2205_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2205_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
v___jp_2249_:
{
lean_object* v___x_2254_; 
lean_inc_ref(v___x_1962_);
v___x_2254_ = l_Lean_Meta_matchEq_x3f(v___x_1962_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref(v___x_2254_);
if (lean_obj_tag(v_a_2255_) == 1)
{
lean_object* v_val_2256_; lean_object* v_snd_2257_; lean_object* v_fst_2258_; lean_object* v_snd_2259_; lean_object* v___x_2260_; 
v_val_2256_ = lean_ctor_get(v_a_2255_, 0);
lean_inc(v_val_2256_);
lean_dec_ref(v_a_2255_);
v_snd_2257_ = lean_ctor_get(v_val_2256_, 1);
lean_inc(v_snd_2257_);
lean_dec(v_val_2256_);
v_fst_2258_ = lean_ctor_get(v_snd_2257_, 0);
lean_inc(v_fst_2258_);
v_snd_2259_ = lean_ctor_get(v_snd_2257_, 1);
lean_inc(v_snd_2259_);
lean_dec(v_snd_2257_);
v___x_2260_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2258_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref(v___x_2260_);
if (lean_obj_tag(v_a_2261_) == 1)
{
lean_object* v_val_2262_; lean_object* v___x_2263_; 
v_val_2262_ = lean_ctor_get(v_a_2261_, 0);
lean_inc(v_val_2262_);
lean_dec_ref(v_a_2261_);
v___x_2263_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2259_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2263_);
if (lean_obj_tag(v_a_2264_) == 1)
{
lean_object* v_toConstantVal_2265_; lean_object* v_val_2266_; lean_object* v_toConstantVal_2267_; lean_object* v_name_2268_; lean_object* v_name_2269_; uint8_t v___x_2270_; 
v_toConstantVal_2265_ = lean_ctor_get(v_val_2262_, 0);
lean_inc_ref(v_toConstantVal_2265_);
lean_dec(v_val_2262_);
v_val_2266_ = lean_ctor_get(v_a_2264_, 0);
lean_inc(v_val_2266_);
lean_dec_ref(v_a_2264_);
v_toConstantVal_2267_ = lean_ctor_get(v_val_2266_, 0);
lean_inc_ref(v_toConstantVal_2267_);
lean_dec(v_val_2266_);
v_name_2268_ = lean_ctor_get(v_toConstantVal_2265_, 0);
lean_inc(v_name_2268_);
lean_dec_ref(v_toConstantVal_2265_);
v_name_2269_ = lean_ctor_get(v_toConstantVal_2267_, 0);
lean_inc(v_name_2269_);
lean_dec_ref(v_toConstantVal_2267_);
v___x_2270_ = lean_name_eq(v_name_2268_, v_name_2269_);
lean_dec(v_name_2269_);
lean_dec(v_name_2268_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v___x_1962_);
lean_dec_ref(v_config_1813_);
v___y_1851_ = v___y_2251_;
v___y_1852_ = v___y_2252_;
v___y_1853_ = v___y_2253_;
v___y_1854_ = v___y_2250_;
goto v___jp_1850_;
}
else
{
if (v___x_1918_ == 0)
{
lean_del_object(v___x_1847_);
v_isEq_2200_ = v___x_1824_;
v___y_2201_ = v___y_2250_;
v___y_2202_ = v___y_2251_;
v___y_2203_ = v___y_2252_;
v___y_2204_ = v___y_2253_;
goto v___jp_2199_;
}
else
{
lean_dec_ref(v___x_1962_);
lean_dec_ref(v_config_1813_);
v___y_1851_ = v___y_2251_;
v___y_1852_ = v___y_2252_;
v___y_1853_ = v___y_2253_;
v___y_1854_ = v___y_2250_;
goto v___jp_1850_;
}
}
}
else
{
lean_dec(v_a_2264_);
lean_dec(v_val_2262_);
lean_del_object(v___x_1847_);
v_isEq_2200_ = v___x_1824_;
v___y_2201_ = v___y_2250_;
v___y_2202_ = v___y_2251_;
v___y_2203_ = v___y_2252_;
v___y_2204_ = v___y_2253_;
goto v___jp_2199_;
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec(v_val_2262_);
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2271_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2263_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2263_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
else
{
lean_dec(v_a_2261_);
lean_dec(v_snd_2259_);
lean_del_object(v___x_1847_);
v_isEq_2200_ = v___x_1824_;
v___y_2201_ = v___y_2250_;
v___y_2202_ = v___y_2251_;
v___y_2203_ = v___y_2252_;
v___y_2204_ = v___y_2253_;
goto v___jp_2199_;
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v_snd_2259_);
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2279_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2260_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2260_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
else
{
lean_dec(v_a_2255_);
lean_del_object(v___x_1847_);
v_isEq_2200_ = v___x_1918_;
v___y_2201_ = v___y_2250_;
v___y_2202_ = v___y_2251_;
v___y_2203_ = v___y_2252_;
v___y_2204_ = v___y_2253_;
goto v___jp_2199_;
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2287_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2254_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2254_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
v___jp_2295_:
{
lean_object* v___x_2300_; 
lean_inc_ref(v___x_1962_);
v___x_2300_ = l_refutableHasNotBit_x3f(v___x_1962_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref(v___x_2300_);
if (lean_obj_tag(v_a_2301_) == 1)
{
lean_object* v_val_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec_ref(v_config_1813_);
v_val_2302_ = lean_ctor_get(v_a_2301_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_a_2301_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2304_ = v_a_2301_;
v_isShared_2305_ = v_isSharedCheck_2341_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_val_2302_);
lean_dec(v_a_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2341_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; 
lean_inc(v_mvarId_1814_);
v___x_2306_ = l_Lean_MVarId_getType(v_mvarId_1814_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = l_Lean_LocalDecl_toExpr(v_val_1845_);
v___x_2309_ = l_Lean_Meta_mkAbsurd(v_a_2307_, v_val_2302_, v___x_2308_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1814_, v_a_2310_, v___y_2297_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2314_; 
lean_dec_ref(v___x_2311_);
v___x_2312_ = lean_box(v___x_1824_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2312_);
v___x_2314_ = v___x_2304_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v___x_1849_);
v_a_1831_ = v___x_2315_;
goto v___jp_1830_;
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_del_object(v___x_2304_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
v_a_2317_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2311_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2311_);
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
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_del_object(v___x_2304_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2325_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2309_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2309_);
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
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_del_object(v___x_2304_);
lean_dec(v_val_2302_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2333_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2306_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2306_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
else
{
lean_object* v___x_2342_; 
lean_dec(v_a_2301_);
lean_inc_ref(v___x_1962_);
v___x_2342_ = l_Lean_Meta_matchNe_x3f(v___x_1962_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
if (lean_obj_tag(v_a_2343_) == 1)
{
lean_object* v_val_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2413_; 
v_val_2344_ = lean_ctor_get(v_a_2343_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_a_2343_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2346_ = v_a_2343_;
v_isShared_2347_ = v_isSharedCheck_2413_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_val_2344_);
lean_dec(v_a_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2413_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v_snd_2348_; lean_object* v_fst_2349_; lean_object* v_snd_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2412_; 
v_snd_2348_ = lean_ctor_get(v_val_2344_, 1);
lean_inc(v_snd_2348_);
lean_dec(v_val_2344_);
v_fst_2349_ = lean_ctor_get(v_snd_2348_, 0);
v_snd_2350_ = lean_ctor_get(v_snd_2348_, 1);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_snd_2348_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2352_ = v_snd_2348_;
v_isShared_2353_ = v_isSharedCheck_2412_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_snd_2350_);
lean_inc(v_fst_2349_);
lean_dec(v_snd_2348_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2412_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; 
lean_inc(v_fst_2349_);
v___x_2354_ = l_Lean_Meta_isExprDefEq(v_fst_2349_, v_snd_2350_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; uint8_t v___x_2356_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = lean_unbox(v_a_2355_);
lean_dec(v_a_2355_);
if (v___x_2356_ == 0)
{
lean_del_object(v___x_2352_);
lean_dec(v_fst_2349_);
lean_del_object(v___x_2346_);
v___y_2250_ = v___y_2296_;
v___y_2251_ = v___y_2297_;
v___y_2252_ = v___y_2298_;
v___y_2253_ = v___y_2299_;
goto v___jp_2249_;
}
else
{
lean_object* v___x_2357_; 
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec_ref(v_config_1813_);
lean_inc(v_mvarId_1814_);
v___x_2357_ = l_Lean_MVarId_getType(v_mvarId_1814_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2359_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2357_);
v___x_2359_ = l_Lean_Meta_mkEqRefl(v_fst_2349_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = l_Lean_LocalDecl_toExpr(v_val_1845_);
v___x_2362_ = l_Lean_Meta_mkAbsurd(v_a_2358_, v_a_2360_, v___x_2361_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2364_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1814_, v_a_2363_, v___y_2297_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
lean_dec_ref(v___x_2364_);
v___x_2365_ = lean_box(v___x_1824_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2365_);
v___x_2367_ = v___x_2346_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2369_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 1, v___x_1849_);
lean_ctor_set(v___x_2352_, 0, v___x_2367_);
v___x_2369_ = v___x_2352_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_1849_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
v_a_1831_ = v___x_2369_;
goto v___jp_1830_;
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_del_object(v___x_2352_);
lean_del_object(v___x_2346_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
v_a_2372_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2364_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2364_);
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
lean_del_object(v___x_2352_);
lean_del_object(v___x_2346_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2380_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2362_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2362_);
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
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v_a_2358_);
lean_del_object(v___x_2352_);
lean_del_object(v___x_2346_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2388_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2359_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2359_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_del_object(v___x_2352_);
lean_dec(v_fst_2349_);
lean_del_object(v___x_2346_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_2396_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2357_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2357_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_del_object(v___x_2352_);
lean_dec(v_fst_2349_);
lean_del_object(v___x_2346_);
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2404_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2354_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2354_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2343_);
v___y_2250_ = v___y_2296_;
v___y_2251_ = v___y_2297_;
v___y_2252_ = v___y_2298_;
v___y_2253_ = v___y_2299_;
goto v___jp_2249_;
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2414_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2342_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2342_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec_ref(v___x_1962_);
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_2422_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2300_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2300_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
else
{
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
v_a_1839_ = v___x_1890_;
goto v___jp_1838_;
}
v___jp_1850_:
{
lean_object* v___x_1855_; 
lean_inc(v_mvarId_1814_);
v___x_1855_ = l_Lean_MVarId_getType(v_mvarId_1814_, v___y_1854_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref(v___x_1855_);
v___x_1857_ = l_Lean_LocalDecl_toExpr(v_val_1845_);
v___x_1858_ = l_Lean_Meta_mkNoConfusion(v_a_1856_, v___x_1857_, v___y_1854_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1860_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1814_, v_a_1859_, v___y_1851_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_dec_ref(v___x_1860_);
v___x_1861_ = lean_box(v___x_1824_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1861_);
v___x_1863_ = v___x_1847_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v___x_1849_);
v_a_1831_ = v___x_1864_;
goto v___jp_1830_;
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_del_object(v___x_1847_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
v_a_1866_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1860_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1860_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1847_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_1874_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1858_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1858_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
v_a_1882_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1855_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1855_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
v___jp_1891_:
{
lean_object* v_searchFuel_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_searchFuel_1896_ = lean_ctor_get(v_config_1813_, 0);
v___x_1897_ = l_Lean_LocalDecl_fvarId(v_val_1845_);
lean_dec(v_val_1845_);
lean_inc(v_searchFuel_1896_);
lean_inc(v_mvarId_1814_);
v___x_1898_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1814_, v___x_1897_, v_searchFuel_1896_, v___y_1895_, v___y_1894_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; uint8_t v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
v___x_1900_ = lean_unbox(v_a_1899_);
lean_dec(v_a_1899_);
if (v___x_1900_ == 0)
{
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
v_a_1839_ = v___x_1890_;
goto v___jp_1838_;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v___x_1901_ = lean_box(v___x_1824_);
v___x_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v___x_1849_);
v_a_1831_ = v___x_1903_;
goto v___jp_1830_;
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_1904_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1898_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1898_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
v___jp_1912_:
{
if (v___y_1917_ == 0)
{
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
v_a_1839_ = v___x_1890_;
goto v___jp_1838_;
}
else
{
v___y_1892_ = v___y_1913_;
v___y_1893_ = v___y_1914_;
v___y_1894_ = v___y_1915_;
v___y_1895_ = v___y_1916_;
goto v___jp_1891_;
}
}
v___jp_1919_:
{
if (v___y_1924_ == 0)
{
v___y_1892_ = v___y_1920_;
v___y_1893_ = v___y_1921_;
v___y_1894_ = v___y_1922_;
v___y_1895_ = v___y_1923_;
goto v___jp_1891_;
}
else
{
v___y_1913_ = v___y_1920_;
v___y_1914_ = v___y_1921_;
v___y_1915_ = v___y_1922_;
v___y_1916_ = v___y_1923_;
v___y_1917_ = v___x_1918_;
goto v___jp_1912_;
}
}
v___jp_1925_:
{
if (v___y_1931_ == 0)
{
v___y_1913_ = v___y_1926_;
v___y_1914_ = v___y_1927_;
v___y_1915_ = v___y_1928_;
v___y_1916_ = v___y_1930_;
v___y_1917_ = v___x_1918_;
goto v___jp_1912_;
}
else
{
v___y_1920_ = v___y_1926_;
v___y_1921_ = v___y_1927_;
v___y_1922_ = v___y_1928_;
v___y_1923_ = v___y_1930_;
v___y_1924_ = v___y_1929_;
goto v___jp_1919_;
}
}
v___jp_1932_:
{
uint8_t v_emptyType_1939_; 
v_emptyType_1939_ = lean_ctor_get_uint8(v_config_1813_, sizeof(void*)*1 + 1);
if (v_emptyType_1939_ == 0)
{
v___y_1926_ = v___y_1937_;
v___y_1927_ = v___y_1938_;
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___y_1934_;
v___y_1930_ = v___y_1935_;
v___y_1931_ = v___x_1918_;
goto v___jp_1925_;
}
else
{
if (v___y_1933_ == 0)
{
v___y_1920_ = v___y_1937_;
v___y_1921_ = v___y_1938_;
v___y_1922_ = v___y_1936_;
v___y_1923_ = v___y_1935_;
v___y_1924_ = v___y_1934_;
goto v___jp_1919_;
}
else
{
v___y_1926_ = v___y_1937_;
v___y_1927_ = v___y_1938_;
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___y_1934_;
v___y_1930_ = v___y_1935_;
v___y_1931_ = v___x_1918_;
goto v___jp_1925_;
}
}
}
v___jp_1940_:
{
if (v___y_1947_ == 0)
{
v___y_1933_ = v___y_1941_;
v___y_1934_ = v___y_1942_;
v___y_1935_ = v___y_1946_;
v___y_1936_ = v___y_1944_;
v___y_1937_ = v___y_1945_;
v___y_1938_ = v___y_1943_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1948_; 
lean_inc(v_val_1845_);
lean_inc(v_mvarId_1814_);
v___x_1948_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1814_, v_val_1845_, v___y_1946_, v___y_1944_, v___y_1945_, v___y_1943_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; uint8_t v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1948_);
v___x_1950_ = lean_unbox(v_a_1949_);
lean_dec(v_a_1949_);
if (v___x_1950_ == 0)
{
v___y_1933_ = v___y_1941_;
v___y_1934_ = v___y_1942_;
v___y_1935_ = v___y_1946_;
v___y_1936_ = v___y_1944_;
v___y_1937_ = v___y_1945_;
v___y_1938_ = v___y_1943_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec(v_val_1845_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v___x_1951_ = lean_box(v___x_1824_);
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
lean_ctor_set(v___x_1953_, 1, v___x_1849_);
v_a_1831_ = v___x_1953_;
goto v___jp_1830_;
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_val_1845_);
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_mvarId_1814_);
lean_dec_ref(v_config_1813_);
v_a_1954_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1948_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1948_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
}
}
v___jp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_a_1831_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1832_);
v___x_1834_ = v___x_1828_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_snd_1826_);
v___x_1834_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
}
v___jp_1838_:
{
lean_object* v___x_1840_; size_t v___x_1841_; size_t v___x_1842_; 
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1837_);
lean_ctor_set(v___x_1840_, 1, v_a_1839_);
v___x_1841_ = ((size_t)1ULL);
v___x_1842_ = lean_usize_add(v_i_1817_, v___x_1841_);
v_i_1817_ = v___x_1842_;
v_b_1818_ = v___x_1840_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2496_, lean_object* v_mvarId_2497_, lean_object* v_as_2498_, lean_object* v_sz_2499_, lean_object* v_i_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
size_t v_sz_boxed_2507_; size_t v_i_boxed_2508_; lean_object* v_res_2509_; 
v_sz_boxed_2507_ = lean_unbox_usize(v_sz_2499_);
lean_dec(v_sz_2499_);
v_i_boxed_2508_ = lean_unbox_usize(v_i_2500_);
lean_dec(v_i_2500_);
v_res_2509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2496_, v_mvarId_2497_, v_as_2498_, v_sz_boxed_2507_, v_i_boxed_2508_, v_b_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v_as_2498_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2510_, lean_object* v_mvarId_2511_, lean_object* v_as_2512_, size_t v_sz_2513_, size_t v_i_2514_, lean_object* v_b_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_usize_dec_lt(v_i_2514_, v_sz_2513_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_b_2515_);
return v___x_2522_;
}
else
{
lean_object* v_snd_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_3191_; 
v_snd_2523_ = lean_ctor_get(v_b_2515_, 1);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_b_2515_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; 
v_unused_3192_ = lean_ctor_get(v_b_2515_, 0);
lean_dec(v_unused_3192_);
v___x_2525_ = v_b_2515_;
v_isShared_2526_ = v_isSharedCheck_3191_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_snd_2523_);
lean_dec(v_b_2515_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_3191_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v_a_2528_; lean_object* v___x_2534_; lean_object* v_a_2536_; lean_object* v_a_2541_; 
v___x_2534_ = lean_box(0);
v_a_2541_ = lean_array_uget(v_as_2512_, v_i_2514_);
if (lean_obj_tag(v_a_2541_) == 0)
{
lean_del_object(v___x_2525_);
v_a_2536_ = v_snd_2523_;
goto v___jp_2535_;
}
else
{
lean_object* v_val_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_3190_; 
v_val_2542_ = lean_ctor_get(v_a_2541_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_a_2541_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_2544_ = v_a_2541_;
v_isShared_2545_ = v_isSharedCheck_3190_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_val_2542_);
lean_dec(v_a_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_3190_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___x_2587_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; uint8_t v___y_2614_; uint8_t v___x_2615_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; uint8_t v___y_2621_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; uint8_t v___y_2627_; uint8_t v___y_2628_; uint8_t v___y_2630_; uint8_t v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2638_; uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; uint8_t v___y_2642_; lean_object* v___y_2643_; uint8_t v___y_2644_; 
v___x_2546_ = lean_box(0);
v___x_2587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2615_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2542_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2659_; uint8_t v___y_2661_; uint8_t v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2670_; lean_object* v___y_2671_; uint8_t v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; uint8_t v___y_2676_; uint8_t v___y_2677_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; uint8_t v___y_2683_; lean_object* v___y_2684_; uint8_t v___y_2685_; lean_object* v_a_2686_; lean_object* v___y_2690_; lean_object* v___y_2691_; uint8_t v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; uint8_t v___y_2695_; lean_object* v___y_2781_; lean_object* v___y_2782_; uint8_t v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; uint8_t v___y_2786_; uint8_t v___y_2787_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; uint8_t v___y_2793_; lean_object* v___y_2794_; uint8_t v___y_2795_; uint8_t v___y_2796_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; uint8_t v___y_2802_; lean_object* v___y_2803_; uint8_t v___y_2804_; uint8_t v___y_2805_; lean_object* v___y_2818_; lean_object* v___y_2819_; uint8_t v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; uint8_t v___y_2823_; uint8_t v___y_2824_; uint8_t v___y_2826_; uint8_t v_isHEq_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; uint8_t v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; uint8_t v_isEq_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___x_3127_; 
v___x_2659_ = l_Lean_LocalDecl_type(v_val_2542_);
lean_inc_ref(v___x_2659_);
v___x_3127_ = l_Lean_Meta_matchNot_x3f(v___x_2659_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref(v___x_3127_);
if (lean_obj_tag(v_a_3128_) == 1)
{
lean_object* v_val_3129_; lean_object* v___x_3130_; 
v_val_3129_ = lean_ctor_get(v_a_3128_, 0);
lean_inc(v_val_3129_);
lean_dec_ref(v_a_3128_);
v___x_3130_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3129_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref(v___x_3130_);
if (lean_obj_tag(v_a_3131_) == 1)
{
lean_object* v_val_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec_ref(v_config_2510_);
v_val_3132_ = lean_ctor_get(v_a_3131_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_a_3131_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3134_ = v_a_3131_;
v_isShared_3135_ = v_isSharedCheck_3173_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_val_3132_);
lean_dec(v_a_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3173_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; 
lean_inc(v_mvarId_2511_);
v___x_3136_ = l_Lean_MVarId_getType(v_mvarId_2511_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref(v___x_3136_);
v___x_3138_ = l_Lean_LocalDecl_toExpr(v_val_2542_);
v___x_3139_ = l_Lean_mkFVar(v_val_3132_);
v___x_3140_ = l_Lean_Expr_app___override(v___x_3138_, v___x_3139_);
v___x_3141_ = l_Lean_Meta_mkFalseElim(v_a_3137_, v___x_3140_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3143_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref(v___x_3141_);
v___x_3143_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2511_, v_a_3142_, v___y_2517_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v___x_3144_; lean_object* v___x_3146_; 
lean_dec_ref(v___x_3143_);
v___x_3144_ = lean_box(v___x_2521_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3144_);
v___x_3146_ = v___x_3134_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v___x_2546_);
v_a_2528_ = v___x_3147_;
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_del_object(v___x_3134_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
v_a_3149_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3143_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3143_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_del_object(v___x_3134_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_3157_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3141_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3141_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_del_object(v___x_3134_);
lean_dec(v_val_3132_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_3165_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3136_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3136_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
}
else
{
lean_dec(v_a_3131_);
v___y_2993_ = v___y_2516_;
v___y_2994_ = v___y_2517_;
v___y_2995_ = v___y_2518_;
v___y_2996_ = v___y_2519_;
goto v___jp_2992_;
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_3174_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3130_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3130_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_dec(v_a_3128_);
v___y_2993_ = v___y_2516_;
v___y_2994_ = v___y_2517_;
v___y_2995_ = v___y_2518_;
v___y_2996_ = v___y_2519_;
goto v___jp_2992_;
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_3182_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3127_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3127_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
v___jp_2660_:
{
uint8_t v_genDiseq_2667_; 
v_genDiseq_2667_ = lean_ctor_get_uint8(v_config_2510_, sizeof(void*)*1 + 2);
if (v_genDiseq_2667_ == 0)
{
lean_dec_ref(v___x_2659_);
v___y_2638_ = v___y_2665_;
v___y_2639_ = v___y_2661_;
v___y_2640_ = v___y_2664_;
v___y_2641_ = v___y_2666_;
v___y_2642_ = v___y_2662_;
v___y_2643_ = v___y_2663_;
v___y_2644_ = v___x_2615_;
goto v___jp_2637_;
}
else
{
uint8_t v___x_2668_; 
v___x_2668_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2659_);
v___y_2638_ = v___y_2665_;
v___y_2639_ = v___y_2661_;
v___y_2640_ = v___y_2664_;
v___y_2641_ = v___y_2666_;
v___y_2642_ = v___y_2662_;
v___y_2643_ = v___y_2663_;
v___y_2644_ = v___x_2668_;
goto v___jp_2637_;
}
}
v___jp_2669_:
{
if (v___y_2677_ == 0)
{
lean_dec_ref(v___y_2675_);
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2676_;
v___y_2663_ = v___y_2671_;
v___y_2664_ = v___y_2670_;
v___y_2665_ = v___y_2673_;
v___y_2666_ = v___y_2674_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2678_; 
lean_dec_ref(v___x_2659_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v___x_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___y_2675_);
return v___x_2678_;
}
}
v___jp_2679_:
{
uint8_t v___x_2687_; 
v___x_2687_ = l_Lean_Exception_isInterrupt(v_a_2686_);
if (v___x_2687_ == 0)
{
uint8_t v___x_2688_; 
lean_inc_ref(v_a_2686_);
v___x_2688_ = l_Lean_Exception_isRuntime(v_a_2686_);
v___y_2670_ = v___y_2681_;
v___y_2671_ = v___y_2680_;
v___y_2672_ = v___y_2683_;
v___y_2673_ = v___y_2682_;
v___y_2674_ = v___y_2684_;
v___y_2675_ = v_a_2686_;
v___y_2676_ = v___y_2685_;
v___y_2677_ = v___x_2688_;
goto v___jp_2669_;
}
else
{
v___y_2670_ = v___y_2681_;
v___y_2671_ = v___y_2680_;
v___y_2672_ = v___y_2683_;
v___y_2673_ = v___y_2682_;
v___y_2674_ = v___y_2684_;
v___y_2675_ = v_a_2686_;
v___y_2676_ = v___y_2685_;
v___y_2677_ = v___x_2687_;
goto v___jp_2669_;
}
}
v___jp_2689_:
{
lean_object* v___x_2696_; 
lean_inc_ref(v___x_2659_);
v___x_2696_ = l_Lean_Meta_mkDecide(v___x_2659_, v___y_2691_, v___y_2690_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2698_; uint8_t v_foApprox_2699_; uint8_t v_ctxApprox_2700_; uint8_t v_quasiPatternApprox_2701_; uint8_t v_constApprox_2702_; uint8_t v_isDefEqStuckEx_2703_; uint8_t v_unificationHints_2704_; uint8_t v_proofIrrelevance_2705_; uint8_t v_assignSyntheticOpaque_2706_; uint8_t v_offsetCnstrs_2707_; uint8_t v_etaStruct_2708_; uint8_t v_univApprox_2709_; uint8_t v_iota_2710_; uint8_t v_beta_2711_; uint8_t v_proj_2712_; uint8_t v_zeta_2713_; uint8_t v_zetaDelta_2714_; uint8_t v_zetaUnused_2715_; uint8_t v_zetaHave_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2778_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2696_);
v___x_2698_ = l_Lean_Meta_Context_config(v___y_2691_);
v_foApprox_2699_ = lean_ctor_get_uint8(v___x_2698_, 0);
v_ctxApprox_2700_ = lean_ctor_get_uint8(v___x_2698_, 1);
v_quasiPatternApprox_2701_ = lean_ctor_get_uint8(v___x_2698_, 2);
v_constApprox_2702_ = lean_ctor_get_uint8(v___x_2698_, 3);
v_isDefEqStuckEx_2703_ = lean_ctor_get_uint8(v___x_2698_, 4);
v_unificationHints_2704_ = lean_ctor_get_uint8(v___x_2698_, 5);
v_proofIrrelevance_2705_ = lean_ctor_get_uint8(v___x_2698_, 6);
v_assignSyntheticOpaque_2706_ = lean_ctor_get_uint8(v___x_2698_, 7);
v_offsetCnstrs_2707_ = lean_ctor_get_uint8(v___x_2698_, 8);
v_etaStruct_2708_ = lean_ctor_get_uint8(v___x_2698_, 10);
v_univApprox_2709_ = lean_ctor_get_uint8(v___x_2698_, 11);
v_iota_2710_ = lean_ctor_get_uint8(v___x_2698_, 12);
v_beta_2711_ = lean_ctor_get_uint8(v___x_2698_, 13);
v_proj_2712_ = lean_ctor_get_uint8(v___x_2698_, 14);
v_zeta_2713_ = lean_ctor_get_uint8(v___x_2698_, 15);
v_zetaDelta_2714_ = lean_ctor_get_uint8(v___x_2698_, 16);
v_zetaUnused_2715_ = lean_ctor_get_uint8(v___x_2698_, 17);
v_zetaHave_2716_ = lean_ctor_get_uint8(v___x_2698_, 18);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2718_ = v___x_2698_;
v_isShared_2719_ = v_isSharedCheck_2778_;
goto v_resetjp_2717_;
}
else
{
lean_dec(v___x_2698_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2778_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
uint8_t v_trackZetaDelta_2720_; lean_object* v_zetaDeltaSet_2721_; lean_object* v_lctx_2722_; lean_object* v_localInstances_2723_; lean_object* v_defEqCtx_x3f_2724_; lean_object* v_synthPendingDepth_2725_; lean_object* v_canUnfold_x3f_2726_; uint8_t v_univApprox_2727_; uint8_t v_inTypeClassResolution_2728_; uint8_t v_cacheInferType_2729_; uint8_t v___x_2730_; lean_object* v_config_2732_; 
v_trackZetaDelta_2720_ = lean_ctor_get_uint8(v___y_2691_, sizeof(void*)*7);
v_zetaDeltaSet_2721_ = lean_ctor_get(v___y_2691_, 1);
v_lctx_2722_ = lean_ctor_get(v___y_2691_, 2);
v_localInstances_2723_ = lean_ctor_get(v___y_2691_, 3);
v_defEqCtx_x3f_2724_ = lean_ctor_get(v___y_2691_, 4);
v_synthPendingDepth_2725_ = lean_ctor_get(v___y_2691_, 5);
v_canUnfold_x3f_2726_ = lean_ctor_get(v___y_2691_, 6);
v_univApprox_2727_ = lean_ctor_get_uint8(v___y_2691_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2728_ = lean_ctor_get_uint8(v___y_2691_, sizeof(void*)*7 + 2);
v_cacheInferType_2729_ = lean_ctor_get_uint8(v___y_2691_, sizeof(void*)*7 + 3);
v___x_2730_ = 1;
if (v_isShared_2719_ == 0)
{
v_config_2732_ = v___x_2718_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 0, v_foApprox_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 1, v_ctxApprox_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 2, v_quasiPatternApprox_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 3, v_constApprox_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 4, v_isDefEqStuckEx_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 5, v_unificationHints_2704_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 6, v_proofIrrelevance_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 7, v_assignSyntheticOpaque_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 8, v_offsetCnstrs_2707_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 10, v_etaStruct_2708_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 11, v_univApprox_2709_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 12, v_iota_2710_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 13, v_beta_2711_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 14, v_proj_2712_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 15, v_zeta_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 16, v_zetaDelta_2714_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 17, v_zetaUnused_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 18, v_zetaHave_2716_);
v_config_2732_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
uint64_t v___x_2733_; uint64_t v___x_2734_; uint64_t v___x_2735_; uint64_t v___x_2736_; uint64_t v___x_2737_; uint64_t v_key_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_ctor_set_uint8(v_config_2732_, 9, v___x_2730_);
v___x_2733_ = l_Lean_Meta_Context_configKey(v___y_2691_);
v___x_2734_ = 2ULL;
v___x_2735_ = lean_uint64_shift_right(v___x_2733_, v___x_2734_);
v___x_2736_ = lean_uint64_shift_left(v___x_2735_, v___x_2734_);
v___x_2737_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_2738_ = lean_uint64_lor(v___x_2736_, v___x_2737_);
v___x_2739_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2739_, 0, v_config_2732_);
lean_ctor_set_uint64(v___x_2739_, sizeof(void*)*1, v_key_2738_);
lean_inc(v_canUnfold_x3f_2726_);
lean_inc(v_synthPendingDepth_2725_);
lean_inc(v_defEqCtx_x3f_2724_);
lean_inc_ref(v_localInstances_2723_);
lean_inc_ref(v_lctx_2722_);
lean_inc(v_zetaDeltaSet_2721_);
v___x_2740_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
lean_ctor_set(v___x_2740_, 1, v_zetaDeltaSet_2721_);
lean_ctor_set(v___x_2740_, 2, v_lctx_2722_);
lean_ctor_set(v___x_2740_, 3, v_localInstances_2723_);
lean_ctor_set(v___x_2740_, 4, v_defEqCtx_x3f_2724_);
lean_ctor_set(v___x_2740_, 5, v_synthPendingDepth_2725_);
lean_ctor_set(v___x_2740_, 6, v_canUnfold_x3f_2726_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*7, v_trackZetaDelta_2720_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*7 + 1, v_univApprox_2727_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2728_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*7 + 3, v_cacheInferType_2729_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2690_);
lean_inc(v_a_2697_);
v___x_2741_ = lean_whnf(v_a_2697_, v___x_2740_, v___y_2690_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref(v___x_2741_);
v___x_2743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_2744_ = l_Lean_Expr_isConstOf(v_a_2742_, v___x_2743_);
lean_dec(v_a_2742_);
if (v___x_2744_ == 0)
{
lean_dec(v_a_2697_);
v___y_2661_ = v___y_2692_;
v___y_2662_ = v___y_2695_;
v___y_2663_ = v___y_2691_;
v___y_2664_ = v___y_2690_;
v___y_2665_ = v___y_2693_;
v___y_2666_ = v___y_2694_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2745_; 
lean_inc(v_a_2697_);
v___x_2745_ = l_Lean_Meta_mkEqRefl(v_a_2697_, v___y_2691_, v___y_2690_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2747_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref(v___x_2745_);
lean_inc(v_mvarId_2511_);
v___x_2747_ = l_Lean_MVarId_getType(v_mvarId_2511_, v___y_2691_, v___y_2690_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v_nargs_2749_; lean_object* v___x_2750_; lean_object* v_dummy_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref(v___x_2747_);
v_nargs_2749_ = l_Lean_Expr_getAppNumArgs(v_a_2697_);
v___x_2750_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2751_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2749_);
v___x_2752_ = lean_mk_array(v_nargs_2749_, v_dummy_2751_);
v___x_2753_ = lean_unsigned_to_nat(1u);
v___x_2754_ = lean_nat_sub(v_nargs_2749_, v___x_2753_);
lean_dec(v_nargs_2749_);
v___x_2755_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2697_, v___x_2752_, v___x_2754_);
v___x_2756_ = lean_array_push(v___x_2755_, v_a_2746_);
v___x_2757_ = l_Lean_mkAppN(v___x_2750_, v___x_2756_);
lean_dec_ref(v___x_2756_);
lean_inc(v_val_2542_);
v___x_2758_ = l_Lean_LocalDecl_toExpr(v_val_2542_);
v___x_2759_ = l_Lean_Meta_mkAbsurd(v_a_2748_, v___x_2758_, v___x_2757_, v___y_2691_, v___y_2690_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref(v___x_2759_);
lean_inc(v_mvarId_2511_);
v___x_2761_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2511_, v_a_2760_, v___y_2690_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v___x_2659_);
lean_dec(v_val_2542_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2770_ == 0)
{
lean_object* v_unused_2771_; 
v_unused_2771_ = lean_ctor_get(v___x_2761_, 0);
lean_dec(v_unused_2771_);
v___x_2763_ = v___x_2761_;
v_isShared_2764_ = v_isSharedCheck_2770_;
goto v_resetjp_2762_;
}
else
{
lean_dec(v___x_2761_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2770_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2765_ = lean_box(v___x_2521_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set_tag(v___x_2763_, 1);
lean_ctor_set(v___x_2763_, 0, v___x_2765_);
v___x_2767_ = v___x_2763_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v___x_2546_);
v_a_2528_ = v___x_2768_;
goto v___jp_2527_;
}
}
}
else
{
lean_object* v_a_2772_; 
v_a_2772_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2772_);
lean_dec_ref(v___x_2761_);
v___y_2680_ = v___y_2691_;
v___y_2681_ = v___y_2690_;
v___y_2682_ = v___y_2693_;
v___y_2683_ = v___y_2692_;
v___y_2684_ = v___y_2694_;
v___y_2685_ = v___y_2695_;
v_a_2686_ = v_a_2772_;
goto v___jp_2679_;
}
}
else
{
lean_object* v_a_2773_; 
v_a_2773_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2773_);
lean_dec_ref(v___x_2759_);
v___y_2680_ = v___y_2691_;
v___y_2681_ = v___y_2690_;
v___y_2682_ = v___y_2693_;
v___y_2683_ = v___y_2692_;
v___y_2684_ = v___y_2694_;
v___y_2685_ = v___y_2695_;
v_a_2686_ = v_a_2773_;
goto v___jp_2679_;
}
}
else
{
lean_object* v_a_2774_; 
lean_dec(v_a_2746_);
lean_dec(v_a_2697_);
v_a_2774_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2774_);
lean_dec_ref(v___x_2747_);
v___y_2680_ = v___y_2691_;
v___y_2681_ = v___y_2690_;
v___y_2682_ = v___y_2693_;
v___y_2683_ = v___y_2692_;
v___y_2684_ = v___y_2694_;
v___y_2685_ = v___y_2695_;
v_a_2686_ = v_a_2774_;
goto v___jp_2679_;
}
}
else
{
lean_object* v_a_2775_; 
lean_dec(v_a_2697_);
v_a_2775_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2775_);
lean_dec_ref(v___x_2745_);
v___y_2680_ = v___y_2691_;
v___y_2681_ = v___y_2690_;
v___y_2682_ = v___y_2693_;
v___y_2683_ = v___y_2692_;
v___y_2684_ = v___y_2694_;
v___y_2685_ = v___y_2695_;
v_a_2686_ = v_a_2775_;
goto v___jp_2679_;
}
}
}
else
{
lean_object* v_a_2776_; 
lean_dec(v_a_2697_);
v_a_2776_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2776_);
lean_dec_ref(v___x_2741_);
v___y_2680_ = v___y_2691_;
v___y_2681_ = v___y_2690_;
v___y_2682_ = v___y_2693_;
v___y_2683_ = v___y_2692_;
v___y_2684_ = v___y_2694_;
v___y_2685_ = v___y_2695_;
v_a_2686_ = v_a_2776_;
goto v___jp_2679_;
}
}
}
}
else
{
lean_object* v_a_2779_; 
v_a_2779_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2779_);
lean_dec_ref(v___x_2696_);
v___y_2680_ = v___y_2691_;
v___y_2681_ = v___y_2690_;
v___y_2682_ = v___y_2693_;
v___y_2683_ = v___y_2692_;
v___y_2684_ = v___y_2694_;
v___y_2685_ = v___y_2695_;
v_a_2686_ = v_a_2779_;
goto v___jp_2679_;
}
}
v___jp_2780_:
{
if (v___y_2787_ == 0)
{
v___y_2661_ = v___y_2783_;
v___y_2662_ = v___y_2786_;
v___y_2663_ = v___y_2782_;
v___y_2664_ = v___y_2781_;
v___y_2665_ = v___y_2784_;
v___y_2666_ = v___y_2785_;
goto v___jp_2660_;
}
else
{
v___y_2690_ = v___y_2781_;
v___y_2691_ = v___y_2782_;
v___y_2692_ = v___y_2783_;
v___y_2693_ = v___y_2784_;
v___y_2694_ = v___y_2785_;
v___y_2695_ = v___y_2786_;
goto v___jp_2689_;
}
}
v___jp_2788_:
{
if (v___y_2796_ == 0)
{
lean_dec_ref(v___y_2791_);
v___y_2781_ = v___y_2790_;
v___y_2782_ = v___y_2789_;
v___y_2783_ = v___y_2793_;
v___y_2784_ = v___y_2792_;
v___y_2785_ = v___y_2794_;
v___y_2786_ = v___y_2795_;
v___y_2787_ = v___x_2615_;
goto v___jp_2780_;
}
else
{
uint8_t v___x_2797_; 
v___x_2797_ = l_Lean_Expr_hasFVar(v___y_2791_);
lean_dec_ref(v___y_2791_);
if (v___x_2797_ == 0)
{
v___y_2690_ = v___y_2790_;
v___y_2691_ = v___y_2789_;
v___y_2692_ = v___y_2793_;
v___y_2693_ = v___y_2792_;
v___y_2694_ = v___y_2794_;
v___y_2695_ = v___y_2795_;
goto v___jp_2689_;
}
else
{
v___y_2781_ = v___y_2790_;
v___y_2782_ = v___y_2789_;
v___y_2783_ = v___y_2793_;
v___y_2784_ = v___y_2792_;
v___y_2785_ = v___y_2794_;
v___y_2786_ = v___y_2795_;
v___y_2787_ = v___x_2615_;
goto v___jp_2780_;
}
}
}
v___jp_2798_:
{
lean_object* v___x_2806_; 
lean_inc_ref(v___x_2659_);
v___x_2806_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2659_, v___y_2800_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; uint8_t v___x_2808_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref(v___x_2806_);
v___x_2808_ = l_Lean_Expr_hasMVar(v_a_2807_);
if (v___x_2808_ == 0)
{
v___y_2789_ = v___y_2799_;
v___y_2790_ = v___y_2800_;
v___y_2791_ = v_a_2807_;
v___y_2792_ = v___y_2801_;
v___y_2793_ = v___y_2802_;
v___y_2794_ = v___y_2803_;
v___y_2795_ = v___y_2804_;
v___y_2796_ = v___y_2805_;
goto v___jp_2788_;
}
else
{
v___y_2789_ = v___y_2799_;
v___y_2790_ = v___y_2800_;
v___y_2791_ = v_a_2807_;
v___y_2792_ = v___y_2801_;
v___y_2793_ = v___y_2802_;
v___y_2794_ = v___y_2803_;
v___y_2795_ = v___y_2804_;
v___y_2796_ = v___x_2615_;
goto v___jp_2788_;
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec_ref(v___x_2659_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2809_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2806_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2806_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
v___jp_2817_:
{
if (v___y_2824_ == 0)
{
v___y_2661_ = v___y_2820_;
v___y_2662_ = v___y_2823_;
v___y_2663_ = v___y_2819_;
v___y_2664_ = v___y_2818_;
v___y_2665_ = v___y_2821_;
v___y_2666_ = v___y_2822_;
goto v___jp_2660_;
}
else
{
v___y_2799_ = v___y_2819_;
v___y_2800_ = v___y_2818_;
v___y_2801_ = v___y_2821_;
v___y_2802_ = v___y_2820_;
v___y_2803_ = v___y_2822_;
v___y_2804_ = v___y_2823_;
v___y_2805_ = v___y_2824_;
goto v___jp_2798_;
}
}
v___jp_2825_:
{
uint8_t v_useDecide_2832_; 
v_useDecide_2832_ = lean_ctor_get_uint8(v_config_2510_, sizeof(void*)*1);
if (v_useDecide_2832_ == 0)
{
v___y_2818_ = v___y_2829_;
v___y_2819_ = v___y_2828_;
v___y_2820_ = v___y_2826_;
v___y_2821_ = v___y_2830_;
v___y_2822_ = v___y_2831_;
v___y_2823_ = v_isHEq_2827_;
v___y_2824_ = v___x_2615_;
goto v___jp_2817_;
}
else
{
uint8_t v___x_2833_; 
v___x_2833_ = l_Lean_Expr_hasFVar(v___x_2659_);
if (v___x_2833_ == 0)
{
v___y_2799_ = v___y_2828_;
v___y_2800_ = v___y_2829_;
v___y_2801_ = v___y_2830_;
v___y_2802_ = v___y_2826_;
v___y_2803_ = v___y_2831_;
v___y_2804_ = v_isHEq_2827_;
v___y_2805_ = v_useDecide_2832_;
goto v___jp_2798_;
}
else
{
v___y_2818_ = v___y_2829_;
v___y_2819_ = v___y_2828_;
v___y_2820_ = v___y_2826_;
v___y_2821_ = v___y_2830_;
v___y_2822_ = v___y_2831_;
v___y_2823_ = v_isHEq_2827_;
v___y_2824_ = v___x_2615_;
goto v___jp_2817_;
}
}
}
v___jp_2834_:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_Meta_isExprDefEq(v___y_2836_, v___y_2837_, v___y_2840_, v___y_2839_, v___y_2835_, v___y_2841_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; uint8_t v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref(v___x_2842_);
v___x_2844_ = lean_unbox(v_a_2843_);
lean_dec(v_a_2843_);
if (v___x_2844_ == 0)
{
v___y_2826_ = v___y_2838_;
v_isHEq_2827_ = v___x_2521_;
v___y_2828_ = v___y_2840_;
v___y_2829_ = v___y_2839_;
v___y_2830_ = v___y_2835_;
v___y_2831_ = v___y_2841_;
goto v___jp_2825_;
}
else
{
lean_object* v___x_2845_; 
lean_dec_ref(v___x_2659_);
lean_dec_ref(v_config_2510_);
lean_inc(v_mvarId_2511_);
v___x_2845_ = l_Lean_MVarId_getType(v_mvarId_2511_, v___y_2840_, v___y_2839_, v___y_2835_, v___y_2841_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref(v___x_2845_);
v___x_2847_ = l_Lean_LocalDecl_toExpr(v_val_2542_);
v___x_2848_ = l_Lean_Meta_mkEqOfHEq(v___x_2847_, v___x_2521_, v___y_2840_, v___y_2839_, v___y_2835_, v___y_2841_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref(v___x_2848_);
v___x_2850_ = l_Lean_Meta_mkNoConfusion(v_a_2846_, v_a_2849_, v___y_2840_, v___y_2839_, v___y_2835_, v___y_2841_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2511_, v_a_2851_, v___y_2839_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_dec_ref(v___x_2852_);
v___x_2853_ = lean_box(v___x_2521_);
v___x_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2546_);
v_a_2528_ = v___x_2855_;
goto v___jp_2527_;
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
v_a_2856_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2852_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2852_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_2864_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2850_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2850_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_a_2846_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_2872_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2848_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2848_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_2880_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2845_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2845_);
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
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v___x_2659_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2888_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2842_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2842_);
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
v___jp_2896_:
{
lean_object* v___x_2902_; 
lean_inc_ref(v___x_2659_);
v___x_2902_ = l_Lean_Meta_matchHEq_x3f(v___x_2659_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref(v___x_2902_);
if (lean_obj_tag(v_a_2903_) == 1)
{
lean_object* v_val_2904_; lean_object* v_snd_2905_; lean_object* v_snd_2906_; lean_object* v_fst_2907_; lean_object* v_fst_2908_; lean_object* v_fst_2909_; lean_object* v_snd_2910_; lean_object* v___x_2911_; 
v_val_2904_ = lean_ctor_get(v_a_2903_, 0);
lean_inc(v_val_2904_);
lean_dec_ref(v_a_2903_);
v_snd_2905_ = lean_ctor_get(v_val_2904_, 1);
lean_inc(v_snd_2905_);
v_snd_2906_ = lean_ctor_get(v_snd_2905_, 1);
lean_inc(v_snd_2906_);
v_fst_2907_ = lean_ctor_get(v_val_2904_, 0);
lean_inc(v_fst_2907_);
lean_dec(v_val_2904_);
v_fst_2908_ = lean_ctor_get(v_snd_2905_, 0);
lean_inc(v_fst_2908_);
lean_dec(v_snd_2905_);
v_fst_2909_ = lean_ctor_get(v_snd_2906_, 0);
lean_inc(v_fst_2909_);
v_snd_2910_ = lean_ctor_get(v_snd_2906_, 1);
lean_inc(v_snd_2910_);
lean_dec(v_snd_2906_);
v___x_2911_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2908_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref(v___x_2911_);
if (lean_obj_tag(v_a_2912_) == 1)
{
lean_object* v_val_2913_; lean_object* v___x_2914_; 
v_val_2913_ = lean_ctor_get(v_a_2912_, 0);
lean_inc(v_val_2913_);
lean_dec_ref(v_a_2912_);
v___x_2914_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2910_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2914_);
if (lean_obj_tag(v_a_2915_) == 1)
{
lean_object* v_toConstantVal_2916_; lean_object* v_val_2917_; lean_object* v_toConstantVal_2918_; lean_object* v_name_2919_; lean_object* v_name_2920_; uint8_t v___x_2921_; 
v_toConstantVal_2916_ = lean_ctor_get(v_val_2913_, 0);
lean_inc_ref(v_toConstantVal_2916_);
lean_dec(v_val_2913_);
v_val_2917_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_val_2917_);
lean_dec_ref(v_a_2915_);
v_toConstantVal_2918_ = lean_ctor_get(v_val_2917_, 0);
lean_inc_ref(v_toConstantVal_2918_);
lean_dec(v_val_2917_);
v_name_2919_ = lean_ctor_get(v_toConstantVal_2916_, 0);
lean_inc(v_name_2919_);
lean_dec_ref(v_toConstantVal_2916_);
v_name_2920_ = lean_ctor_get(v_toConstantVal_2918_, 0);
lean_inc(v_name_2920_);
lean_dec_ref(v_toConstantVal_2918_);
v___x_2921_ = lean_name_eq(v_name_2919_, v_name_2920_);
lean_dec(v_name_2920_);
lean_dec(v_name_2919_);
if (v___x_2921_ == 0)
{
v___y_2835_ = v___y_2900_;
v___y_2836_ = v_fst_2907_;
v___y_2837_ = v_fst_2909_;
v___y_2838_ = v_isEq_2897_;
v___y_2839_ = v___y_2899_;
v___y_2840_ = v___y_2898_;
v___y_2841_ = v___y_2901_;
goto v___jp_2834_;
}
else
{
if (v___x_2615_ == 0)
{
lean_dec(v_fst_2909_);
lean_dec(v_fst_2907_);
v___y_2826_ = v_isEq_2897_;
v_isHEq_2827_ = v___x_2521_;
v___y_2828_ = v___y_2898_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
v___y_2831_ = v___y_2901_;
goto v___jp_2825_;
}
else
{
v___y_2835_ = v___y_2900_;
v___y_2836_ = v_fst_2907_;
v___y_2837_ = v_fst_2909_;
v___y_2838_ = v_isEq_2897_;
v___y_2839_ = v___y_2899_;
v___y_2840_ = v___y_2898_;
v___y_2841_ = v___y_2901_;
goto v___jp_2834_;
}
}
}
else
{
lean_dec(v_a_2915_);
lean_dec(v_val_2913_);
lean_dec(v_fst_2909_);
lean_dec(v_fst_2907_);
v___y_2826_ = v_isEq_2897_;
v_isHEq_2827_ = v___x_2521_;
v___y_2828_ = v___y_2898_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
v___y_2831_ = v___y_2901_;
goto v___jp_2825_;
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_val_2913_);
lean_dec(v_fst_2909_);
lean_dec(v_fst_2907_);
lean_dec_ref(v___x_2659_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2922_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2914_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2914_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_dec(v_a_2912_);
lean_dec(v_snd_2910_);
lean_dec(v_fst_2909_);
lean_dec(v_fst_2907_);
v___y_2826_ = v_isEq_2897_;
v_isHEq_2827_ = v___x_2521_;
v___y_2828_ = v___y_2898_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
v___y_2831_ = v___y_2901_;
goto v___jp_2825_;
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_snd_2910_);
lean_dec(v_fst_2909_);
lean_dec(v_fst_2907_);
lean_dec_ref(v___x_2659_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2930_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2911_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2911_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_dec(v_a_2903_);
v___y_2826_ = v_isEq_2897_;
v_isHEq_2827_ = v___x_2615_;
v___y_2828_ = v___y_2898_;
v___y_2829_ = v___y_2899_;
v___y_2830_ = v___y_2900_;
v___y_2831_ = v___y_2901_;
goto v___jp_2825_;
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v___x_2659_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2938_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2902_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2902_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
v___jp_2946_:
{
lean_object* v___x_2951_; 
lean_inc_ref(v___x_2659_);
v___x_2951_ = l_Lean_Meta_matchEq_x3f(v___x_2659_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref(v___x_2951_);
if (lean_obj_tag(v_a_2952_) == 1)
{
lean_object* v_val_2953_; lean_object* v_snd_2954_; lean_object* v_fst_2955_; lean_object* v_snd_2956_; lean_object* v___x_2957_; 
v_val_2953_ = lean_ctor_get(v_a_2952_, 0);
lean_inc(v_val_2953_);
lean_dec_ref(v_a_2952_);
v_snd_2954_ = lean_ctor_get(v_val_2953_, 1);
lean_inc(v_snd_2954_);
lean_dec(v_val_2953_);
v_fst_2955_ = lean_ctor_get(v_snd_2954_, 0);
lean_inc(v_fst_2955_);
v_snd_2956_ = lean_ctor_get(v_snd_2954_, 1);
lean_inc(v_snd_2956_);
lean_dec(v_snd_2954_);
v___x_2957_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2955_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref(v___x_2957_);
if (lean_obj_tag(v_a_2958_) == 1)
{
lean_object* v_val_2959_; lean_object* v___x_2960_; 
v_val_2959_ = lean_ctor_get(v_a_2958_, 0);
lean_inc(v_val_2959_);
lean_dec_ref(v_a_2958_);
v___x_2960_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2956_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref(v___x_2960_);
if (lean_obj_tag(v_a_2961_) == 1)
{
lean_object* v_toConstantVal_2962_; lean_object* v_val_2963_; lean_object* v_toConstantVal_2964_; lean_object* v_name_2965_; lean_object* v_name_2966_; uint8_t v___x_2967_; 
v_toConstantVal_2962_ = lean_ctor_get(v_val_2959_, 0);
lean_inc_ref(v_toConstantVal_2962_);
lean_dec(v_val_2959_);
v_val_2963_ = lean_ctor_get(v_a_2961_, 0);
lean_inc(v_val_2963_);
lean_dec_ref(v_a_2961_);
v_toConstantVal_2964_ = lean_ctor_get(v_val_2963_, 0);
lean_inc_ref(v_toConstantVal_2964_);
lean_dec(v_val_2963_);
v_name_2965_ = lean_ctor_get(v_toConstantVal_2962_, 0);
lean_inc(v_name_2965_);
lean_dec_ref(v_toConstantVal_2962_);
v_name_2966_ = lean_ctor_get(v_toConstantVal_2964_, 0);
lean_inc(v_name_2966_);
lean_dec_ref(v_toConstantVal_2964_);
v___x_2967_ = lean_name_eq(v_name_2965_, v_name_2966_);
lean_dec(v_name_2966_);
lean_dec(v_name_2965_);
if (v___x_2967_ == 0)
{
lean_dec_ref(v___x_2659_);
lean_dec_ref(v_config_2510_);
v___y_2548_ = v___y_2949_;
v___y_2549_ = v___y_2948_;
v___y_2550_ = v___y_2950_;
v___y_2551_ = v___y_2947_;
goto v___jp_2547_;
}
else
{
if (v___x_2615_ == 0)
{
lean_del_object(v___x_2544_);
v_isEq_2897_ = v___x_2521_;
v___y_2898_ = v___y_2947_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
v___y_2901_ = v___y_2950_;
goto v___jp_2896_;
}
else
{
lean_dec_ref(v___x_2659_);
lean_dec_ref(v_config_2510_);
v___y_2548_ = v___y_2949_;
v___y_2549_ = v___y_2948_;
v___y_2550_ = v___y_2950_;
v___y_2551_ = v___y_2947_;
goto v___jp_2547_;
}
}
}
else
{
lean_dec(v_a_2961_);
lean_dec(v_val_2959_);
lean_del_object(v___x_2544_);
v_isEq_2897_ = v___x_2521_;
v___y_2898_ = v___y_2947_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
v___y_2901_ = v___y_2950_;
goto v___jp_2896_;
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec(v_val_2959_);
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2968_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2960_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2960_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
lean_dec(v_a_2958_);
lean_dec(v_snd_2956_);
lean_del_object(v___x_2544_);
v_isEq_2897_ = v___x_2521_;
v___y_2898_ = v___y_2947_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
v___y_2901_ = v___y_2950_;
goto v___jp_2896_;
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_snd_2956_);
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2976_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2957_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2957_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_dec(v_a_2952_);
lean_del_object(v___x_2544_);
v_isEq_2897_ = v___x_2615_;
v___y_2898_ = v___y_2947_;
v___y_2899_ = v___y_2948_;
v___y_2900_ = v___y_2949_;
v___y_2901_ = v___y_2950_;
goto v___jp_2896_;
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2984_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2951_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2951_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
v___jp_2992_:
{
lean_object* v___x_2997_; 
lean_inc_ref(v___x_2659_);
v___x_2997_ = l_refutableHasNotBit_x3f(v___x_2659_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref(v___x_2997_);
if (lean_obj_tag(v_a_2998_) == 1)
{
lean_object* v_val_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec_ref(v_config_2510_);
v_val_2999_ = lean_ctor_get(v_a_2998_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_a_2998_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3001_ = v_a_2998_;
v_isShared_3002_ = v_isSharedCheck_3038_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_val_2999_);
lean_dec(v_a_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3038_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; 
lean_inc(v_mvarId_2511_);
v___x_3003_ = l_Lean_MVarId_getType(v_mvarId_2511_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = l_Lean_LocalDecl_toExpr(v_val_2542_);
v___x_3006_ = l_Lean_Meta_mkAbsurd(v_a_3004_, v_val_2999_, v___x_3005_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3006_);
v___x_3008_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2511_, v_a_3007_, v___y_2994_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_dec_ref(v___x_3008_);
v___x_3009_ = lean_box(v___x_2521_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3009_);
v___x_3011_ = v___x_3001_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
lean_ctor_set(v___x_3012_, 1, v___x_2546_);
v_a_2528_ = v___x_3012_;
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_del_object(v___x_3001_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
v_a_3014_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3008_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3008_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_del_object(v___x_3001_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_3022_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3006_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3006_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_del_object(v___x_3001_);
lean_dec(v_val_2999_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_3030_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3003_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3003_);
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
}
else
{
lean_object* v___x_3039_; 
lean_dec(v_a_2998_);
lean_inc_ref(v___x_2659_);
v___x_3039_ = l_Lean_Meta_matchNe_x3f(v___x_2659_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref(v___x_3039_);
if (lean_obj_tag(v_a_3040_) == 1)
{
lean_object* v_val_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3110_; 
v_val_3041_ = lean_ctor_get(v_a_3040_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_a_3040_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3043_ = v_a_3040_;
v_isShared_3044_ = v_isSharedCheck_3110_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_val_3041_);
lean_dec(v_a_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3110_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_snd_3045_; lean_object* v_fst_3046_; lean_object* v_snd_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3109_; 
v_snd_3045_ = lean_ctor_get(v_val_3041_, 1);
lean_inc(v_snd_3045_);
lean_dec(v_val_3041_);
v_fst_3046_ = lean_ctor_get(v_snd_3045_, 0);
v_snd_3047_ = lean_ctor_get(v_snd_3045_, 1);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_snd_3045_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3049_ = v_snd_3045_;
v_isShared_3050_ = v_isSharedCheck_3109_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_snd_3047_);
lean_inc(v_fst_3046_);
lean_dec(v_snd_3045_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3109_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3051_; 
lean_inc(v_fst_3046_);
v___x_3051_ = l_Lean_Meta_isExprDefEq(v_fst_3046_, v_snd_3047_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; uint8_t v___x_3053_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref(v___x_3051_);
v___x_3053_ = lean_unbox(v_a_3052_);
lean_dec(v_a_3052_);
if (v___x_3053_ == 0)
{
lean_del_object(v___x_3049_);
lean_dec(v_fst_3046_);
lean_del_object(v___x_3043_);
v___y_2947_ = v___y_2993_;
v___y_2948_ = v___y_2994_;
v___y_2949_ = v___y_2995_;
v___y_2950_ = v___y_2996_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_3054_; 
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec_ref(v_config_2510_);
lean_inc(v_mvarId_2511_);
v___x_3054_ = l_Lean_MVarId_getType(v_mvarId_2511_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3056_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref(v___x_3054_);
v___x_3056_ = l_Lean_Meta_mkEqRefl(v_fst_3046_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref(v___x_3056_);
v___x_3058_ = l_Lean_LocalDecl_toExpr(v_val_2542_);
v___x_3059_ = l_Lean_Meta_mkAbsurd(v_a_3055_, v_a_3057_, v___x_3058_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3061_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref(v___x_3059_);
v___x_3061_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2511_, v_a_3060_, v___y_2994_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
lean_dec_ref(v___x_3061_);
v___x_3062_ = lean_box(v___x_2521_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3062_);
v___x_3064_ = v___x_3043_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3066_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 1, v___x_2546_);
lean_ctor_set(v___x_3049_, 0, v___x_3064_);
v___x_3066_ = v___x_3049_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_2546_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
v_a_2528_ = v___x_3066_;
goto v___jp_2527_;
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_del_object(v___x_3049_);
lean_del_object(v___x_3043_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
v_a_3069_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3061_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3061_);
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
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_del_object(v___x_3049_);
lean_del_object(v___x_3043_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_3077_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3059_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3059_);
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
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_a_3055_);
lean_del_object(v___x_3049_);
lean_del_object(v___x_3043_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_3085_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3056_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3056_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_del_object(v___x_3049_);
lean_dec(v_fst_3046_);
lean_del_object(v___x_3043_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_3093_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3054_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3054_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_del_object(v___x_3049_);
lean_dec(v_fst_3046_);
lean_del_object(v___x_3043_);
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_3101_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3051_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3051_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3040_);
v___y_2947_ = v___y_2993_;
v___y_2948_ = v___y_2994_;
v___y_2949_ = v___y_2995_;
v___y_2950_ = v___y_2996_;
goto v___jp_2946_;
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_3111_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3039_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3039_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v___x_2659_);
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_3119_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_2997_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_2997_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
v_a_2536_ = v___x_2587_;
goto v___jp_2535_;
}
v___jp_2547_:
{
lean_object* v___x_2552_; 
lean_inc(v_mvarId_2511_);
v___x_2552_ = l_Lean_MVarId_getType(v_mvarId_2511_, v___y_2551_, v___y_2549_, v___y_2548_, v___y_2550_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
v___x_2554_ = l_Lean_LocalDecl_toExpr(v_val_2542_);
v___x_2555_ = l_Lean_Meta_mkNoConfusion(v_a_2553_, v___x_2554_, v___y_2551_, v___y_2549_, v___y_2548_, v___y_2550_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref(v___x_2555_);
v___x_2557_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2511_, v_a_2556_, v___y_2549_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_dec_ref(v___x_2557_);
v___x_2558_ = lean_box(v___x_2521_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2558_);
v___x_2560_ = v___x_2544_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
lean_ctor_set(v___x_2561_, 1, v___x_2546_);
v_a_2528_ = v___x_2561_;
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_del_object(v___x_2544_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
v_a_2563_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2557_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2557_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_del_object(v___x_2544_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_2571_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2555_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2555_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_del_object(v___x_2544_);
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
v_a_2579_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2552_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2552_);
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
v___jp_2588_:
{
lean_object* v_searchFuel_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_searchFuel_2593_ = lean_ctor_get(v_config_2510_, 0);
v___x_2594_ = l_Lean_LocalDecl_fvarId(v_val_2542_);
lean_dec(v_val_2542_);
lean_inc(v_searchFuel_2593_);
lean_inc(v_mvarId_2511_);
v___x_2595_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2511_, v___x_2594_, v_searchFuel_2593_, v___y_2589_, v___y_2592_, v___y_2591_, v___y_2590_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; uint8_t v___x_2597_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref(v___x_2595_);
v___x_2597_ = lean_unbox(v_a_2596_);
lean_dec(v_a_2596_);
if (v___x_2597_ == 0)
{
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
v_a_2536_ = v___x_2587_;
goto v___jp_2535_;
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v___x_2598_ = lean_box(v___x_2521_);
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2546_);
v_a_2528_ = v___x_2600_;
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2601_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2595_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2595_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
v___jp_2609_:
{
if (v___y_2614_ == 0)
{
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
v_a_2536_ = v___x_2587_;
goto v___jp_2535_;
}
else
{
v___y_2589_ = v___y_2610_;
v___y_2590_ = v___y_2611_;
v___y_2591_ = v___y_2612_;
v___y_2592_ = v___y_2613_;
goto v___jp_2588_;
}
}
v___jp_2616_:
{
if (v___y_2621_ == 0)
{
v___y_2589_ = v___y_2617_;
v___y_2590_ = v___y_2618_;
v___y_2591_ = v___y_2619_;
v___y_2592_ = v___y_2620_;
goto v___jp_2588_;
}
else
{
v___y_2610_ = v___y_2617_;
v___y_2611_ = v___y_2618_;
v___y_2612_ = v___y_2619_;
v___y_2613_ = v___y_2620_;
v___y_2614_ = v___x_2615_;
goto v___jp_2609_;
}
}
v___jp_2622_:
{
if (v___y_2628_ == 0)
{
v___y_2610_ = v___y_2623_;
v___y_2611_ = v___y_2624_;
v___y_2612_ = v___y_2625_;
v___y_2613_ = v___y_2626_;
v___y_2614_ = v___x_2615_;
goto v___jp_2609_;
}
else
{
v___y_2617_ = v___y_2623_;
v___y_2618_ = v___y_2624_;
v___y_2619_ = v___y_2625_;
v___y_2620_ = v___y_2626_;
v___y_2621_ = v___y_2627_;
goto v___jp_2616_;
}
}
v___jp_2629_:
{
uint8_t v_emptyType_2636_; 
v_emptyType_2636_ = lean_ctor_get_uint8(v_config_2510_, sizeof(void*)*1 + 1);
if (v_emptyType_2636_ == 0)
{
v___y_2623_ = v___y_2632_;
v___y_2624_ = v___y_2635_;
v___y_2625_ = v___y_2634_;
v___y_2626_ = v___y_2633_;
v___y_2627_ = v___y_2631_;
v___y_2628_ = v___x_2615_;
goto v___jp_2622_;
}
else
{
if (v___y_2630_ == 0)
{
v___y_2617_ = v___y_2632_;
v___y_2618_ = v___y_2635_;
v___y_2619_ = v___y_2634_;
v___y_2620_ = v___y_2633_;
v___y_2621_ = v___y_2631_;
goto v___jp_2616_;
}
else
{
v___y_2623_ = v___y_2632_;
v___y_2624_ = v___y_2635_;
v___y_2625_ = v___y_2634_;
v___y_2626_ = v___y_2633_;
v___y_2627_ = v___y_2631_;
v___y_2628_ = v___x_2615_;
goto v___jp_2622_;
}
}
}
v___jp_2637_:
{
if (v___y_2644_ == 0)
{
v___y_2630_ = v___y_2639_;
v___y_2631_ = v___y_2642_;
v___y_2632_ = v___y_2643_;
v___y_2633_ = v___y_2640_;
v___y_2634_ = v___y_2638_;
v___y_2635_ = v___y_2641_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2645_; 
lean_inc(v_val_2542_);
lean_inc(v_mvarId_2511_);
v___x_2645_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2511_, v_val_2542_, v___y_2643_, v___y_2640_, v___y_2638_, v___y_2641_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; uint8_t v___x_2647_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = lean_unbox(v_a_2646_);
lean_dec(v_a_2646_);
if (v___x_2647_ == 0)
{
v___y_2630_ = v___y_2639_;
v___y_2631_ = v___y_2642_;
v___y_2632_ = v___y_2643_;
v___y_2633_ = v___y_2640_;
v___y_2634_ = v___y_2638_;
v___y_2635_ = v___y_2641_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec(v_val_2542_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v___x_2648_ = lean_box(v___x_2521_);
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v___x_2546_);
v_a_2528_ = v___x_2650_;
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v_val_2542_);
lean_del_object(v___x_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_mvarId_2511_);
lean_dec_ref(v_config_2510_);
v_a_2651_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2645_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2645_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_a_2528_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2529_);
v___x_2531_ = v___x_2525_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_snd_2523_);
v___x_2531_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
return v___x_2532_;
}
}
v___jp_2535_:
{
lean_object* v___x_2537_; size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2534_);
lean_ctor_set(v___x_2537_, 1, v_a_2536_);
v___x_2538_ = ((size_t)1ULL);
v___x_2539_ = lean_usize_add(v_i_2514_, v___x_2538_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2510_, v_mvarId_2511_, v_as_2512_, v_sz_2513_, v___x_2539_, v___x_2537_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
return v___x_2540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3193_, lean_object* v_mvarId_3194_, lean_object* v_as_3195_, lean_object* v_sz_3196_, lean_object* v_i_3197_, lean_object* v_b_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
size_t v_sz_boxed_3204_; size_t v_i_boxed_3205_; lean_object* v_res_3206_; 
v_sz_boxed_3204_ = lean_unbox_usize(v_sz_3196_);
lean_dec(v_sz_3196_);
v_i_boxed_3205_ = lean_unbox_usize(v_i_3197_);
lean_dec(v_i_3197_);
v_res_3206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3193_, v_mvarId_3194_, v_as_3195_, v_sz_boxed_3204_, v_i_boxed_3205_, v_b_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec_ref(v_as_3195_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3210_, lean_object* v_mvarId_3211_, lean_object* v_as_3212_, size_t v_sz_3213_, size_t v_i_3214_, lean_object* v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v___x_3221_; 
v___x_3221_ = lean_usize_dec_lt(v_i_3214_, v_sz_3213_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; 
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_b_3215_);
return v___x_3222_;
}
else
{
lean_object* v_snd_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3911_; 
v_snd_3223_ = lean_ctor_get(v_b_3215_, 1);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_b_3215_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; 
v_unused_3912_ = lean_ctor_get(v_b_3215_, 0);
lean_dec(v_unused_3912_);
v___x_3225_ = v_b_3215_;
v_isShared_3226_ = v_isSharedCheck_3911_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_snd_3223_);
lean_dec(v_b_3215_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3911_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v_a_3228_; lean_object* v___x_3234_; lean_object* v_a_3236_; lean_object* v_a_3241_; 
v___x_3234_ = lean_box(0);
v_a_3241_ = lean_array_uget(v_as_3212_, v_i_3214_);
if (lean_obj_tag(v_a_3241_) == 0)
{
lean_del_object(v___x_3225_);
v_a_3236_ = v_snd_3223_;
goto v___jp_3235_;
}
else
{
lean_object* v_val_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3910_; 
v_val_3242_ = lean_ctor_get(v_a_3241_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_a_3241_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3244_ = v_a_3241_;
v_isShared_3245_ = v_isSharedCheck_3910_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_val_3242_);
lean_dec(v_a_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3910_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___x_3288_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; uint8_t v___y_3316_; uint8_t v___x_3317_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; uint8_t v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3325_; lean_object* v___y_3326_; uint8_t v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; uint8_t v___y_3330_; uint8_t v___y_3332_; uint8_t v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3340_; lean_object* v___y_3341_; uint8_t v___y_3342_; lean_object* v___y_3343_; uint8_t v___y_3344_; lean_object* v___y_3345_; uint8_t v___y_3346_; 
v___x_3246_ = lean_box(0);
v___x_3288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3317_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3242_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3362_; uint8_t v___y_3364_; uint8_t v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3373_; lean_object* v___y_3374_; uint8_t v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; uint8_t v___y_3378_; lean_object* v___y_3379_; uint8_t v___y_3380_; lean_object* v___y_3383_; lean_object* v___y_3384_; uint8_t v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; uint8_t v___y_3388_; lean_object* v_a_3389_; lean_object* v___y_3393_; lean_object* v___y_3394_; uint8_t v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; uint8_t v___y_3398_; lean_object* v___y_3491_; lean_object* v___y_3492_; uint8_t v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; uint8_t v___y_3496_; uint8_t v___y_3497_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; uint8_t v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; uint8_t v___y_3505_; uint8_t v___y_3506_; lean_object* v___y_3509_; lean_object* v___y_3510_; uint8_t v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; uint8_t v___y_3514_; uint8_t v___y_3515_; lean_object* v___y_3528_; lean_object* v___y_3529_; uint8_t v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; uint8_t v___y_3533_; uint8_t v___y_3534_; uint8_t v___y_3536_; uint8_t v_isHEq_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3545_; lean_object* v___y_3546_; uint8_t v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v_isEq_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___x_3840_; 
v___x_3362_ = l_Lean_LocalDecl_type(v_val_3242_);
lean_inc_ref(v___x_3362_);
v___x_3840_ = l_Lean_Meta_matchNot_x3f(v___x_3362_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref(v___x_3840_);
if (lean_obj_tag(v_a_3841_) == 1)
{
lean_object* v_val_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3901_; 
v_val_3842_ = lean_ctor_get(v_a_3841_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_a_3841_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3844_ = v_a_3841_;
v_isShared_3845_ = v_isSharedCheck_3901_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_val_3842_);
lean_dec(v_a_3841_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3901_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3842_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref(v___x_3846_);
if (lean_obj_tag(v_a_3847_) == 1)
{
lean_object* v_val_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3892_; 
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec_ref(v_config_3210_);
v_val_3848_ = lean_ctor_get(v_a_3847_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_a_3847_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3850_ = v_a_3847_;
v_isShared_3851_ = v_isSharedCheck_3892_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_val_3848_);
lean_dec(v_a_3847_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3892_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; 
lean_inc(v_mvarId_3211_);
v___x_3852_ = l_Lean_MVarId_getType(v_mvarId_3211_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = l_Lean_LocalDecl_toExpr(v_val_3242_);
v___x_3855_ = l_Lean_mkFVar(v_val_3848_);
v___x_3856_ = l_Lean_Expr_app___override(v___x_3854_, v___x_3855_);
v___x_3857_ = l_Lean_Meta_mkFalseElim(v_a_3853_, v___x_3856_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3859_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref(v___x_3857_);
v___x_3859_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3211_, v_a_3858_, v___y_3217_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v___x_3860_; lean_object* v___x_3862_; 
lean_dec_ref(v___x_3859_);
v___x_3860_ = lean_box(v___x_3221_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 0, v___x_3860_);
v___x_3862_ = v___x_3850_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3863_; lean_object* v___x_3865_; 
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
lean_ctor_set(v___x_3863_, 1, v___x_3246_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set_tag(v___x_3844_, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3863_);
v___x_3865_ = v___x_3844_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
v_a_3228_ = v___x_3865_;
goto v___jp_3227_;
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_del_object(v___x_3850_);
lean_del_object(v___x_3844_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
v_a_3868_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3859_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3859_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_del_object(v___x_3850_);
lean_del_object(v___x_3844_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3876_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3857_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3857_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_del_object(v___x_3850_);
lean_dec(v_val_3848_);
lean_del_object(v___x_3844_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3884_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3852_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3852_);
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
else
{
lean_dec(v_a_3847_);
lean_del_object(v___x_3844_);
v___y_3704_ = v___y_3216_;
v___y_3705_ = v___y_3217_;
v___y_3706_ = v___y_3218_;
v___y_3707_ = v___y_3219_;
goto v___jp_3703_;
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_del_object(v___x_3844_);
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3893_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3846_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3846_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
else
{
lean_dec(v_a_3841_);
v___y_3704_ = v___y_3216_;
v___y_3705_ = v___y_3217_;
v___y_3706_ = v___y_3218_;
v___y_3707_ = v___y_3219_;
goto v___jp_3703_;
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3902_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3840_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3840_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
v___jp_3363_:
{
uint8_t v_genDiseq_3370_; 
v_genDiseq_3370_ = lean_ctor_get_uint8(v_config_3210_, sizeof(void*)*1 + 2);
if (v_genDiseq_3370_ == 0)
{
lean_dec_ref(v___x_3362_);
v___y_3340_ = v___y_3368_;
v___y_3341_ = v___y_3366_;
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3369_;
v___y_3344_ = v___y_3365_;
v___y_3345_ = v___y_3367_;
v___y_3346_ = v___x_3317_;
goto v___jp_3339_;
}
else
{
uint8_t v___x_3371_; 
v___x_3371_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3362_);
v___y_3340_ = v___y_3368_;
v___y_3341_ = v___y_3366_;
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3369_;
v___y_3344_ = v___y_3365_;
v___y_3345_ = v___y_3367_;
v___y_3346_ = v___x_3371_;
goto v___jp_3339_;
}
}
v___jp_3372_:
{
if (v___y_3380_ == 0)
{
lean_dec_ref(v___y_3379_);
v___y_3364_ = v___y_3375_;
v___y_3365_ = v___y_3378_;
v___y_3366_ = v___y_3377_;
v___y_3367_ = v___y_3374_;
v___y_3368_ = v___y_3373_;
v___y_3369_ = v___y_3376_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3381_; 
lean_dec_ref(v___x_3362_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v___x_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___y_3379_);
return v___x_3381_;
}
}
v___jp_3382_:
{
uint8_t v___x_3390_; 
v___x_3390_ = l_Lean_Exception_isInterrupt(v_a_3389_);
if (v___x_3390_ == 0)
{
uint8_t v___x_3391_; 
lean_inc_ref(v_a_3389_);
v___x_3391_ = l_Lean_Exception_isRuntime(v_a_3389_);
v___y_3373_ = v___y_3384_;
v___y_3374_ = v___y_3383_;
v___y_3375_ = v___y_3385_;
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v_a_3389_;
v___y_3380_ = v___x_3391_;
goto v___jp_3372_;
}
else
{
v___y_3373_ = v___y_3384_;
v___y_3374_ = v___y_3383_;
v___y_3375_ = v___y_3385_;
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v_a_3389_;
v___y_3380_ = v___x_3390_;
goto v___jp_3372_;
}
}
v___jp_3392_:
{
lean_object* v___x_3399_; 
lean_inc_ref(v___x_3362_);
v___x_3399_ = l_Lean_Meta_mkDecide(v___x_3362_, v___y_3397_, v___y_3394_, v___y_3393_, v___y_3396_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3401_; uint8_t v_foApprox_3402_; uint8_t v_ctxApprox_3403_; uint8_t v_quasiPatternApprox_3404_; uint8_t v_constApprox_3405_; uint8_t v_isDefEqStuckEx_3406_; uint8_t v_unificationHints_3407_; uint8_t v_proofIrrelevance_3408_; uint8_t v_assignSyntheticOpaque_3409_; uint8_t v_offsetCnstrs_3410_; uint8_t v_etaStruct_3411_; uint8_t v_univApprox_3412_; uint8_t v_iota_3413_; uint8_t v_beta_3414_; uint8_t v_proj_3415_; uint8_t v_zeta_3416_; uint8_t v_zetaDelta_3417_; uint8_t v_zetaUnused_3418_; uint8_t v_zetaHave_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3488_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref(v___x_3399_);
v___x_3401_ = l_Lean_Meta_Context_config(v___y_3397_);
v_foApprox_3402_ = lean_ctor_get_uint8(v___x_3401_, 0);
v_ctxApprox_3403_ = lean_ctor_get_uint8(v___x_3401_, 1);
v_quasiPatternApprox_3404_ = lean_ctor_get_uint8(v___x_3401_, 2);
v_constApprox_3405_ = lean_ctor_get_uint8(v___x_3401_, 3);
v_isDefEqStuckEx_3406_ = lean_ctor_get_uint8(v___x_3401_, 4);
v_unificationHints_3407_ = lean_ctor_get_uint8(v___x_3401_, 5);
v_proofIrrelevance_3408_ = lean_ctor_get_uint8(v___x_3401_, 6);
v_assignSyntheticOpaque_3409_ = lean_ctor_get_uint8(v___x_3401_, 7);
v_offsetCnstrs_3410_ = lean_ctor_get_uint8(v___x_3401_, 8);
v_etaStruct_3411_ = lean_ctor_get_uint8(v___x_3401_, 10);
v_univApprox_3412_ = lean_ctor_get_uint8(v___x_3401_, 11);
v_iota_3413_ = lean_ctor_get_uint8(v___x_3401_, 12);
v_beta_3414_ = lean_ctor_get_uint8(v___x_3401_, 13);
v_proj_3415_ = lean_ctor_get_uint8(v___x_3401_, 14);
v_zeta_3416_ = lean_ctor_get_uint8(v___x_3401_, 15);
v_zetaDelta_3417_ = lean_ctor_get_uint8(v___x_3401_, 16);
v_zetaUnused_3418_ = lean_ctor_get_uint8(v___x_3401_, 17);
v_zetaHave_3419_ = lean_ctor_get_uint8(v___x_3401_, 18);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3421_ = v___x_3401_;
v_isShared_3422_ = v_isSharedCheck_3488_;
goto v_resetjp_3420_;
}
else
{
lean_dec(v___x_3401_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3488_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
uint8_t v_trackZetaDelta_3423_; lean_object* v_zetaDeltaSet_3424_; lean_object* v_lctx_3425_; lean_object* v_localInstances_3426_; lean_object* v_defEqCtx_x3f_3427_; lean_object* v_synthPendingDepth_3428_; lean_object* v_canUnfold_x3f_3429_; uint8_t v_univApprox_3430_; uint8_t v_inTypeClassResolution_3431_; uint8_t v_cacheInferType_3432_; uint8_t v___x_3433_; lean_object* v_config_3435_; 
v_trackZetaDelta_3423_ = lean_ctor_get_uint8(v___y_3397_, sizeof(void*)*7);
v_zetaDeltaSet_3424_ = lean_ctor_get(v___y_3397_, 1);
v_lctx_3425_ = lean_ctor_get(v___y_3397_, 2);
v_localInstances_3426_ = lean_ctor_get(v___y_3397_, 3);
v_defEqCtx_x3f_3427_ = lean_ctor_get(v___y_3397_, 4);
v_synthPendingDepth_3428_ = lean_ctor_get(v___y_3397_, 5);
v_canUnfold_x3f_3429_ = lean_ctor_get(v___y_3397_, 6);
v_univApprox_3430_ = lean_ctor_get_uint8(v___y_3397_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3431_ = lean_ctor_get_uint8(v___y_3397_, sizeof(void*)*7 + 2);
v_cacheInferType_3432_ = lean_ctor_get_uint8(v___y_3397_, sizeof(void*)*7 + 3);
v___x_3433_ = 1;
if (v_isShared_3422_ == 0)
{
v_config_3435_ = v___x_3421_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 0, v_foApprox_3402_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 1, v_ctxApprox_3403_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 2, v_quasiPatternApprox_3404_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 3, v_constApprox_3405_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 4, v_isDefEqStuckEx_3406_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 5, v_unificationHints_3407_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 6, v_proofIrrelevance_3408_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 7, v_assignSyntheticOpaque_3409_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 8, v_offsetCnstrs_3410_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 10, v_etaStruct_3411_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 11, v_univApprox_3412_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 12, v_iota_3413_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 13, v_beta_3414_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 14, v_proj_3415_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 15, v_zeta_3416_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 16, v_zetaDelta_3417_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 17, v_zetaUnused_3418_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, 18, v_zetaHave_3419_);
v_config_3435_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
uint64_t v___x_3436_; uint64_t v___x_3437_; uint64_t v___x_3438_; uint64_t v___x_3439_; uint64_t v___x_3440_; uint64_t v_key_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_ctor_set_uint8(v_config_3435_, 9, v___x_3433_);
v___x_3436_ = l_Lean_Meta_Context_configKey(v___y_3397_);
v___x_3437_ = 2ULL;
v___x_3438_ = lean_uint64_shift_right(v___x_3436_, v___x_3437_);
v___x_3439_ = lean_uint64_shift_left(v___x_3438_, v___x_3437_);
v___x_3440_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_3441_ = lean_uint64_lor(v___x_3439_, v___x_3440_);
v___x_3442_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3442_, 0, v_config_3435_);
lean_ctor_set_uint64(v___x_3442_, sizeof(void*)*1, v_key_3441_);
lean_inc(v_canUnfold_x3f_3429_);
lean_inc(v_synthPendingDepth_3428_);
lean_inc(v_defEqCtx_x3f_3427_);
lean_inc_ref(v_localInstances_3426_);
lean_inc_ref(v_lctx_3425_);
lean_inc(v_zetaDeltaSet_3424_);
v___x_3443_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
lean_ctor_set(v___x_3443_, 1, v_zetaDeltaSet_3424_);
lean_ctor_set(v___x_3443_, 2, v_lctx_3425_);
lean_ctor_set(v___x_3443_, 3, v_localInstances_3426_);
lean_ctor_set(v___x_3443_, 4, v_defEqCtx_x3f_3427_);
lean_ctor_set(v___x_3443_, 5, v_synthPendingDepth_3428_);
lean_ctor_set(v___x_3443_, 6, v_canUnfold_x3f_3429_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*7, v_trackZetaDelta_3423_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*7 + 1, v_univApprox_3430_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3431_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*7 + 3, v_cacheInferType_3432_);
lean_inc(v___y_3396_);
lean_inc_ref(v___y_3393_);
lean_inc(v___y_3394_);
lean_inc(v_a_3400_);
v___x_3444_ = lean_whnf(v_a_3400_, v___x_3443_, v___y_3394_, v___y_3393_, v___y_3396_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v___x_3444_);
v___x_3446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_3447_ = l_Lean_Expr_isConstOf(v_a_3445_, v___x_3446_);
lean_dec(v_a_3445_);
if (v___x_3447_ == 0)
{
lean_dec(v_a_3400_);
v___y_3364_ = v___y_3395_;
v___y_3365_ = v___y_3398_;
v___y_3366_ = v___y_3397_;
v___y_3367_ = v___y_3394_;
v___y_3368_ = v___y_3393_;
v___y_3369_ = v___y_3396_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3448_; 
lean_inc(v_a_3400_);
v___x_3448_ = l_Lean_Meta_mkEqRefl(v_a_3400_, v___y_3397_, v___y_3394_, v___y_3393_, v___y_3396_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3450_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref(v___x_3448_);
lean_inc(v_mvarId_3211_);
v___x_3450_ = l_Lean_MVarId_getType(v_mvarId_3211_, v___y_3397_, v___y_3394_, v___y_3393_, v___y_3396_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v_nargs_3452_; lean_object* v___x_3453_; lean_object* v_dummy_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref(v___x_3450_);
v_nargs_3452_ = l_Lean_Expr_getAppNumArgs(v_a_3400_);
v___x_3453_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_3454_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_3452_);
v___x_3455_ = lean_mk_array(v_nargs_3452_, v_dummy_3454_);
v___x_3456_ = lean_unsigned_to_nat(1u);
v___x_3457_ = lean_nat_sub(v_nargs_3452_, v___x_3456_);
lean_dec(v_nargs_3452_);
v___x_3458_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3400_, v___x_3455_, v___x_3457_);
v___x_3459_ = lean_array_push(v___x_3458_, v_a_3449_);
v___x_3460_ = l_Lean_mkAppN(v___x_3453_, v___x_3459_);
lean_dec_ref(v___x_3459_);
lean_inc(v_val_3242_);
v___x_3461_ = l_Lean_LocalDecl_toExpr(v_val_3242_);
v___x_3462_ = l_Lean_Meta_mkAbsurd(v_a_3451_, v___x_3461_, v___x_3460_, v___y_3397_, v___y_3394_, v___y_3393_, v___y_3396_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3482_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3482_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3482_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; 
lean_inc(v_mvarId_3211_);
v___x_3467_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3211_, v_a_3463_, v___y_3394_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v___x_3362_);
lean_dec(v_val_3242_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v___x_3467_, 0);
lean_dec(v_unused_3480_);
v___x_3469_ = v___x_3467_;
v_isShared_3470_ = v_isSharedCheck_3479_;
goto v_resetjp_3468_;
}
else
{
lean_dec(v___x_3467_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3479_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_box(v___x_3221_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set_tag(v___x_3469_, 1);
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3246_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3474_);
v___x_3476_ = v___x_3465_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
v_a_3228_ = v___x_3476_;
goto v___jp_3227_;
}
}
}
}
else
{
lean_object* v_a_3481_; 
lean_del_object(v___x_3465_);
v_a_3481_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___x_3467_);
v___y_3383_ = v___y_3394_;
v___y_3384_ = v___y_3393_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v___y_3388_ = v___y_3398_;
v_a_3389_ = v_a_3481_;
goto v___jp_3382_;
}
}
}
else
{
lean_object* v_a_3483_; 
v_a_3483_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3483_);
lean_dec_ref(v___x_3462_);
v___y_3383_ = v___y_3394_;
v___y_3384_ = v___y_3393_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v___y_3388_ = v___y_3398_;
v_a_3389_ = v_a_3483_;
goto v___jp_3382_;
}
}
else
{
lean_object* v_a_3484_; 
lean_dec(v_a_3449_);
lean_dec(v_a_3400_);
v_a_3484_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3484_);
lean_dec_ref(v___x_3450_);
v___y_3383_ = v___y_3394_;
v___y_3384_ = v___y_3393_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v___y_3388_ = v___y_3398_;
v_a_3389_ = v_a_3484_;
goto v___jp_3382_;
}
}
else
{
lean_object* v_a_3485_; 
lean_dec(v_a_3400_);
v_a_3485_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3485_);
lean_dec_ref(v___x_3448_);
v___y_3383_ = v___y_3394_;
v___y_3384_ = v___y_3393_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v___y_3388_ = v___y_3398_;
v_a_3389_ = v_a_3485_;
goto v___jp_3382_;
}
}
}
else
{
lean_object* v_a_3486_; 
lean_dec(v_a_3400_);
v_a_3486_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3486_);
lean_dec_ref(v___x_3444_);
v___y_3383_ = v___y_3394_;
v___y_3384_ = v___y_3393_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v___y_3388_ = v___y_3398_;
v_a_3389_ = v_a_3486_;
goto v___jp_3382_;
}
}
}
}
else
{
lean_object* v_a_3489_; 
v_a_3489_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3489_);
lean_dec_ref(v___x_3399_);
v___y_3383_ = v___y_3394_;
v___y_3384_ = v___y_3393_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3396_;
v___y_3387_ = v___y_3397_;
v___y_3388_ = v___y_3398_;
v_a_3389_ = v_a_3489_;
goto v___jp_3382_;
}
}
v___jp_3490_:
{
if (v___y_3497_ == 0)
{
v___y_3364_ = v___y_3493_;
v___y_3365_ = v___y_3496_;
v___y_3366_ = v___y_3495_;
v___y_3367_ = v___y_3492_;
v___y_3368_ = v___y_3491_;
v___y_3369_ = v___y_3494_;
goto v___jp_3363_;
}
else
{
v___y_3393_ = v___y_3491_;
v___y_3394_ = v___y_3492_;
v___y_3395_ = v___y_3493_;
v___y_3396_ = v___y_3494_;
v___y_3397_ = v___y_3495_;
v___y_3398_ = v___y_3496_;
goto v___jp_3392_;
}
}
v___jp_3498_:
{
if (v___y_3506_ == 0)
{
lean_dec_ref(v___y_3499_);
v___y_3491_ = v___y_3501_;
v___y_3492_ = v___y_3500_;
v___y_3493_ = v___y_3502_;
v___y_3494_ = v___y_3503_;
v___y_3495_ = v___y_3504_;
v___y_3496_ = v___y_3505_;
v___y_3497_ = v___x_3317_;
goto v___jp_3490_;
}
else
{
uint8_t v___x_3507_; 
v___x_3507_ = l_Lean_Expr_hasFVar(v___y_3499_);
lean_dec_ref(v___y_3499_);
if (v___x_3507_ == 0)
{
v___y_3393_ = v___y_3501_;
v___y_3394_ = v___y_3500_;
v___y_3395_ = v___y_3502_;
v___y_3396_ = v___y_3503_;
v___y_3397_ = v___y_3504_;
v___y_3398_ = v___y_3505_;
goto v___jp_3392_;
}
else
{
v___y_3491_ = v___y_3501_;
v___y_3492_ = v___y_3500_;
v___y_3493_ = v___y_3502_;
v___y_3494_ = v___y_3503_;
v___y_3495_ = v___y_3504_;
v___y_3496_ = v___y_3505_;
v___y_3497_ = v___x_3317_;
goto v___jp_3490_;
}
}
}
v___jp_3508_:
{
lean_object* v___x_3516_; 
lean_inc_ref(v___x_3362_);
v___x_3516_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3362_, v___y_3510_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; uint8_t v___x_3518_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref(v___x_3516_);
v___x_3518_ = l_Lean_Expr_hasMVar(v_a_3517_);
if (v___x_3518_ == 0)
{
v___y_3499_ = v_a_3517_;
v___y_3500_ = v___y_3510_;
v___y_3501_ = v___y_3509_;
v___y_3502_ = v___y_3511_;
v___y_3503_ = v___y_3512_;
v___y_3504_ = v___y_3513_;
v___y_3505_ = v___y_3514_;
v___y_3506_ = v___y_3515_;
goto v___jp_3498_;
}
else
{
v___y_3499_ = v_a_3517_;
v___y_3500_ = v___y_3510_;
v___y_3501_ = v___y_3509_;
v___y_3502_ = v___y_3511_;
v___y_3503_ = v___y_3512_;
v___y_3504_ = v___y_3513_;
v___y_3505_ = v___y_3514_;
v___y_3506_ = v___x_3317_;
goto v___jp_3498_;
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec_ref(v___x_3362_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3519_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3516_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3516_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
v___jp_3527_:
{
if (v___y_3534_ == 0)
{
v___y_3364_ = v___y_3530_;
v___y_3365_ = v___y_3533_;
v___y_3366_ = v___y_3532_;
v___y_3367_ = v___y_3529_;
v___y_3368_ = v___y_3528_;
v___y_3369_ = v___y_3531_;
goto v___jp_3363_;
}
else
{
v___y_3509_ = v___y_3528_;
v___y_3510_ = v___y_3529_;
v___y_3511_ = v___y_3530_;
v___y_3512_ = v___y_3531_;
v___y_3513_ = v___y_3532_;
v___y_3514_ = v___y_3533_;
v___y_3515_ = v___y_3534_;
goto v___jp_3508_;
}
}
v___jp_3535_:
{
uint8_t v_useDecide_3542_; 
v_useDecide_3542_ = lean_ctor_get_uint8(v_config_3210_, sizeof(void*)*1);
if (v_useDecide_3542_ == 0)
{
v___y_3528_ = v___y_3540_;
v___y_3529_ = v___y_3539_;
v___y_3530_ = v___y_3536_;
v___y_3531_ = v___y_3541_;
v___y_3532_ = v___y_3538_;
v___y_3533_ = v_isHEq_3537_;
v___y_3534_ = v___x_3317_;
goto v___jp_3527_;
}
else
{
uint8_t v___x_3543_; 
v___x_3543_ = l_Lean_Expr_hasFVar(v___x_3362_);
if (v___x_3543_ == 0)
{
v___y_3509_ = v___y_3540_;
v___y_3510_ = v___y_3539_;
v___y_3511_ = v___y_3536_;
v___y_3512_ = v___y_3541_;
v___y_3513_ = v___y_3538_;
v___y_3514_ = v_isHEq_3537_;
v___y_3515_ = v_useDecide_3542_;
goto v___jp_3508_;
}
else
{
v___y_3528_ = v___y_3540_;
v___y_3529_ = v___y_3539_;
v___y_3530_ = v___y_3536_;
v___y_3531_ = v___y_3541_;
v___y_3532_ = v___y_3538_;
v___y_3533_ = v_isHEq_3537_;
v___y_3534_ = v___x_3317_;
goto v___jp_3527_;
}
}
}
v___jp_3544_:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_Meta_isExprDefEq(v___y_3551_, v___y_3549_, v___y_3546_, v___y_3545_, v___y_3550_, v___y_3548_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; uint8_t v___x_3554_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = lean_unbox(v_a_3553_);
lean_dec(v_a_3553_);
if (v___x_3554_ == 0)
{
v___y_3536_ = v___y_3547_;
v_isHEq_3537_ = v___x_3221_;
v___y_3538_ = v___y_3546_;
v___y_3539_ = v___y_3545_;
v___y_3540_ = v___y_3550_;
v___y_3541_ = v___y_3548_;
goto v___jp_3535_;
}
else
{
lean_object* v___x_3555_; 
lean_dec_ref(v___x_3362_);
lean_dec_ref(v_config_3210_);
lean_inc(v_mvarId_3211_);
v___x_3555_ = l_Lean_MVarId_getType(v_mvarId_3211_, v___y_3546_, v___y_3545_, v___y_3550_, v___y_3548_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = l_Lean_LocalDecl_toExpr(v_val_3242_);
v___x_3558_ = l_Lean_Meta_mkEqOfHEq(v___x_3557_, v___x_3221_, v___y_3546_, v___y_3545_, v___y_3550_, v___y_3548_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3560_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref(v___x_3558_);
v___x_3560_ = l_Lean_Meta_mkNoConfusion(v_a_3556_, v_a_3559_, v___y_3546_, v___y_3545_, v___y_3550_, v___y_3548_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref(v___x_3560_);
v___x_3562_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3211_, v_a_3561_, v___y_3545_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec_ref(v___x_3562_);
v___x_3563_ = lean_box(v___x_3221_);
v___x_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
v___x_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
lean_ctor_set(v___x_3565_, 1, v___x_3246_);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
v_a_3228_ = v___x_3566_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
v_a_3567_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3562_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3562_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3575_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3560_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3560_);
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
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v_a_3556_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3583_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3558_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3558_);
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
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
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
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec_ref(v___x_3362_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3599_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3552_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3552_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
v___jp_3607_:
{
lean_object* v___x_3613_; 
lean_inc_ref(v___x_3362_);
v___x_3613_ = l_Lean_Meta_matchHEq_x3f(v___x_3362_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref(v___x_3613_);
if (lean_obj_tag(v_a_3614_) == 1)
{
lean_object* v_val_3615_; lean_object* v_snd_3616_; lean_object* v_snd_3617_; lean_object* v_fst_3618_; lean_object* v_fst_3619_; lean_object* v_fst_3620_; lean_object* v_snd_3621_; lean_object* v___x_3622_; 
v_val_3615_ = lean_ctor_get(v_a_3614_, 0);
lean_inc(v_val_3615_);
lean_dec_ref(v_a_3614_);
v_snd_3616_ = lean_ctor_get(v_val_3615_, 1);
lean_inc(v_snd_3616_);
v_snd_3617_ = lean_ctor_get(v_snd_3616_, 1);
lean_inc(v_snd_3617_);
v_fst_3618_ = lean_ctor_get(v_val_3615_, 0);
lean_inc(v_fst_3618_);
lean_dec(v_val_3615_);
v_fst_3619_ = lean_ctor_get(v_snd_3616_, 0);
lean_inc(v_fst_3619_);
lean_dec(v_snd_3616_);
v_fst_3620_ = lean_ctor_get(v_snd_3617_, 0);
lean_inc(v_fst_3620_);
v_snd_3621_ = lean_ctor_get(v_snd_3617_, 1);
lean_inc(v_snd_3621_);
lean_dec(v_snd_3617_);
v___x_3622_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3619_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref(v___x_3622_);
if (lean_obj_tag(v_a_3623_) == 1)
{
lean_object* v_val_3624_; lean_object* v___x_3625_; 
v_val_3624_ = lean_ctor_get(v_a_3623_, 0);
lean_inc(v_val_3624_);
lean_dec_ref(v_a_3623_);
v___x_3625_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3621_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref(v___x_3625_);
if (lean_obj_tag(v_a_3626_) == 1)
{
lean_object* v_toConstantVal_3627_; lean_object* v_val_3628_; lean_object* v_toConstantVal_3629_; lean_object* v_name_3630_; lean_object* v_name_3631_; uint8_t v___x_3632_; 
v_toConstantVal_3627_ = lean_ctor_get(v_val_3624_, 0);
lean_inc_ref(v_toConstantVal_3627_);
lean_dec(v_val_3624_);
v_val_3628_ = lean_ctor_get(v_a_3626_, 0);
lean_inc(v_val_3628_);
lean_dec_ref(v_a_3626_);
v_toConstantVal_3629_ = lean_ctor_get(v_val_3628_, 0);
lean_inc_ref(v_toConstantVal_3629_);
lean_dec(v_val_3628_);
v_name_3630_ = lean_ctor_get(v_toConstantVal_3627_, 0);
lean_inc(v_name_3630_);
lean_dec_ref(v_toConstantVal_3627_);
v_name_3631_ = lean_ctor_get(v_toConstantVal_3629_, 0);
lean_inc(v_name_3631_);
lean_dec_ref(v_toConstantVal_3629_);
v___x_3632_ = lean_name_eq(v_name_3630_, v_name_3631_);
lean_dec(v_name_3631_);
lean_dec(v_name_3630_);
if (v___x_3632_ == 0)
{
v___y_3545_ = v___y_3610_;
v___y_3546_ = v___y_3609_;
v___y_3547_ = v_isEq_3608_;
v___y_3548_ = v___y_3612_;
v___y_3549_ = v_fst_3620_;
v___y_3550_ = v___y_3611_;
v___y_3551_ = v_fst_3618_;
goto v___jp_3544_;
}
else
{
if (v___x_3317_ == 0)
{
lean_dec(v_fst_3620_);
lean_dec(v_fst_3618_);
v___y_3536_ = v_isEq_3608_;
v_isHEq_3537_ = v___x_3221_;
v___y_3538_ = v___y_3609_;
v___y_3539_ = v___y_3610_;
v___y_3540_ = v___y_3611_;
v___y_3541_ = v___y_3612_;
goto v___jp_3535_;
}
else
{
v___y_3545_ = v___y_3610_;
v___y_3546_ = v___y_3609_;
v___y_3547_ = v_isEq_3608_;
v___y_3548_ = v___y_3612_;
v___y_3549_ = v_fst_3620_;
v___y_3550_ = v___y_3611_;
v___y_3551_ = v_fst_3618_;
goto v___jp_3544_;
}
}
}
else
{
lean_dec(v_a_3626_);
lean_dec(v_val_3624_);
lean_dec(v_fst_3620_);
lean_dec(v_fst_3618_);
v___y_3536_ = v_isEq_3608_;
v_isHEq_3537_ = v___x_3221_;
v___y_3538_ = v___y_3609_;
v___y_3539_ = v___y_3610_;
v___y_3540_ = v___y_3611_;
v___y_3541_ = v___y_3612_;
goto v___jp_3535_;
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v_val_3624_);
lean_dec(v_fst_3620_);
lean_dec(v_fst_3618_);
lean_dec_ref(v___x_3362_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3633_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3625_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3625_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
else
{
lean_dec(v_a_3623_);
lean_dec(v_snd_3621_);
lean_dec(v_fst_3620_);
lean_dec(v_fst_3618_);
v___y_3536_ = v_isEq_3608_;
v_isHEq_3537_ = v___x_3221_;
v___y_3538_ = v___y_3609_;
v___y_3539_ = v___y_3610_;
v___y_3540_ = v___y_3611_;
v___y_3541_ = v___y_3612_;
goto v___jp_3535_;
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_dec(v_snd_3621_);
lean_dec(v_fst_3620_);
lean_dec(v_fst_3618_);
lean_dec_ref(v___x_3362_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3641_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3622_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3622_);
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
else
{
lean_dec(v_a_3614_);
v___y_3536_ = v_isEq_3608_;
v_isHEq_3537_ = v___x_3317_;
v___y_3538_ = v___y_3609_;
v___y_3539_ = v___y_3610_;
v___y_3540_ = v___y_3611_;
v___y_3541_ = v___y_3612_;
goto v___jp_3535_;
}
}
else
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
lean_dec_ref(v___x_3362_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3649_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3613_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3613_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
v___jp_3657_:
{
lean_object* v___x_3662_; 
lean_inc_ref(v___x_3362_);
v___x_3662_ = l_Lean_Meta_matchEq_x3f(v___x_3362_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref(v___x_3662_);
if (lean_obj_tag(v_a_3663_) == 1)
{
lean_object* v_val_3664_; lean_object* v_snd_3665_; lean_object* v_fst_3666_; lean_object* v_snd_3667_; lean_object* v___x_3668_; 
v_val_3664_ = lean_ctor_get(v_a_3663_, 0);
lean_inc(v_val_3664_);
lean_dec_ref(v_a_3663_);
v_snd_3665_ = lean_ctor_get(v_val_3664_, 1);
lean_inc(v_snd_3665_);
lean_dec(v_val_3664_);
v_fst_3666_ = lean_ctor_get(v_snd_3665_, 0);
lean_inc(v_fst_3666_);
v_snd_3667_ = lean_ctor_get(v_snd_3665_, 1);
lean_inc(v_snd_3667_);
lean_dec(v_snd_3665_);
v___x_3668_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3666_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref(v___x_3668_);
if (lean_obj_tag(v_a_3669_) == 1)
{
lean_object* v_val_3670_; lean_object* v___x_3671_; 
v_val_3670_ = lean_ctor_get(v_a_3669_, 0);
lean_inc(v_val_3670_);
lean_dec_ref(v_a_3669_);
v___x_3671_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3667_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref(v___x_3671_);
if (lean_obj_tag(v_a_3672_) == 1)
{
lean_object* v_toConstantVal_3673_; lean_object* v_val_3674_; lean_object* v_toConstantVal_3675_; lean_object* v_name_3676_; lean_object* v_name_3677_; uint8_t v___x_3678_; 
v_toConstantVal_3673_ = lean_ctor_get(v_val_3670_, 0);
lean_inc_ref(v_toConstantVal_3673_);
lean_dec(v_val_3670_);
v_val_3674_ = lean_ctor_get(v_a_3672_, 0);
lean_inc(v_val_3674_);
lean_dec_ref(v_a_3672_);
v_toConstantVal_3675_ = lean_ctor_get(v_val_3674_, 0);
lean_inc_ref(v_toConstantVal_3675_);
lean_dec(v_val_3674_);
v_name_3676_ = lean_ctor_get(v_toConstantVal_3673_, 0);
lean_inc(v_name_3676_);
lean_dec_ref(v_toConstantVal_3673_);
v_name_3677_ = lean_ctor_get(v_toConstantVal_3675_, 0);
lean_inc(v_name_3677_);
lean_dec_ref(v_toConstantVal_3675_);
v___x_3678_ = lean_name_eq(v_name_3676_, v_name_3677_);
lean_dec(v_name_3677_);
lean_dec(v_name_3676_);
if (v___x_3678_ == 0)
{
lean_dec_ref(v___x_3362_);
lean_dec_ref(v_config_3210_);
v___y_3248_ = v___y_3658_;
v___y_3249_ = v___y_3661_;
v___y_3250_ = v___y_3660_;
v___y_3251_ = v___y_3659_;
goto v___jp_3247_;
}
else
{
if (v___x_3317_ == 0)
{
lean_del_object(v___x_3244_);
v_isEq_3608_ = v___x_3221_;
v___y_3609_ = v___y_3658_;
v___y_3610_ = v___y_3659_;
v___y_3611_ = v___y_3660_;
v___y_3612_ = v___y_3661_;
goto v___jp_3607_;
}
else
{
lean_dec_ref(v___x_3362_);
lean_dec_ref(v_config_3210_);
v___y_3248_ = v___y_3658_;
v___y_3249_ = v___y_3661_;
v___y_3250_ = v___y_3660_;
v___y_3251_ = v___y_3659_;
goto v___jp_3247_;
}
}
}
else
{
lean_dec(v_a_3672_);
lean_dec(v_val_3670_);
lean_del_object(v___x_3244_);
v_isEq_3608_ = v___x_3221_;
v___y_3609_ = v___y_3658_;
v___y_3610_ = v___y_3659_;
v___y_3611_ = v___y_3660_;
v___y_3612_ = v___y_3661_;
goto v___jp_3607_;
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v_val_3670_);
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3679_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3671_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3671_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
else
{
lean_dec(v_a_3669_);
lean_dec(v_snd_3667_);
lean_del_object(v___x_3244_);
v_isEq_3608_ = v___x_3221_;
v___y_3609_ = v___y_3658_;
v___y_3610_ = v___y_3659_;
v___y_3611_ = v___y_3660_;
v___y_3612_ = v___y_3661_;
goto v___jp_3607_;
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v_snd_3667_);
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3687_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3668_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3668_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
lean_dec(v_a_3663_);
lean_del_object(v___x_3244_);
v_isEq_3608_ = v___x_3317_;
v___y_3609_ = v___y_3658_;
v___y_3610_ = v___y_3659_;
v___y_3611_ = v___y_3660_;
v___y_3612_ = v___y_3661_;
goto v___jp_3607_;
}
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3695_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3662_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3662_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
v___jp_3703_:
{
lean_object* v___x_3708_; 
lean_inc_ref(v___x_3362_);
v___x_3708_ = l_refutableHasNotBit_x3f(v___x_3362_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref(v___x_3708_);
if (lean_obj_tag(v_a_3709_) == 1)
{
lean_object* v_val_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec_ref(v_config_3210_);
v_val_3710_ = lean_ctor_get(v_a_3709_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v_a_3709_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3712_ = v_a_3709_;
v_isShared_3713_ = v_isSharedCheck_3750_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_val_3710_);
lean_dec(v_a_3709_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3750_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3714_; 
lean_inc(v_mvarId_3211_);
v___x_3714_ = l_Lean_MVarId_getType(v_mvarId_3211_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_a_3715_);
lean_dec_ref(v___x_3714_);
v___x_3716_ = l_Lean_LocalDecl_toExpr(v_val_3242_);
v___x_3717_ = l_Lean_Meta_mkAbsurd(v_a_3715_, v_val_3710_, v___x_3716_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v___x_3719_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3211_, v_a_3718_, v___y_3705_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v___x_3720_; lean_object* v___x_3722_; 
lean_dec_ref(v___x_3719_);
v___x_3720_ = lean_box(v___x_3221_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3720_);
v___x_3722_ = v___x_3712_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set(v___x_3723_, 1, v___x_3246_);
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
v_a_3228_ = v___x_3724_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_del_object(v___x_3712_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
v_a_3726_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3719_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3719_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_del_object(v___x_3712_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3734_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3717_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3717_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_del_object(v___x_3712_);
lean_dec(v_val_3710_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3742_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3714_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3714_);
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
}
else
{
lean_object* v___x_3751_; 
lean_dec(v_a_3709_);
lean_inc_ref(v___x_3362_);
v___x_3751_ = l_Lean_Meta_matchNe_x3f(v___x_3362_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref(v___x_3751_);
if (lean_obj_tag(v_a_3752_) == 1)
{
lean_object* v_val_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3823_; 
v_val_3753_ = lean_ctor_get(v_a_3752_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_a_3752_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3755_ = v_a_3752_;
v_isShared_3756_ = v_isSharedCheck_3823_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_val_3753_);
lean_dec(v_a_3752_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3823_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v_snd_3757_; lean_object* v_fst_3758_; lean_object* v_snd_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3822_; 
v_snd_3757_ = lean_ctor_get(v_val_3753_, 1);
lean_inc(v_snd_3757_);
lean_dec(v_val_3753_);
v_fst_3758_ = lean_ctor_get(v_snd_3757_, 0);
v_snd_3759_ = lean_ctor_get(v_snd_3757_, 1);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_snd_3757_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3761_ = v_snd_3757_;
v_isShared_3762_ = v_isSharedCheck_3822_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_snd_3759_);
lean_inc(v_fst_3758_);
lean_dec(v_snd_3757_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3822_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3763_; 
lean_inc(v_fst_3758_);
v___x_3763_ = l_Lean_Meta_isExprDefEq(v_fst_3758_, v_snd_3759_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; uint8_t v___x_3765_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref(v___x_3763_);
v___x_3765_ = lean_unbox(v_a_3764_);
lean_dec(v_a_3764_);
if (v___x_3765_ == 0)
{
lean_del_object(v___x_3761_);
lean_dec(v_fst_3758_);
lean_del_object(v___x_3755_);
v___y_3658_ = v___y_3704_;
v___y_3659_ = v___y_3705_;
v___y_3660_ = v___y_3706_;
v___y_3661_ = v___y_3707_;
goto v___jp_3657_;
}
else
{
lean_object* v___x_3766_; 
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec_ref(v_config_3210_);
lean_inc(v_mvarId_3211_);
v___x_3766_ = l_Lean_MVarId_getType(v_mvarId_3211_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3768_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref(v___x_3766_);
v___x_3768_ = l_Lean_Meta_mkEqRefl(v_fst_3758_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_a_3769_);
lean_dec_ref(v___x_3768_);
v___x_3770_ = l_Lean_LocalDecl_toExpr(v_val_3242_);
v___x_3771_ = l_Lean_Meta_mkAbsurd(v_a_3767_, v_a_3769_, v___x_3770_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3773_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref(v___x_3771_);
v___x_3773_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3211_, v_a_3772_, v___y_3705_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
lean_dec_ref(v___x_3773_);
v___x_3774_ = lean_box(v___x_3221_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v___x_3774_);
v___x_3776_ = v___x_3755_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3778_; 
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 1, v___x_3246_);
lean_ctor_set(v___x_3761_, 0, v___x_3776_);
v___x_3778_ = v___x_3761_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v___x_3246_);
v___x_3778_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
v_a_3228_ = v___x_3779_;
goto v___jp_3227_;
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_del_object(v___x_3761_);
lean_del_object(v___x_3755_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
v_a_3782_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3773_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3773_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_del_object(v___x_3761_);
lean_del_object(v___x_3755_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3790_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3771_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3771_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec(v_a_3767_);
lean_del_object(v___x_3761_);
lean_del_object(v___x_3755_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3798_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3768_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3768_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_del_object(v___x_3761_);
lean_dec(v_fst_3758_);
lean_del_object(v___x_3755_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3806_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3766_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3766_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_del_object(v___x_3761_);
lean_dec(v_fst_3758_);
lean_del_object(v___x_3755_);
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3814_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3763_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3763_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3752_);
v___y_3658_ = v___y_3704_;
v___y_3659_ = v___y_3705_;
v___y_3660_ = v___y_3706_;
v___y_3661_ = v___y_3707_;
goto v___jp_3657_;
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3824_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3751_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3751_);
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
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref(v___x_3362_);
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3832_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3708_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3708_);
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
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
v_a_3236_ = v___x_3288_;
goto v___jp_3235_;
}
v___jp_3247_:
{
lean_object* v___x_3252_; 
lean_inc(v_mvarId_3211_);
v___x_3252_ = l_Lean_MVarId_getType(v_mvarId_3211_, v___y_3248_, v___y_3251_, v___y_3250_, v___y_3249_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref(v___x_3252_);
v___x_3254_ = l_Lean_LocalDecl_toExpr(v_val_3242_);
v___x_3255_ = l_Lean_Meta_mkNoConfusion(v_a_3253_, v___x_3254_, v___y_3248_, v___y_3251_, v___y_3250_, v___y_3249_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref(v___x_3255_);
v___x_3257_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3211_, v_a_3256_, v___y_3251_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
lean_dec_ref(v___x_3257_);
v___x_3258_ = lean_box(v___x_3221_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3258_);
v___x_3260_ = v___x_3244_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
lean_ctor_set(v___x_3261_, 1, v___x_3246_);
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
v_a_3228_ = v___x_3262_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_del_object(v___x_3244_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
v_a_3264_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3257_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3257_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_del_object(v___x_3244_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3272_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3255_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3255_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_del_object(v___x_3244_);
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
v_a_3280_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3252_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3252_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
v___jp_3289_:
{
lean_object* v_searchFuel_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_searchFuel_3294_ = lean_ctor_get(v_config_3210_, 0);
v___x_3295_ = l_Lean_LocalDecl_fvarId(v_val_3242_);
lean_dec(v_val_3242_);
lean_inc(v_searchFuel_3294_);
lean_inc(v_mvarId_3211_);
v___x_3296_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3211_, v___x_3295_, v_searchFuel_3294_, v___y_3292_, v___y_3291_, v___y_3293_, v___y_3290_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; uint8_t v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref(v___x_3296_);
v___x_3298_ = lean_unbox(v_a_3297_);
lean_dec(v_a_3297_);
if (v___x_3298_ == 0)
{
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
v_a_3236_ = v___x_3288_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v___x_3299_ = lean_box(v___x_3221_);
v___x_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3246_);
v___x_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
v_a_3228_ = v___x_3302_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3303_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3296_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3296_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
v___jp_3311_:
{
if (v___y_3316_ == 0)
{
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
v_a_3236_ = v___x_3288_;
goto v___jp_3235_;
}
else
{
v___y_3290_ = v___y_3312_;
v___y_3291_ = v___y_3313_;
v___y_3292_ = v___y_3314_;
v___y_3293_ = v___y_3315_;
goto v___jp_3289_;
}
}
v___jp_3318_:
{
if (v___y_3322_ == 0)
{
v___y_3290_ = v___y_3319_;
v___y_3291_ = v___y_3320_;
v___y_3292_ = v___y_3321_;
v___y_3293_ = v___y_3323_;
goto v___jp_3289_;
}
else
{
v___y_3312_ = v___y_3319_;
v___y_3313_ = v___y_3320_;
v___y_3314_ = v___y_3321_;
v___y_3315_ = v___y_3323_;
v___y_3316_ = v___x_3317_;
goto v___jp_3311_;
}
}
v___jp_3324_:
{
if (v___y_3330_ == 0)
{
v___y_3312_ = v___y_3325_;
v___y_3313_ = v___y_3326_;
v___y_3314_ = v___y_3328_;
v___y_3315_ = v___y_3329_;
v___y_3316_ = v___x_3317_;
goto v___jp_3311_;
}
else
{
v___y_3319_ = v___y_3325_;
v___y_3320_ = v___y_3326_;
v___y_3321_ = v___y_3328_;
v___y_3322_ = v___y_3327_;
v___y_3323_ = v___y_3329_;
goto v___jp_3318_;
}
}
v___jp_3331_:
{
uint8_t v_emptyType_3338_; 
v_emptyType_3338_ = lean_ctor_get_uint8(v_config_3210_, sizeof(void*)*1 + 1);
if (v_emptyType_3338_ == 0)
{
v___y_3325_ = v___y_3337_;
v___y_3326_ = v___y_3335_;
v___y_3327_ = v___y_3333_;
v___y_3328_ = v___y_3334_;
v___y_3329_ = v___y_3336_;
v___y_3330_ = v___x_3317_;
goto v___jp_3324_;
}
else
{
if (v___y_3332_ == 0)
{
v___y_3319_ = v___y_3337_;
v___y_3320_ = v___y_3335_;
v___y_3321_ = v___y_3334_;
v___y_3322_ = v___y_3333_;
v___y_3323_ = v___y_3336_;
goto v___jp_3318_;
}
else
{
v___y_3325_ = v___y_3337_;
v___y_3326_ = v___y_3335_;
v___y_3327_ = v___y_3333_;
v___y_3328_ = v___y_3334_;
v___y_3329_ = v___y_3336_;
v___y_3330_ = v___x_3317_;
goto v___jp_3324_;
}
}
}
v___jp_3339_:
{
if (v___y_3346_ == 0)
{
v___y_3332_ = v___y_3342_;
v___y_3333_ = v___y_3344_;
v___y_3334_ = v___y_3341_;
v___y_3335_ = v___y_3345_;
v___y_3336_ = v___y_3340_;
v___y_3337_ = v___y_3343_;
goto v___jp_3331_;
}
else
{
lean_object* v___x_3347_; 
lean_inc(v_val_3242_);
lean_inc(v_mvarId_3211_);
v___x_3347_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3211_, v_val_3242_, v___y_3341_, v___y_3345_, v___y_3340_, v___y_3343_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; uint8_t v___x_3349_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref(v___x_3347_);
v___x_3349_ = lean_unbox(v_a_3348_);
lean_dec(v_a_3348_);
if (v___x_3349_ == 0)
{
v___y_3332_ = v___y_3342_;
v___y_3333_ = v___y_3344_;
v___y_3334_ = v___y_3341_;
v___y_3335_ = v___y_3345_;
v___y_3336_ = v___y_3340_;
v___y_3337_ = v___y_3343_;
goto v___jp_3331_;
}
else
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec(v_val_3242_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v___x_3350_ = lean_box(v___x_3221_);
v___x_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
lean_ctor_set(v___x_3352_, 1, v___x_3246_);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
v_a_3228_ = v___x_3353_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec(v_val_3242_);
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
lean_dec(v_mvarId_3211_);
lean_dec_ref(v_config_3210_);
v_a_3354_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3347_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3347_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
}
}
}
v___jp_3227_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3229_, 0, v_a_3228_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3229_);
v___x_3231_ = v___x_3225_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_snd_3223_);
v___x_3231_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
return v___x_3232_;
}
}
v___jp_3235_:
{
lean_object* v___x_3237_; size_t v___x_3238_; size_t v___x_3239_; 
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3234_);
lean_ctor_set(v___x_3237_, 1, v_a_3236_);
v___x_3238_ = ((size_t)1ULL);
v___x_3239_ = lean_usize_add(v_i_3214_, v___x_3238_);
v_i_3214_ = v___x_3239_;
v_b_3215_ = v___x_3237_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3913_, lean_object* v_mvarId_3914_, lean_object* v_as_3915_, lean_object* v_sz_3916_, lean_object* v_i_3917_, lean_object* v_b_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
size_t v_sz_boxed_3924_; size_t v_i_boxed_3925_; lean_object* v_res_3926_; 
v_sz_boxed_3924_ = lean_unbox_usize(v_sz_3916_);
lean_dec(v_sz_3916_);
v_i_boxed_3925_ = lean_unbox_usize(v_i_3917_);
lean_dec(v_i_3917_);
v_res_3926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3913_, v_mvarId_3914_, v_as_3915_, v_sz_boxed_3924_, v_i_boxed_3925_, v_b_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v_as_3915_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3927_, lean_object* v_mvarId_3928_, lean_object* v_as_3929_, size_t v_sz_3930_, size_t v_i_3931_, lean_object* v_b_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
uint8_t v___x_3938_; 
v___x_3938_ = lean_usize_dec_lt(v_i_3931_, v_sz_3930_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; 
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v_b_3932_);
return v___x_3939_;
}
else
{
lean_object* v_snd_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_4628_; 
v_snd_3940_ = lean_ctor_get(v_b_3932_, 1);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_b_3932_);
if (v_isSharedCheck_4628_ == 0)
{
lean_object* v_unused_4629_; 
v_unused_4629_ = lean_ctor_get(v_b_3932_, 0);
lean_dec(v_unused_4629_);
v___x_3942_ = v_b_3932_;
v_isShared_3943_ = v_isSharedCheck_4628_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_snd_3940_);
lean_dec(v_b_3932_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_4628_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v_a_3945_; lean_object* v___x_3951_; lean_object* v_a_3953_; lean_object* v_a_3958_; 
v___x_3951_ = lean_box(0);
v_a_3958_ = lean_array_uget(v_as_3929_, v_i_3931_);
if (lean_obj_tag(v_a_3958_) == 0)
{
lean_del_object(v___x_3942_);
v_a_3953_ = v_snd_3940_;
goto v___jp_3952_;
}
else
{
lean_object* v_val_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_4627_; 
v_val_3959_ = lean_ctor_get(v_a_3958_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_a_3958_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_3961_ = v_a_3958_;
v_isShared_3962_ = v_isSharedCheck_4627_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_val_3959_);
lean_dec(v_a_3958_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_4627_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___x_4005_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; uint8_t v___y_4033_; uint8_t v___x_4034_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; uint8_t v___y_4040_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; uint8_t v___y_4046_; uint8_t v___y_4047_; uint8_t v___y_4049_; uint8_t v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; uint8_t v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; uint8_t v___y_4061_; lean_object* v___y_4062_; uint8_t v___y_4063_; 
v___x_3963_ = lean_box(0);
v___x_4005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_4034_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3959_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4079_; uint8_t v___y_4081_; uint8_t v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4090_; uint8_t v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; uint8_t v___y_4096_; uint8_t v___y_4097_; lean_object* v___y_4100_; uint8_t v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; uint8_t v___y_4105_; lean_object* v_a_4106_; lean_object* v___y_4110_; uint8_t v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; uint8_t v___y_4115_; lean_object* v___y_4208_; uint8_t v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; uint8_t v___y_4213_; uint8_t v___y_4214_; lean_object* v___y_4216_; uint8_t v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; uint8_t v___y_4222_; uint8_t v___y_4223_; lean_object* v___y_4226_; uint8_t v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; uint8_t v___y_4231_; uint8_t v___y_4232_; lean_object* v___y_4245_; uint8_t v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; uint8_t v___y_4250_; uint8_t v___y_4251_; uint8_t v___y_4253_; uint8_t v_isHEq_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4262_; lean_object* v___y_4263_; uint8_t v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; uint8_t v_isEq_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___x_4557_; 
v___x_4079_ = l_Lean_LocalDecl_type(v_val_3959_);
lean_inc_ref(v___x_4079_);
v___x_4557_ = l_Lean_Meta_matchNot_x3f(v___x_4079_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_a_4558_);
lean_dec_ref(v___x_4557_);
if (lean_obj_tag(v_a_4558_) == 1)
{
lean_object* v_val_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4618_; 
v_val_4559_ = lean_ctor_get(v_a_4558_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v_a_4558_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4561_ = v_a_4558_;
v_isShared_4562_ = v_isSharedCheck_4618_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_val_4559_);
lean_dec(v_a_4558_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4618_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4559_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref(v___x_4563_);
if (lean_obj_tag(v_a_4564_) == 1)
{
lean_object* v_val_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4609_; 
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec_ref(v_config_3927_);
v_val_4565_ = lean_ctor_get(v_a_4564_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v_a_4564_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4567_ = v_a_4564_;
v_isShared_4568_ = v_isSharedCheck_4609_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_val_4565_);
lean_dec(v_a_4564_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4609_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4569_; 
lean_inc(v_mvarId_3928_);
v___x_4569_ = l_Lean_MVarId_getType(v_mvarId_3928_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_a_4570_);
lean_dec_ref(v___x_4569_);
v___x_4571_ = l_Lean_LocalDecl_toExpr(v_val_3959_);
v___x_4572_ = l_Lean_mkFVar(v_val_4565_);
v___x_4573_ = l_Lean_Expr_app___override(v___x_4571_, v___x_4572_);
v___x_4574_ = l_Lean_Meta_mkFalseElim(v_a_4570_, v___x_4573_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v___x_4576_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref(v___x_4574_);
v___x_4576_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3928_, v_a_4575_, v___y_3934_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v___x_4577_; lean_object* v___x_4579_; 
lean_dec_ref(v___x_4576_);
v___x_4577_ = lean_box(v___x_3938_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 0, v___x_4577_);
v___x_4579_ = v___x_4567_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4577_);
v___x_4579_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
lean_object* v___x_4580_; lean_object* v___x_4582_; 
v___x_4580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v___x_3963_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set_tag(v___x_4561_, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4580_);
v___x_4582_ = v___x_4561_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4580_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
v_a_3945_ = v___x_4582_;
goto v___jp_3944_;
}
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_del_object(v___x_4567_);
lean_del_object(v___x_4561_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
v_a_4585_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4576_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4576_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_del_object(v___x_4567_);
lean_del_object(v___x_4561_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4593_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4574_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4574_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_del_object(v___x_4567_);
lean_dec(v_val_4565_);
lean_del_object(v___x_4561_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4601_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4569_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4569_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
else
{
lean_dec(v_a_4564_);
lean_del_object(v___x_4561_);
v___y_4421_ = v___y_3933_;
v___y_4422_ = v___y_3934_;
v___y_4423_ = v___y_3935_;
v___y_4424_ = v___y_3936_;
goto v___jp_4420_;
}
}
else
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
lean_del_object(v___x_4561_);
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4610_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___x_4563_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4563_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
}
}
else
{
lean_dec(v_a_4558_);
v___y_4421_ = v___y_3933_;
v___y_4422_ = v___y_3934_;
v___y_4423_ = v___y_3935_;
v___y_4424_ = v___y_3936_;
goto v___jp_4420_;
}
}
else
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4619_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___x_4557_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4557_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
v___jp_4080_:
{
uint8_t v_genDiseq_4087_; 
v_genDiseq_4087_ = lean_ctor_get_uint8(v_config_3927_, sizeof(void*)*1 + 2);
if (v_genDiseq_4087_ == 0)
{
lean_dec_ref(v___x_4079_);
v___y_4057_ = v___y_4081_;
v___y_4058_ = v___y_4085_;
v___y_4059_ = v___y_4083_;
v___y_4060_ = v___y_4086_;
v___y_4061_ = v___y_4082_;
v___y_4062_ = v___y_4084_;
v___y_4063_ = v___x_4034_;
goto v___jp_4056_;
}
else
{
uint8_t v___x_4088_; 
v___x_4088_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4079_);
v___y_4057_ = v___y_4081_;
v___y_4058_ = v___y_4085_;
v___y_4059_ = v___y_4083_;
v___y_4060_ = v___y_4086_;
v___y_4061_ = v___y_4082_;
v___y_4062_ = v___y_4084_;
v___y_4063_ = v___x_4088_;
goto v___jp_4056_;
}
}
v___jp_4089_:
{
if (v___y_4097_ == 0)
{
lean_dec_ref(v___y_4093_);
v___y_4081_ = v___y_4091_;
v___y_4082_ = v___y_4096_;
v___y_4083_ = v___y_4095_;
v___y_4084_ = v___y_4092_;
v___y_4085_ = v___y_4094_;
v___y_4086_ = v___y_4090_;
goto v___jp_4080_;
}
else
{
lean_object* v___x_4098_; 
lean_dec_ref(v___x_4079_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v___x_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___y_4093_);
return v___x_4098_;
}
}
v___jp_4099_:
{
uint8_t v___x_4107_; 
v___x_4107_ = l_Lean_Exception_isInterrupt(v_a_4106_);
if (v___x_4107_ == 0)
{
uint8_t v___x_4108_; 
lean_inc_ref(v_a_4106_);
v___x_4108_ = l_Lean_Exception_isRuntime(v_a_4106_);
v___y_4090_ = v___y_4100_;
v___y_4091_ = v___y_4101_;
v___y_4092_ = v___y_4102_;
v___y_4093_ = v_a_4106_;
v___y_4094_ = v___y_4103_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___y_4105_;
v___y_4097_ = v___x_4108_;
goto v___jp_4089_;
}
else
{
v___y_4090_ = v___y_4100_;
v___y_4091_ = v___y_4101_;
v___y_4092_ = v___y_4102_;
v___y_4093_ = v_a_4106_;
v___y_4094_ = v___y_4103_;
v___y_4095_ = v___y_4104_;
v___y_4096_ = v___y_4105_;
v___y_4097_ = v___x_4107_;
goto v___jp_4089_;
}
}
v___jp_4109_:
{
lean_object* v___x_4116_; 
lean_inc_ref(v___x_4079_);
v___x_4116_ = l_Lean_Meta_mkDecide(v___x_4079_, v___y_4114_, v___y_4112_, v___y_4113_, v___y_4110_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4118_; uint8_t v_foApprox_4119_; uint8_t v_ctxApprox_4120_; uint8_t v_quasiPatternApprox_4121_; uint8_t v_constApprox_4122_; uint8_t v_isDefEqStuckEx_4123_; uint8_t v_unificationHints_4124_; uint8_t v_proofIrrelevance_4125_; uint8_t v_assignSyntheticOpaque_4126_; uint8_t v_offsetCnstrs_4127_; uint8_t v_etaStruct_4128_; uint8_t v_univApprox_4129_; uint8_t v_iota_4130_; uint8_t v_beta_4131_; uint8_t v_proj_4132_; uint8_t v_zeta_4133_; uint8_t v_zetaDelta_4134_; uint8_t v_zetaUnused_4135_; uint8_t v_zetaHave_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4205_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref(v___x_4116_);
v___x_4118_ = l_Lean_Meta_Context_config(v___y_4114_);
v_foApprox_4119_ = lean_ctor_get_uint8(v___x_4118_, 0);
v_ctxApprox_4120_ = lean_ctor_get_uint8(v___x_4118_, 1);
v_quasiPatternApprox_4121_ = lean_ctor_get_uint8(v___x_4118_, 2);
v_constApprox_4122_ = lean_ctor_get_uint8(v___x_4118_, 3);
v_isDefEqStuckEx_4123_ = lean_ctor_get_uint8(v___x_4118_, 4);
v_unificationHints_4124_ = lean_ctor_get_uint8(v___x_4118_, 5);
v_proofIrrelevance_4125_ = lean_ctor_get_uint8(v___x_4118_, 6);
v_assignSyntheticOpaque_4126_ = lean_ctor_get_uint8(v___x_4118_, 7);
v_offsetCnstrs_4127_ = lean_ctor_get_uint8(v___x_4118_, 8);
v_etaStruct_4128_ = lean_ctor_get_uint8(v___x_4118_, 10);
v_univApprox_4129_ = lean_ctor_get_uint8(v___x_4118_, 11);
v_iota_4130_ = lean_ctor_get_uint8(v___x_4118_, 12);
v_beta_4131_ = lean_ctor_get_uint8(v___x_4118_, 13);
v_proj_4132_ = lean_ctor_get_uint8(v___x_4118_, 14);
v_zeta_4133_ = lean_ctor_get_uint8(v___x_4118_, 15);
v_zetaDelta_4134_ = lean_ctor_get_uint8(v___x_4118_, 16);
v_zetaUnused_4135_ = lean_ctor_get_uint8(v___x_4118_, 17);
v_zetaHave_4136_ = lean_ctor_get_uint8(v___x_4118_, 18);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4138_ = v___x_4118_;
v_isShared_4139_ = v_isSharedCheck_4205_;
goto v_resetjp_4137_;
}
else
{
lean_dec(v___x_4118_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4205_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
uint8_t v_trackZetaDelta_4140_; lean_object* v_zetaDeltaSet_4141_; lean_object* v_lctx_4142_; lean_object* v_localInstances_4143_; lean_object* v_defEqCtx_x3f_4144_; lean_object* v_synthPendingDepth_4145_; lean_object* v_canUnfold_x3f_4146_; uint8_t v_univApprox_4147_; uint8_t v_inTypeClassResolution_4148_; uint8_t v_cacheInferType_4149_; uint8_t v___x_4150_; lean_object* v_config_4152_; 
v_trackZetaDelta_4140_ = lean_ctor_get_uint8(v___y_4114_, sizeof(void*)*7);
v_zetaDeltaSet_4141_ = lean_ctor_get(v___y_4114_, 1);
v_lctx_4142_ = lean_ctor_get(v___y_4114_, 2);
v_localInstances_4143_ = lean_ctor_get(v___y_4114_, 3);
v_defEqCtx_x3f_4144_ = lean_ctor_get(v___y_4114_, 4);
v_synthPendingDepth_4145_ = lean_ctor_get(v___y_4114_, 5);
v_canUnfold_x3f_4146_ = lean_ctor_get(v___y_4114_, 6);
v_univApprox_4147_ = lean_ctor_get_uint8(v___y_4114_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4148_ = lean_ctor_get_uint8(v___y_4114_, sizeof(void*)*7 + 2);
v_cacheInferType_4149_ = lean_ctor_get_uint8(v___y_4114_, sizeof(void*)*7 + 3);
v___x_4150_ = 1;
if (v_isShared_4139_ == 0)
{
v_config_4152_ = v___x_4138_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 0, v_foApprox_4119_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 1, v_ctxApprox_4120_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 2, v_quasiPatternApprox_4121_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 3, v_constApprox_4122_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 4, v_isDefEqStuckEx_4123_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 5, v_unificationHints_4124_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 6, v_proofIrrelevance_4125_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 7, v_assignSyntheticOpaque_4126_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 8, v_offsetCnstrs_4127_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 10, v_etaStruct_4128_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 11, v_univApprox_4129_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 12, v_iota_4130_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 13, v_beta_4131_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 14, v_proj_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 15, v_zeta_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 16, v_zetaDelta_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 17, v_zetaUnused_4135_);
lean_ctor_set_uint8(v_reuseFailAlloc_4204_, 18, v_zetaHave_4136_);
v_config_4152_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
uint64_t v___x_4153_; uint64_t v___x_4154_; uint64_t v___x_4155_; uint64_t v___x_4156_; uint64_t v___x_4157_; uint64_t v_key_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_ctor_set_uint8(v_config_4152_, 9, v___x_4150_);
v___x_4153_ = l_Lean_Meta_Context_configKey(v___y_4114_);
v___x_4154_ = 2ULL;
v___x_4155_ = lean_uint64_shift_right(v___x_4153_, v___x_4154_);
v___x_4156_ = lean_uint64_shift_left(v___x_4155_, v___x_4154_);
v___x_4157_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_4158_ = lean_uint64_lor(v___x_4156_, v___x_4157_);
v___x_4159_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4159_, 0, v_config_4152_);
lean_ctor_set_uint64(v___x_4159_, sizeof(void*)*1, v_key_4158_);
lean_inc(v_canUnfold_x3f_4146_);
lean_inc(v_synthPendingDepth_4145_);
lean_inc(v_defEqCtx_x3f_4144_);
lean_inc_ref(v_localInstances_4143_);
lean_inc_ref(v_lctx_4142_);
lean_inc(v_zetaDeltaSet_4141_);
v___x_4160_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
lean_ctor_set(v___x_4160_, 1, v_zetaDeltaSet_4141_);
lean_ctor_set(v___x_4160_, 2, v_lctx_4142_);
lean_ctor_set(v___x_4160_, 3, v_localInstances_4143_);
lean_ctor_set(v___x_4160_, 4, v_defEqCtx_x3f_4144_);
lean_ctor_set(v___x_4160_, 5, v_synthPendingDepth_4145_);
lean_ctor_set(v___x_4160_, 6, v_canUnfold_x3f_4146_);
lean_ctor_set_uint8(v___x_4160_, sizeof(void*)*7, v_trackZetaDelta_4140_);
lean_ctor_set_uint8(v___x_4160_, sizeof(void*)*7 + 1, v_univApprox_4147_);
lean_ctor_set_uint8(v___x_4160_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4148_);
lean_ctor_set_uint8(v___x_4160_, sizeof(void*)*7 + 3, v_cacheInferType_4149_);
lean_inc(v___y_4110_);
lean_inc_ref(v___y_4113_);
lean_inc(v___y_4112_);
lean_inc(v_a_4117_);
v___x_4161_ = lean_whnf(v_a_4117_, v___x_4160_, v___y_4112_, v___y_4113_, v___y_4110_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4163_; uint8_t v___x_4164_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4162_);
lean_dec_ref(v___x_4161_);
v___x_4163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_4164_ = l_Lean_Expr_isConstOf(v_a_4162_, v___x_4163_);
lean_dec(v_a_4162_);
if (v___x_4164_ == 0)
{
lean_dec(v_a_4117_);
v___y_4081_ = v___y_4111_;
v___y_4082_ = v___y_4115_;
v___y_4083_ = v___y_4114_;
v___y_4084_ = v___y_4112_;
v___y_4085_ = v___y_4113_;
v___y_4086_ = v___y_4110_;
goto v___jp_4080_;
}
else
{
lean_object* v___x_4165_; 
lean_inc(v_a_4117_);
v___x_4165_ = l_Lean_Meta_mkEqRefl(v_a_4117_, v___y_4114_, v___y_4112_, v___y_4113_, v___y_4110_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4167_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref(v___x_4165_);
lean_inc(v_mvarId_3928_);
v___x_4167_ = l_Lean_MVarId_getType(v_mvarId_3928_, v___y_4114_, v___y_4112_, v___y_4113_, v___y_4110_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v_nargs_4169_; lean_object* v___x_4170_; lean_object* v_dummy_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4168_);
lean_dec_ref(v___x_4167_);
v_nargs_4169_ = l_Lean_Expr_getAppNumArgs(v_a_4117_);
v___x_4170_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_4171_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_4169_);
v___x_4172_ = lean_mk_array(v_nargs_4169_, v_dummy_4171_);
v___x_4173_ = lean_unsigned_to_nat(1u);
v___x_4174_ = lean_nat_sub(v_nargs_4169_, v___x_4173_);
lean_dec(v_nargs_4169_);
v___x_4175_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4117_, v___x_4172_, v___x_4174_);
v___x_4176_ = lean_array_push(v___x_4175_, v_a_4166_);
v___x_4177_ = l_Lean_mkAppN(v___x_4170_, v___x_4176_);
lean_dec_ref(v___x_4176_);
lean_inc(v_val_3959_);
v___x_4178_ = l_Lean_LocalDecl_toExpr(v_val_3959_);
v___x_4179_ = l_Lean_Meta_mkAbsurd(v_a_4168_, v___x_4178_, v___x_4177_, v___y_4114_, v___y_4112_, v___y_4113_, v___y_4110_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4199_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4199_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4199_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4184_; 
lean_inc(v_mvarId_3928_);
v___x_4184_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3928_, v_a_4180_, v___y_4112_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref(v___x_4079_);
lean_dec(v_val_3959_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4196_ == 0)
{
lean_object* v_unused_4197_; 
v_unused_4197_ = lean_ctor_get(v___x_4184_, 0);
lean_dec(v_unused_4197_);
v___x_4186_ = v___x_4184_;
v_isShared_4187_ = v_isSharedCheck_4196_;
goto v_resetjp_4185_;
}
else
{
lean_dec(v___x_4184_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4196_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4188_ = lean_box(v___x_3938_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set_tag(v___x_4186_, 1);
lean_ctor_set(v___x_4186_, 0, v___x_4188_);
v___x_4190_ = v___x_4186_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4191_; lean_object* v___x_4193_; 
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
lean_ctor_set(v___x_4191_, 1, v___x_3963_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v___x_4191_);
v___x_4193_ = v___x_4182_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
v_a_3945_ = v___x_4193_;
goto v___jp_3944_;
}
}
}
}
else
{
lean_object* v_a_4198_; 
lean_del_object(v___x_4182_);
v_a_4198_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4198_);
lean_dec_ref(v___x_4184_);
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v___y_4105_ = v___y_4115_;
v_a_4106_ = v_a_4198_;
goto v___jp_4099_;
}
}
}
else
{
lean_object* v_a_4200_; 
v_a_4200_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4200_);
lean_dec_ref(v___x_4179_);
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v___y_4105_ = v___y_4115_;
v_a_4106_ = v_a_4200_;
goto v___jp_4099_;
}
}
else
{
lean_object* v_a_4201_; 
lean_dec(v_a_4166_);
lean_dec(v_a_4117_);
v_a_4201_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4201_);
lean_dec_ref(v___x_4167_);
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v___y_4105_ = v___y_4115_;
v_a_4106_ = v_a_4201_;
goto v___jp_4099_;
}
}
else
{
lean_object* v_a_4202_; 
lean_dec(v_a_4117_);
v_a_4202_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4202_);
lean_dec_ref(v___x_4165_);
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v___y_4105_ = v___y_4115_;
v_a_4106_ = v_a_4202_;
goto v___jp_4099_;
}
}
}
else
{
lean_object* v_a_4203_; 
lean_dec(v_a_4117_);
v_a_4203_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4203_);
lean_dec_ref(v___x_4161_);
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v___y_4105_ = v___y_4115_;
v_a_4106_ = v_a_4203_;
goto v___jp_4099_;
}
}
}
}
else
{
lean_object* v_a_4206_; 
v_a_4206_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4206_);
lean_dec_ref(v___x_4116_);
v___y_4100_ = v___y_4110_;
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4112_;
v___y_4103_ = v___y_4113_;
v___y_4104_ = v___y_4114_;
v___y_4105_ = v___y_4115_;
v_a_4106_ = v_a_4206_;
goto v___jp_4099_;
}
}
v___jp_4207_:
{
if (v___y_4214_ == 0)
{
v___y_4081_ = v___y_4209_;
v___y_4082_ = v___y_4213_;
v___y_4083_ = v___y_4212_;
v___y_4084_ = v___y_4210_;
v___y_4085_ = v___y_4211_;
v___y_4086_ = v___y_4208_;
goto v___jp_4080_;
}
else
{
v___y_4110_ = v___y_4208_;
v___y_4111_ = v___y_4209_;
v___y_4112_ = v___y_4210_;
v___y_4113_ = v___y_4211_;
v___y_4114_ = v___y_4212_;
v___y_4115_ = v___y_4213_;
goto v___jp_4109_;
}
}
v___jp_4215_:
{
if (v___y_4223_ == 0)
{
lean_dec_ref(v___y_4219_);
v___y_4208_ = v___y_4216_;
v___y_4209_ = v___y_4217_;
v___y_4210_ = v___y_4218_;
v___y_4211_ = v___y_4220_;
v___y_4212_ = v___y_4221_;
v___y_4213_ = v___y_4222_;
v___y_4214_ = v___x_4034_;
goto v___jp_4207_;
}
else
{
uint8_t v___x_4224_; 
v___x_4224_ = l_Lean_Expr_hasFVar(v___y_4219_);
lean_dec_ref(v___y_4219_);
if (v___x_4224_ == 0)
{
v___y_4110_ = v___y_4216_;
v___y_4111_ = v___y_4217_;
v___y_4112_ = v___y_4218_;
v___y_4113_ = v___y_4220_;
v___y_4114_ = v___y_4221_;
v___y_4115_ = v___y_4222_;
goto v___jp_4109_;
}
else
{
v___y_4208_ = v___y_4216_;
v___y_4209_ = v___y_4217_;
v___y_4210_ = v___y_4218_;
v___y_4211_ = v___y_4220_;
v___y_4212_ = v___y_4221_;
v___y_4213_ = v___y_4222_;
v___y_4214_ = v___x_4034_;
goto v___jp_4207_;
}
}
}
v___jp_4225_:
{
lean_object* v___x_4233_; 
lean_inc_ref(v___x_4079_);
v___x_4233_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4079_, v___y_4228_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; uint8_t v___x_4235_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref(v___x_4233_);
v___x_4235_ = l_Lean_Expr_hasMVar(v_a_4234_);
if (v___x_4235_ == 0)
{
v___y_4216_ = v___y_4226_;
v___y_4217_ = v___y_4227_;
v___y_4218_ = v___y_4228_;
v___y_4219_ = v_a_4234_;
v___y_4220_ = v___y_4229_;
v___y_4221_ = v___y_4230_;
v___y_4222_ = v___y_4231_;
v___y_4223_ = v___y_4232_;
goto v___jp_4215_;
}
else
{
v___y_4216_ = v___y_4226_;
v___y_4217_ = v___y_4227_;
v___y_4218_ = v___y_4228_;
v___y_4219_ = v_a_4234_;
v___y_4220_ = v___y_4229_;
v___y_4221_ = v___y_4230_;
v___y_4222_ = v___y_4231_;
v___y_4223_ = v___x_4034_;
goto v___jp_4215_;
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec_ref(v___x_4079_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4236_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4233_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4233_);
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
v___jp_4244_:
{
if (v___y_4251_ == 0)
{
v___y_4081_ = v___y_4246_;
v___y_4082_ = v___y_4250_;
v___y_4083_ = v___y_4249_;
v___y_4084_ = v___y_4247_;
v___y_4085_ = v___y_4248_;
v___y_4086_ = v___y_4245_;
goto v___jp_4080_;
}
else
{
v___y_4226_ = v___y_4245_;
v___y_4227_ = v___y_4246_;
v___y_4228_ = v___y_4247_;
v___y_4229_ = v___y_4248_;
v___y_4230_ = v___y_4249_;
v___y_4231_ = v___y_4250_;
v___y_4232_ = v___y_4251_;
goto v___jp_4225_;
}
}
v___jp_4252_:
{
uint8_t v_useDecide_4259_; 
v_useDecide_4259_ = lean_ctor_get_uint8(v_config_3927_, sizeof(void*)*1);
if (v_useDecide_4259_ == 0)
{
v___y_4245_ = v___y_4258_;
v___y_4246_ = v___y_4253_;
v___y_4247_ = v___y_4256_;
v___y_4248_ = v___y_4257_;
v___y_4249_ = v___y_4255_;
v___y_4250_ = v_isHEq_4254_;
v___y_4251_ = v___x_4034_;
goto v___jp_4244_;
}
else
{
uint8_t v___x_4260_; 
v___x_4260_ = l_Lean_Expr_hasFVar(v___x_4079_);
if (v___x_4260_ == 0)
{
v___y_4226_ = v___y_4258_;
v___y_4227_ = v___y_4253_;
v___y_4228_ = v___y_4256_;
v___y_4229_ = v___y_4257_;
v___y_4230_ = v___y_4255_;
v___y_4231_ = v_isHEq_4254_;
v___y_4232_ = v_useDecide_4259_;
goto v___jp_4225_;
}
else
{
v___y_4245_ = v___y_4258_;
v___y_4246_ = v___y_4253_;
v___y_4247_ = v___y_4256_;
v___y_4248_ = v___y_4257_;
v___y_4249_ = v___y_4255_;
v___y_4250_ = v_isHEq_4254_;
v___y_4251_ = v___x_4034_;
goto v___jp_4244_;
}
}
}
v___jp_4261_:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lean_Meta_isExprDefEq(v___y_4263_, v___y_4268_, v___y_4262_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; uint8_t v___x_4271_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref(v___x_4269_);
v___x_4271_ = lean_unbox(v_a_4270_);
lean_dec(v_a_4270_);
if (v___x_4271_ == 0)
{
v___y_4253_ = v___y_4264_;
v_isHEq_4254_ = v___x_3938_;
v___y_4255_ = v___y_4262_;
v___y_4256_ = v___y_4265_;
v___y_4257_ = v___y_4266_;
v___y_4258_ = v___y_4267_;
goto v___jp_4252_;
}
else
{
lean_object* v___x_4272_; 
lean_dec_ref(v___x_4079_);
lean_dec_ref(v_config_3927_);
lean_inc(v_mvarId_3928_);
v___x_4272_ = l_Lean_MVarId_getType(v_mvarId_3928_, v___y_4262_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref(v___x_4272_);
v___x_4274_ = l_Lean_LocalDecl_toExpr(v_val_3959_);
v___x_4275_ = l_Lean_Meta_mkEqOfHEq(v___x_4274_, v___x_3938_, v___y_4262_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4277_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref(v___x_4275_);
v___x_4277_ = l_Lean_Meta_mkNoConfusion(v_a_4273_, v_a_4276_, v___y_4262_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4279_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref(v___x_4277_);
v___x_4279_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3928_, v_a_4278_, v___y_4265_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
lean_dec_ref(v___x_4279_);
v___x_4280_ = lean_box(v___x_3938_);
v___x_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
lean_ctor_set(v___x_4282_, 1, v___x_3963_);
v___x_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4282_);
v_a_3945_ = v___x_4283_;
goto v___jp_3944_;
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
v_a_4284_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4279_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4279_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4292_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4277_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4277_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec(v_a_4273_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4300_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4275_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4275_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4308_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4272_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4272_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec_ref(v___x_4079_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4316_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4269_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4269_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
v___jp_4324_:
{
lean_object* v___x_4330_; 
lean_inc_ref(v___x_4079_);
v___x_4330_ = l_Lean_Meta_matchHEq_x3f(v___x_4079_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref(v___x_4330_);
if (lean_obj_tag(v_a_4331_) == 1)
{
lean_object* v_val_4332_; lean_object* v_snd_4333_; lean_object* v_snd_4334_; lean_object* v_fst_4335_; lean_object* v_fst_4336_; lean_object* v_fst_4337_; lean_object* v_snd_4338_; lean_object* v___x_4339_; 
v_val_4332_ = lean_ctor_get(v_a_4331_, 0);
lean_inc(v_val_4332_);
lean_dec_ref(v_a_4331_);
v_snd_4333_ = lean_ctor_get(v_val_4332_, 1);
lean_inc(v_snd_4333_);
v_snd_4334_ = lean_ctor_get(v_snd_4333_, 1);
lean_inc(v_snd_4334_);
v_fst_4335_ = lean_ctor_get(v_val_4332_, 0);
lean_inc(v_fst_4335_);
lean_dec(v_val_4332_);
v_fst_4336_ = lean_ctor_get(v_snd_4333_, 0);
lean_inc(v_fst_4336_);
lean_dec(v_snd_4333_);
v_fst_4337_ = lean_ctor_get(v_snd_4334_, 0);
lean_inc(v_fst_4337_);
v_snd_4338_ = lean_ctor_get(v_snd_4334_, 1);
lean_inc(v_snd_4338_);
lean_dec(v_snd_4334_);
v___x_4339_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4336_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
lean_dec_ref(v___x_4339_);
if (lean_obj_tag(v_a_4340_) == 1)
{
lean_object* v_val_4341_; lean_object* v___x_4342_; 
v_val_4341_ = lean_ctor_get(v_a_4340_, 0);
lean_inc(v_val_4341_);
lean_dec_ref(v_a_4340_);
v___x_4342_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4338_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
lean_inc(v_a_4343_);
lean_dec_ref(v___x_4342_);
if (lean_obj_tag(v_a_4343_) == 1)
{
lean_object* v_toConstantVal_4344_; lean_object* v_val_4345_; lean_object* v_toConstantVal_4346_; lean_object* v_name_4347_; lean_object* v_name_4348_; uint8_t v___x_4349_; 
v_toConstantVal_4344_ = lean_ctor_get(v_val_4341_, 0);
lean_inc_ref(v_toConstantVal_4344_);
lean_dec(v_val_4341_);
v_val_4345_ = lean_ctor_get(v_a_4343_, 0);
lean_inc(v_val_4345_);
lean_dec_ref(v_a_4343_);
v_toConstantVal_4346_ = lean_ctor_get(v_val_4345_, 0);
lean_inc_ref(v_toConstantVal_4346_);
lean_dec(v_val_4345_);
v_name_4347_ = lean_ctor_get(v_toConstantVal_4344_, 0);
lean_inc(v_name_4347_);
lean_dec_ref(v_toConstantVal_4344_);
v_name_4348_ = lean_ctor_get(v_toConstantVal_4346_, 0);
lean_inc(v_name_4348_);
lean_dec_ref(v_toConstantVal_4346_);
v___x_4349_ = lean_name_eq(v_name_4347_, v_name_4348_);
lean_dec(v_name_4348_);
lean_dec(v_name_4347_);
if (v___x_4349_ == 0)
{
v___y_4262_ = v___y_4326_;
v___y_4263_ = v_fst_4335_;
v___y_4264_ = v_isEq_4325_;
v___y_4265_ = v___y_4327_;
v___y_4266_ = v___y_4328_;
v___y_4267_ = v___y_4329_;
v___y_4268_ = v_fst_4337_;
goto v___jp_4261_;
}
else
{
if (v___x_4034_ == 0)
{
lean_dec(v_fst_4337_);
lean_dec(v_fst_4335_);
v___y_4253_ = v_isEq_4325_;
v_isHEq_4254_ = v___x_3938_;
v___y_4255_ = v___y_4326_;
v___y_4256_ = v___y_4327_;
v___y_4257_ = v___y_4328_;
v___y_4258_ = v___y_4329_;
goto v___jp_4252_;
}
else
{
v___y_4262_ = v___y_4326_;
v___y_4263_ = v_fst_4335_;
v___y_4264_ = v_isEq_4325_;
v___y_4265_ = v___y_4327_;
v___y_4266_ = v___y_4328_;
v___y_4267_ = v___y_4329_;
v___y_4268_ = v_fst_4337_;
goto v___jp_4261_;
}
}
}
else
{
lean_dec(v_a_4343_);
lean_dec(v_val_4341_);
lean_dec(v_fst_4337_);
lean_dec(v_fst_4335_);
v___y_4253_ = v_isEq_4325_;
v_isHEq_4254_ = v___x_3938_;
v___y_4255_ = v___y_4326_;
v___y_4256_ = v___y_4327_;
v___y_4257_ = v___y_4328_;
v___y_4258_ = v___y_4329_;
goto v___jp_4252_;
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
lean_dec(v_val_4341_);
lean_dec(v_fst_4337_);
lean_dec(v_fst_4335_);
lean_dec_ref(v___x_4079_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4350_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4342_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4342_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
else
{
lean_dec(v_a_4340_);
lean_dec(v_snd_4338_);
lean_dec(v_fst_4337_);
lean_dec(v_fst_4335_);
v___y_4253_ = v_isEq_4325_;
v_isHEq_4254_ = v___x_3938_;
v___y_4255_ = v___y_4326_;
v___y_4256_ = v___y_4327_;
v___y_4257_ = v___y_4328_;
v___y_4258_ = v___y_4329_;
goto v___jp_4252_;
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_dec(v_snd_4338_);
lean_dec(v_fst_4337_);
lean_dec(v_fst_4335_);
lean_dec_ref(v___x_4079_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4358_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4339_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4339_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
else
{
lean_dec(v_a_4331_);
v___y_4253_ = v_isEq_4325_;
v_isHEq_4254_ = v___x_4034_;
v___y_4255_ = v___y_4326_;
v___y_4256_ = v___y_4327_;
v___y_4257_ = v___y_4328_;
v___y_4258_ = v___y_4329_;
goto v___jp_4252_;
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec_ref(v___x_4079_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4366_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4330_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4330_);
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
v___jp_4374_:
{
lean_object* v___x_4379_; 
lean_inc_ref(v___x_4079_);
v___x_4379_ = l_Lean_Meta_matchEq_x3f(v___x_4079_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref(v___x_4379_);
if (lean_obj_tag(v_a_4380_) == 1)
{
lean_object* v_val_4381_; lean_object* v_snd_4382_; lean_object* v_fst_4383_; lean_object* v_snd_4384_; lean_object* v___x_4385_; 
v_val_4381_ = lean_ctor_get(v_a_4380_, 0);
lean_inc(v_val_4381_);
lean_dec_ref(v_a_4380_);
v_snd_4382_ = lean_ctor_get(v_val_4381_, 1);
lean_inc(v_snd_4382_);
lean_dec(v_val_4381_);
v_fst_4383_ = lean_ctor_get(v_snd_4382_, 0);
lean_inc(v_fst_4383_);
v_snd_4384_ = lean_ctor_get(v_snd_4382_, 1);
lean_inc(v_snd_4384_);
lean_dec(v_snd_4382_);
v___x_4385_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4383_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref(v___x_4385_);
if (lean_obj_tag(v_a_4386_) == 1)
{
lean_object* v_val_4387_; lean_object* v___x_4388_; 
v_val_4387_ = lean_ctor_get(v_a_4386_, 0);
lean_inc(v_val_4387_);
lean_dec_ref(v_a_4386_);
v___x_4388_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4384_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref(v___x_4388_);
if (lean_obj_tag(v_a_4389_) == 1)
{
lean_object* v_toConstantVal_4390_; lean_object* v_val_4391_; lean_object* v_toConstantVal_4392_; lean_object* v_name_4393_; lean_object* v_name_4394_; uint8_t v___x_4395_; 
v_toConstantVal_4390_ = lean_ctor_get(v_val_4387_, 0);
lean_inc_ref(v_toConstantVal_4390_);
lean_dec(v_val_4387_);
v_val_4391_ = lean_ctor_get(v_a_4389_, 0);
lean_inc(v_val_4391_);
lean_dec_ref(v_a_4389_);
v_toConstantVal_4392_ = lean_ctor_get(v_val_4391_, 0);
lean_inc_ref(v_toConstantVal_4392_);
lean_dec(v_val_4391_);
v_name_4393_ = lean_ctor_get(v_toConstantVal_4390_, 0);
lean_inc(v_name_4393_);
lean_dec_ref(v_toConstantVal_4390_);
v_name_4394_ = lean_ctor_get(v_toConstantVal_4392_, 0);
lean_inc(v_name_4394_);
lean_dec_ref(v_toConstantVal_4392_);
v___x_4395_ = lean_name_eq(v_name_4393_, v_name_4394_);
lean_dec(v_name_4394_);
lean_dec(v_name_4393_);
if (v___x_4395_ == 0)
{
lean_dec_ref(v___x_4079_);
lean_dec_ref(v_config_3927_);
v___y_3965_ = v___y_4378_;
v___y_3966_ = v___y_4377_;
v___y_3967_ = v___y_4376_;
v___y_3968_ = v___y_4375_;
goto v___jp_3964_;
}
else
{
if (v___x_4034_ == 0)
{
lean_del_object(v___x_3961_);
v_isEq_4325_ = v___x_3938_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4376_;
v___y_4328_ = v___y_4377_;
v___y_4329_ = v___y_4378_;
goto v___jp_4324_;
}
else
{
lean_dec_ref(v___x_4079_);
lean_dec_ref(v_config_3927_);
v___y_3965_ = v___y_4378_;
v___y_3966_ = v___y_4377_;
v___y_3967_ = v___y_4376_;
v___y_3968_ = v___y_4375_;
goto v___jp_3964_;
}
}
}
else
{
lean_dec(v_a_4389_);
lean_dec(v_val_4387_);
lean_del_object(v___x_3961_);
v_isEq_4325_ = v___x_3938_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4376_;
v___y_4328_ = v___y_4377_;
v___y_4329_ = v___y_4378_;
goto v___jp_4324_;
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec(v_val_4387_);
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4396_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4388_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4388_);
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
lean_dec(v_a_4386_);
lean_dec(v_snd_4384_);
lean_del_object(v___x_3961_);
v_isEq_4325_ = v___x_3938_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4376_;
v___y_4328_ = v___y_4377_;
v___y_4329_ = v___y_4378_;
goto v___jp_4324_;
}
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_dec(v_snd_4384_);
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
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
lean_dec(v_a_4380_);
lean_del_object(v___x_3961_);
v_isEq_4325_ = v___x_4034_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4376_;
v___y_4328_ = v___y_4377_;
v___y_4329_ = v___y_4378_;
goto v___jp_4324_;
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4412_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4379_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4379_);
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
v___jp_4420_:
{
lean_object* v___x_4425_; 
lean_inc_ref(v___x_4079_);
v___x_4425_ = l_refutableHasNotBit_x3f(v___x_4079_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref(v___x_4425_);
if (lean_obj_tag(v_a_4426_) == 1)
{
lean_object* v_val_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4467_; 
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec_ref(v_config_3927_);
v_val_4427_ = lean_ctor_get(v_a_4426_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v_a_4426_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4429_ = v_a_4426_;
v_isShared_4430_ = v_isSharedCheck_4467_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_val_4427_);
lean_dec(v_a_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4467_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; 
lean_inc(v_mvarId_3928_);
v___x_4431_ = l_Lean_MVarId_getType(v_mvarId_3928_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_a_4432_);
lean_dec_ref(v___x_4431_);
v___x_4433_ = l_Lean_LocalDecl_toExpr(v_val_3959_);
v___x_4434_ = l_Lean_Meta_mkAbsurd(v_a_4432_, v_val_4427_, v___x_4433_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_object* v_a_4435_; lean_object* v___x_4436_; 
v_a_4435_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_a_4435_);
lean_dec_ref(v___x_4434_);
v___x_4436_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3928_, v_a_4435_, v___y_4422_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v___x_4437_; lean_object* v___x_4439_; 
lean_dec_ref(v___x_4436_);
v___x_4437_ = lean_box(v___x_3938_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4437_);
v___x_4439_ = v___x_4429_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
lean_ctor_set(v___x_4440_, 1, v___x_3963_);
v___x_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
v_a_3945_ = v___x_4441_;
goto v___jp_3944_;
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_del_object(v___x_4429_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
v_a_4443_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4436_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4436_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_del_object(v___x_4429_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4451_ = lean_ctor_get(v___x_4434_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4434_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4434_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_del_object(v___x_4429_);
lean_dec(v_val_4427_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4459_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4431_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4431_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
}
else
{
lean_object* v___x_4468_; 
lean_dec(v_a_4426_);
lean_inc_ref(v___x_4079_);
v___x_4468_ = l_Lean_Meta_matchNe_x3f(v___x_4079_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_a_4469_);
lean_dec_ref(v___x_4468_);
if (lean_obj_tag(v_a_4469_) == 1)
{
lean_object* v_val_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4540_; 
v_val_4470_ = lean_ctor_get(v_a_4469_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v_a_4469_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4472_ = v_a_4469_;
v_isShared_4473_ = v_isSharedCheck_4540_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_val_4470_);
lean_dec(v_a_4469_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4540_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v_snd_4474_; lean_object* v_fst_4475_; lean_object* v_snd_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4539_; 
v_snd_4474_ = lean_ctor_get(v_val_4470_, 1);
lean_inc(v_snd_4474_);
lean_dec(v_val_4470_);
v_fst_4475_ = lean_ctor_get(v_snd_4474_, 0);
v_snd_4476_ = lean_ctor_get(v_snd_4474_, 1);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_snd_4474_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4478_ = v_snd_4474_;
v_isShared_4479_ = v_isSharedCheck_4539_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_snd_4476_);
lean_inc(v_fst_4475_);
lean_dec(v_snd_4474_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4539_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4480_; 
lean_inc(v_fst_4475_);
v___x_4480_ = l_Lean_Meta_isExprDefEq(v_fst_4475_, v_snd_4476_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; uint8_t v___x_4482_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref(v___x_4480_);
v___x_4482_ = lean_unbox(v_a_4481_);
lean_dec(v_a_4481_);
if (v___x_4482_ == 0)
{
lean_del_object(v___x_4478_);
lean_dec(v_fst_4475_);
lean_del_object(v___x_4472_);
v___y_4375_ = v___y_4421_;
v___y_4376_ = v___y_4422_;
v___y_4377_ = v___y_4423_;
v___y_4378_ = v___y_4424_;
goto v___jp_4374_;
}
else
{
lean_object* v___x_4483_; 
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec_ref(v_config_3927_);
lean_inc(v_mvarId_3928_);
v___x_4483_ = l_Lean_MVarId_getType(v_mvarId_3928_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4485_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref(v___x_4483_);
v___x_4485_ = l_Lean_Meta_mkEqRefl(v_fst_4475_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref(v___x_4485_);
v___x_4487_ = l_Lean_LocalDecl_toExpr(v_val_3959_);
v___x_4488_ = l_Lean_Meta_mkAbsurd(v_a_4484_, v_a_4486_, v___x_4487_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4490_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref(v___x_4488_);
v___x_4490_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3928_, v_a_4489_, v___y_4422_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4493_; 
lean_dec_ref(v___x_4490_);
v___x_4491_ = lean_box(v___x_3938_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 0, v___x_4491_);
v___x_4493_ = v___x_4472_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4491_);
v___x_4493_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4495_; 
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 1, v___x_3963_);
lean_ctor_set(v___x_4478_, 0, v___x_4493_);
v___x_4495_ = v___x_4478_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4493_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v___x_3963_);
v___x_4495_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v___x_4496_; 
v___x_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
v_a_3945_ = v___x_4496_;
goto v___jp_3944_;
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_del_object(v___x_4478_);
lean_del_object(v___x_4472_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
v_a_4499_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4490_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4490_);
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
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_del_object(v___x_4478_);
lean_del_object(v___x_4472_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4507_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4488_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4488_);
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
lean_dec(v_a_4484_);
lean_del_object(v___x_4478_);
lean_del_object(v___x_4472_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4515_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4485_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4485_);
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
lean_del_object(v___x_4478_);
lean_dec(v_fst_4475_);
lean_del_object(v___x_4472_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_4523_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4483_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4483_);
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
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_del_object(v___x_4478_);
lean_dec(v_fst_4475_);
lean_del_object(v___x_4472_);
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4531_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4480_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4480_);
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
}
else
{
lean_dec(v_a_4469_);
v___y_4375_ = v___y_4421_;
v___y_4376_ = v___y_4422_;
v___y_4377_ = v___y_4423_;
v___y_4378_ = v___y_4424_;
goto v___jp_4374_;
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4541_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4468_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4468_);
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
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec_ref(v___x_4079_);
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4549_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4425_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4425_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
else
{
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
v_a_3953_ = v___x_4005_;
goto v___jp_3952_;
}
v___jp_3964_:
{
lean_object* v___x_3969_; 
lean_inc(v_mvarId_3928_);
v___x_3969_ = l_Lean_MVarId_getType(v_mvarId_3928_, v___y_3968_, v___y_3967_, v___y_3966_, v___y_3965_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref(v___x_3969_);
v___x_3971_ = l_Lean_LocalDecl_toExpr(v_val_3959_);
v___x_3972_ = l_Lean_Meta_mkNoConfusion(v_a_3970_, v___x_3971_, v___y_3968_, v___y_3967_, v___y_3966_, v___y_3965_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3974_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref(v___x_3972_);
v___x_3974_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3928_, v_a_3973_, v___y_3967_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v___x_3975_; lean_object* v___x_3977_; 
lean_dec_ref(v___x_3974_);
v___x_3975_ = lean_box(v___x_3938_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 0, v___x_3975_);
v___x_3977_ = v___x_3961_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
lean_ctor_set(v___x_3978_, 1, v___x_3963_);
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
v_a_3945_ = v___x_3979_;
goto v___jp_3944_;
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_del_object(v___x_3961_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
v_a_3981_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3974_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3974_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_del_object(v___x_3961_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_3989_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3972_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3972_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_del_object(v___x_3961_);
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
v_a_3997_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3969_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3969_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
v___jp_4006_:
{
lean_object* v_searchFuel_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_searchFuel_4011_ = lean_ctor_get(v_config_3927_, 0);
v___x_4012_ = l_Lean_LocalDecl_fvarId(v_val_3959_);
lean_dec(v_val_3959_);
lean_inc(v_searchFuel_4011_);
lean_inc(v_mvarId_3928_);
v___x_4013_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3928_, v___x_4012_, v_searchFuel_4011_, v___y_4007_, v___y_4008_, v___y_4010_, v___y_4009_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; uint8_t v___x_4015_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref(v___x_4013_);
v___x_4015_ = lean_unbox(v_a_4014_);
lean_dec(v_a_4014_);
if (v___x_4015_ == 0)
{
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
v_a_3953_ = v___x_4005_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v___x_4016_ = lean_box(v___x_3938_);
v___x_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
v___x_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
lean_ctor_set(v___x_4018_, 1, v___x_3963_);
v___x_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
v_a_3945_ = v___x_4019_;
goto v___jp_3944_;
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4020_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4013_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4013_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
v___jp_4028_:
{
if (v___y_4033_ == 0)
{
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
v_a_3953_ = v___x_4005_;
goto v___jp_3952_;
}
else
{
v___y_4007_ = v___y_4029_;
v___y_4008_ = v___y_4030_;
v___y_4009_ = v___y_4031_;
v___y_4010_ = v___y_4032_;
goto v___jp_4006_;
}
}
v___jp_4035_:
{
if (v___y_4040_ == 0)
{
v___y_4007_ = v___y_4036_;
v___y_4008_ = v___y_4037_;
v___y_4009_ = v___y_4038_;
v___y_4010_ = v___y_4039_;
goto v___jp_4006_;
}
else
{
v___y_4029_ = v___y_4036_;
v___y_4030_ = v___y_4037_;
v___y_4031_ = v___y_4038_;
v___y_4032_ = v___y_4039_;
v___y_4033_ = v___x_4034_;
goto v___jp_4028_;
}
}
v___jp_4041_:
{
if (v___y_4047_ == 0)
{
v___y_4029_ = v___y_4042_;
v___y_4030_ = v___y_4043_;
v___y_4031_ = v___y_4044_;
v___y_4032_ = v___y_4045_;
v___y_4033_ = v___x_4034_;
goto v___jp_4028_;
}
else
{
v___y_4036_ = v___y_4042_;
v___y_4037_ = v___y_4043_;
v___y_4038_ = v___y_4044_;
v___y_4039_ = v___y_4045_;
v___y_4040_ = v___y_4046_;
goto v___jp_4035_;
}
}
v___jp_4048_:
{
uint8_t v_emptyType_4055_; 
v_emptyType_4055_ = lean_ctor_get_uint8(v_config_3927_, sizeof(void*)*1 + 1);
if (v_emptyType_4055_ == 0)
{
v___y_4042_ = v___y_4051_;
v___y_4043_ = v___y_4052_;
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4053_;
v___y_4046_ = v___y_4050_;
v___y_4047_ = v___x_4034_;
goto v___jp_4041_;
}
else
{
if (v___y_4049_ == 0)
{
v___y_4036_ = v___y_4051_;
v___y_4037_ = v___y_4052_;
v___y_4038_ = v___y_4054_;
v___y_4039_ = v___y_4053_;
v___y_4040_ = v___y_4050_;
goto v___jp_4035_;
}
else
{
v___y_4042_ = v___y_4051_;
v___y_4043_ = v___y_4052_;
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4053_;
v___y_4046_ = v___y_4050_;
v___y_4047_ = v___x_4034_;
goto v___jp_4041_;
}
}
}
v___jp_4056_:
{
if (v___y_4063_ == 0)
{
v___y_4049_ = v___y_4057_;
v___y_4050_ = v___y_4061_;
v___y_4051_ = v___y_4059_;
v___y_4052_ = v___y_4062_;
v___y_4053_ = v___y_4058_;
v___y_4054_ = v___y_4060_;
goto v___jp_4048_;
}
else
{
lean_object* v___x_4064_; 
lean_inc(v_val_3959_);
lean_inc(v_mvarId_3928_);
v___x_4064_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3928_, v_val_3959_, v___y_4059_, v___y_4062_, v___y_4058_, v___y_4060_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; uint8_t v___x_4066_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_a_4065_);
lean_dec_ref(v___x_4064_);
v___x_4066_ = lean_unbox(v_a_4065_);
lean_dec(v_a_4065_);
if (v___x_4066_ == 0)
{
v___y_4049_ = v___y_4057_;
v___y_4050_ = v___y_4061_;
v___y_4051_ = v___y_4059_;
v___y_4052_ = v___y_4062_;
v___y_4053_ = v___y_4058_;
v___y_4054_ = v___y_4060_;
goto v___jp_4048_;
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
lean_dec(v_val_3959_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v___x_4067_ = lean_box(v___x_3938_);
v___x_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
v___x_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
lean_ctor_set(v___x_4069_, 1, v___x_3963_);
v___x_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
v_a_3945_ = v___x_4070_;
goto v___jp_3944_;
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v_val_3959_);
lean_del_object(v___x_3942_);
lean_dec(v_snd_3940_);
lean_dec(v_mvarId_3928_);
lean_dec_ref(v_config_3927_);
v_a_4071_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4064_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4064_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
}
}
v___jp_3944_:
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3946_, 0, v_a_3945_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3946_);
v___x_3948_ = v___x_3942_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_snd_3940_);
v___x_3948_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
return v___x_3949_;
}
}
v___jp_3952_:
{
lean_object* v___x_3954_; size_t v___x_3955_; size_t v___x_3956_; lean_object* v___x_3957_; 
v___x_3954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3951_);
lean_ctor_set(v___x_3954_, 1, v_a_3953_);
v___x_3955_ = ((size_t)1ULL);
v___x_3956_ = lean_usize_add(v_i_3931_, v___x_3955_);
v___x_3957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3927_, v_mvarId_3928_, v_as_3929_, v_sz_3930_, v___x_3956_, v___x_3954_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
return v___x_3957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4630_, lean_object* v_mvarId_4631_, lean_object* v_as_4632_, lean_object* v_sz_4633_, lean_object* v_i_4634_, lean_object* v_b_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
size_t v_sz_boxed_4641_; size_t v_i_boxed_4642_; lean_object* v_res_4643_; 
v_sz_boxed_4641_ = lean_unbox_usize(v_sz_4633_);
lean_dec(v_sz_4633_);
v_i_boxed_4642_ = lean_unbox_usize(v_i_4634_);
lean_dec(v_i_4634_);
v_res_4643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4630_, v_mvarId_4631_, v_as_4632_, v_sz_boxed_4641_, v_i_boxed_4642_, v_b_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec_ref(v_as_4632_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4644_, lean_object* v_config_4645_, lean_object* v_mvarId_4646_, lean_object* v_n_4647_, lean_object* v_b_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_){
_start:
{
if (lean_obj_tag(v_n_4647_) == 0)
{
lean_object* v_cs_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; size_t v_sz_4657_; size_t v___x_4658_; lean_object* v___x_4659_; 
v_cs_4654_ = lean_ctor_get(v_n_4647_, 0);
v___x_4655_ = lean_box(0);
v___x_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4655_);
lean_ctor_set(v___x_4656_, 1, v_b_4648_);
v_sz_4657_ = lean_array_size(v_cs_4654_);
v___x_4658_ = ((size_t)0ULL);
v___x_4659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4644_, v_config_4645_, v_mvarId_4646_, v_cs_4654_, v_sz_4657_, v___x_4658_, v___x_4656_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4674_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4662_ = v___x_4659_;
v_isShared_4663_ = v_isSharedCheck_4674_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4659_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4674_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v_fst_4664_; 
v_fst_4664_ = lean_ctor_get(v_a_4660_, 0);
if (lean_obj_tag(v_fst_4664_) == 0)
{
lean_object* v_snd_4665_; lean_object* v___x_4666_; lean_object* v___x_4668_; 
v_snd_4665_ = lean_ctor_get(v_a_4660_, 1);
lean_inc(v_snd_4665_);
lean_dec(v_a_4660_);
v___x_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4666_, 0, v_snd_4665_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 0, v___x_4666_);
v___x_4668_ = v___x_4662_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v___x_4666_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
else
{
lean_object* v_val_4670_; lean_object* v___x_4672_; 
lean_inc_ref(v_fst_4664_);
lean_dec(v_a_4660_);
v_val_4670_ = lean_ctor_get(v_fst_4664_, 0);
lean_inc(v_val_4670_);
lean_dec_ref(v_fst_4664_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 0, v_val_4670_);
v___x_4672_ = v___x_4662_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_val_4670_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
v_a_4675_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4677_ = v___x_4659_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4659_);
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
else
{
lean_object* v_vs_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; size_t v_sz_4686_; size_t v___x_4687_; lean_object* v___x_4688_; 
v_vs_4683_ = lean_ctor_get(v_n_4647_, 0);
v___x_4684_ = lean_box(0);
v___x_4685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4684_);
lean_ctor_set(v___x_4685_, 1, v_b_4648_);
v_sz_4686_ = lean_array_size(v_vs_4683_);
v___x_4687_ = ((size_t)0ULL);
v___x_4688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4645_, v_mvarId_4646_, v_vs_4683_, v_sz_4686_, v___x_4687_, v___x_4685_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4703_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4691_ = v___x_4688_;
v_isShared_4692_ = v_isSharedCheck_4703_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4688_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4703_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v_fst_4693_; 
v_fst_4693_ = lean_ctor_get(v_a_4689_, 0);
if (lean_obj_tag(v_fst_4693_) == 0)
{
lean_object* v_snd_4694_; lean_object* v___x_4695_; lean_object* v___x_4697_; 
v_snd_4694_ = lean_ctor_get(v_a_4689_, 1);
lean_inc(v_snd_4694_);
lean_dec(v_a_4689_);
v___x_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4695_, 0, v_snd_4694_);
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 0, v___x_4695_);
v___x_4697_ = v___x_4691_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
else
{
lean_object* v_val_4699_; lean_object* v___x_4701_; 
lean_inc_ref(v_fst_4693_);
lean_dec(v_a_4689_);
v_val_4699_ = lean_ctor_get(v_fst_4693_, 0);
lean_inc(v_val_4699_);
lean_dec_ref(v_fst_4693_);
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 0, v_val_4699_);
v___x_4701_ = v___x_4691_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_val_4699_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
}
else
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
v_a_4704_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4688_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4688_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4712_, lean_object* v_config_4713_, lean_object* v_mvarId_4714_, lean_object* v_as_4715_, size_t v_sz_4716_, size_t v_i_4717_, lean_object* v_b_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
uint8_t v___x_4724_; 
v___x_4724_ = lean_usize_dec_lt(v_i_4717_, v_sz_4716_);
if (v___x_4724_ == 0)
{
lean_object* v___x_4725_; 
lean_dec(v_mvarId_4714_);
lean_dec_ref(v_config_4713_);
v___x_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4725_, 0, v_b_4718_);
return v___x_4725_;
}
else
{
lean_object* v_snd_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4760_; 
v_snd_4726_ = lean_ctor_get(v_b_4718_, 1);
v_isSharedCheck_4760_ = !lean_is_exclusive(v_b_4718_);
if (v_isSharedCheck_4760_ == 0)
{
lean_object* v_unused_4761_; 
v_unused_4761_ = lean_ctor_get(v_b_4718_, 0);
lean_dec(v_unused_4761_);
v___x_4728_ = v_b_4718_;
v_isShared_4729_ = v_isSharedCheck_4760_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_snd_4726_);
lean_dec(v_b_4718_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4760_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v_a_4730_; lean_object* v___x_4731_; 
v_a_4730_ = lean_array_uget_borrowed(v_as_4715_, v_i_4717_);
lean_inc(v_snd_4726_);
lean_inc(v_mvarId_4714_);
lean_inc_ref(v_config_4713_);
v___x_4731_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4712_, v_config_4713_, v_mvarId_4714_, v_a_4730_, v_snd_4726_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4751_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4734_ = v___x_4731_;
v_isShared_4735_ = v_isSharedCheck_4751_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4751_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
if (lean_obj_tag(v_a_4732_) == 0)
{
lean_object* v___x_4736_; lean_object* v___x_4738_; 
lean_dec(v_mvarId_4714_);
lean_dec_ref(v_config_4713_);
v___x_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4736_, 0, v_a_4732_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 0, v___x_4736_);
v___x_4738_ = v___x_4728_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4736_);
lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_snd_4726_);
v___x_4738_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
lean_object* v___x_4740_; 
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 0, v___x_4738_);
v___x_4740_ = v___x_4734_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4738_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4744_; lean_object* v___x_4746_; 
lean_del_object(v___x_4734_);
lean_dec(v_snd_4726_);
v_a_4743_ = lean_ctor_get(v_a_4732_, 0);
lean_inc(v_a_4743_);
lean_dec_ref(v_a_4732_);
v___x_4744_ = lean_box(0);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 1, v_a_4743_);
lean_ctor_set(v___x_4728_, 0, v___x_4744_);
v___x_4746_ = v___x_4728_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_a_4743_);
v___x_4746_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
size_t v___x_4747_; size_t v___x_4748_; 
v___x_4747_ = ((size_t)1ULL);
v___x_4748_ = lean_usize_add(v_i_4717_, v___x_4747_);
v_i_4717_ = v___x_4748_;
v_b_4718_ = v___x_4746_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_del_object(v___x_4728_);
lean_dec(v_snd_4726_);
lean_dec(v_mvarId_4714_);
lean_dec_ref(v_config_4713_);
v_a_4752_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4731_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4731_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4762_, lean_object* v_config_4763_, lean_object* v_mvarId_4764_, lean_object* v_as_4765_, lean_object* v_sz_4766_, lean_object* v_i_4767_, lean_object* v_b_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
size_t v_sz_boxed_4774_; size_t v_i_boxed_4775_; lean_object* v_res_4776_; 
v_sz_boxed_4774_ = lean_unbox_usize(v_sz_4766_);
lean_dec(v_sz_4766_);
v_i_boxed_4775_ = lean_unbox_usize(v_i_4767_);
lean_dec(v_i_4767_);
v_res_4776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4762_, v_config_4763_, v_mvarId_4764_, v_as_4765_, v_sz_boxed_4774_, v_i_boxed_4775_, v_b_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
lean_dec_ref(v_as_4765_);
lean_dec_ref(v_init_4762_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4777_, lean_object* v_config_4778_, lean_object* v_mvarId_4779_, lean_object* v_n_4780_, lean_object* v_b_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4777_, v_config_4778_, v_mvarId_4779_, v_n_4780_, v_b_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec_ref(v_n_4780_);
lean_dec_ref(v_init_4777_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4788_, lean_object* v_mvarId_4789_, lean_object* v_t_4790_, lean_object* v_init_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
lean_object* v_root_4797_; lean_object* v_tail_4798_; lean_object* v___x_4799_; 
v_root_4797_ = lean_ctor_get(v_t_4790_, 0);
v_tail_4798_ = lean_ctor_get(v_t_4790_, 1);
lean_inc(v_mvarId_4789_);
lean_inc_ref(v_config_4788_);
lean_inc_ref(v_init_4791_);
v___x_4799_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4791_, v_config_4788_, v_mvarId_4789_, v_root_4797_, v_init_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
lean_dec_ref(v_init_4791_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4836_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4836_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4836_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
if (lean_obj_tag(v_a_4800_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4806_; 
lean_dec(v_mvarId_4789_);
lean_dec_ref(v_config_4788_);
v_a_4804_ = lean_ctor_get(v_a_4800_, 0);
lean_inc(v_a_4804_);
lean_dec_ref(v_a_4800_);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v_a_4804_);
v___x_4806_ = v___x_4802_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4804_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; size_t v_sz_4811_; size_t v___x_4812_; lean_object* v___x_4813_; 
lean_del_object(v___x_4802_);
v_a_4808_ = lean_ctor_get(v_a_4800_, 0);
lean_inc(v_a_4808_);
lean_dec_ref(v_a_4800_);
v___x_4809_ = lean_box(0);
v___x_4810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4810_, 0, v___x_4809_);
lean_ctor_set(v___x_4810_, 1, v_a_4808_);
v_sz_4811_ = lean_array_size(v_tail_4798_);
v___x_4812_ = ((size_t)0ULL);
v___x_4813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4788_, v_mvarId_4789_, v_tail_4798_, v_sz_4811_, v___x_4812_, v___x_4810_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4827_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4816_ = v___x_4813_;
v_isShared_4817_ = v_isSharedCheck_4827_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4827_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v_fst_4818_; 
v_fst_4818_ = lean_ctor_get(v_a_4814_, 0);
if (lean_obj_tag(v_fst_4818_) == 0)
{
lean_object* v_snd_4819_; lean_object* v___x_4821_; 
v_snd_4819_ = lean_ctor_get(v_a_4814_, 1);
lean_inc(v_snd_4819_);
lean_dec(v_a_4814_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v_snd_4819_);
v___x_4821_ = v___x_4816_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_snd_4819_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
else
{
lean_object* v_val_4823_; lean_object* v___x_4825_; 
lean_inc_ref(v_fst_4818_);
lean_dec(v_a_4814_);
v_val_4823_ = lean_ctor_get(v_fst_4818_, 0);
lean_inc(v_val_4823_);
lean_dec_ref(v_fst_4818_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v_val_4823_);
v___x_4825_ = v___x_4816_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_val_4823_);
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
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
v_a_4828_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4813_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4813_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
}
}
else
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
lean_dec(v_mvarId_4789_);
lean_dec_ref(v_config_4788_);
v_a_4837_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4799_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4799_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4845_, lean_object* v_mvarId_4846_, lean_object* v_t_4847_, lean_object* v_init_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v_res_4854_; 
v_res_4854_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4845_, v_mvarId_4846_, v_t_4847_, v_init_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec_ref(v_t_4847_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4855_, lean_object* v___x_4856_, lean_object* v_config_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_){
_start:
{
lean_object* v___x_4863_; 
lean_inc(v_mvarId_4855_);
v___x_4863_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4855_, v___x_4856_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v___x_4864_; 
lean_dec_ref(v___x_4863_);
lean_inc(v_mvarId_4855_);
v___x_4864_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4855_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4898_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4867_ = v___x_4864_;
v_isShared_4868_ = v_isSharedCheck_4898_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4864_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4898_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
uint8_t v___x_4869_; 
v___x_4869_ = lean_unbox(v_a_4865_);
if (v___x_4869_ == 0)
{
lean_object* v_lctx_4870_; lean_object* v_decls_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
lean_del_object(v___x_4867_);
v_lctx_4870_ = lean_ctor_get(v___y_4858_, 2);
v_decls_4871_ = lean_ctor_get(v_lctx_4870_, 1);
v___x_4872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4873_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4857_, v_mvarId_4855_, v_decls_4871_, v___x_4872_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4886_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4886_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4886_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v_fst_4878_; 
v_fst_4878_ = lean_ctor_get(v_a_4874_, 0);
lean_inc(v_fst_4878_);
lean_dec(v_a_4874_);
if (lean_obj_tag(v_fst_4878_) == 0)
{
lean_object* v___x_4880_; 
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v_a_4865_);
v___x_4880_ = v___x_4876_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4865_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
else
{
lean_object* v_val_4882_; lean_object* v___x_4884_; 
lean_dec(v_a_4865_);
v_val_4882_ = lean_ctor_get(v_fst_4878_, 0);
lean_inc(v_val_4882_);
lean_dec_ref(v_fst_4878_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v_val_4882_);
v___x_4884_ = v___x_4876_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_val_4882_);
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
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
lean_dec(v_a_4865_);
v_a_4887_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4873_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4873_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
else
{
lean_object* v___x_4896_; 
lean_dec_ref(v_config_4857_);
lean_dec(v_mvarId_4855_);
if (v_isShared_4868_ == 0)
{
v___x_4896_ = v___x_4867_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4865_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
else
{
lean_dec_ref(v_config_4857_);
lean_dec(v_mvarId_4855_);
return v___x_4864_;
}
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
lean_dec_ref(v_config_4857_);
lean_dec(v_mvarId_4855_);
v_a_4899_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4863_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4863_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4907_, lean_object* v___x_4908_, lean_object* v_config_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4907_, v___x_4908_, v_config_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4918_, lean_object* v_config_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_){
_start:
{
lean_object* v___x_4925_; lean_object* v___f_4926_; lean_object* v___x_4927_; 
v___x_4925_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4918_);
v___f_4926_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4926_, 0, v_mvarId_4918_);
lean_closure_set(v___f_4926_, 1, v___x_4925_);
lean_closure_set(v___f_4926_, 2, v_config_4919_);
v___x_4927_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4918_, v___f_4926_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4928_, lean_object* v_config_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l_Lean_MVarId_contradictionCore(v_mvarId_4928_, v_config_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
lean_dec(v_a_4933_);
lean_dec_ref(v_a_4932_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4936_, lean_object* v_config_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_){
_start:
{
lean_object* v___x_4943_; 
lean_inc(v_mvarId_4936_);
v___x_4943_ = l_Lean_MVarId_contradictionCore(v_mvarId_4936_, v_config_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4956_; 
v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4946_ = v___x_4943_;
v_isShared_4947_ = v_isSharedCheck_4956_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4943_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4956_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
uint8_t v___x_4948_; 
v___x_4948_ = lean_unbox(v_a_4944_);
lean_dec(v_a_4944_);
if (v___x_4948_ == 0)
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
lean_del_object(v___x_4946_);
v___x_4949_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4950_ = lean_box(0);
v___x_4951_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4949_, v_mvarId_4936_, v___x_4950_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_);
return v___x_4951_;
}
else
{
lean_object* v___x_4952_; lean_object* v___x_4954_; 
lean_dec(v_mvarId_4936_);
v___x_4952_ = lean_box(0);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 0, v___x_4952_);
v___x_4954_ = v___x_4946_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4952_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
else
{
lean_object* v_a_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4964_; 
lean_dec(v_mvarId_4936_);
v_a_4957_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4959_ = v___x_4943_;
v_isShared_4960_ = v_isSharedCheck_4964_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_a_4957_);
lean_dec(v___x_4943_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4964_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v___x_4962_; 
if (v_isShared_4960_ == 0)
{
v___x_4962_ = v___x_4959_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_a_4957_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4965_, lean_object* v_config_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_Lean_MVarId_contradiction(v_mvarId_4965_, v_config_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
lean_dec(v_a_4970_);
lean_dec_ref(v_a_4969_);
lean_dec(v_a_4968_);
lean_dec_ref(v_a_4967_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5035_; uint8_t v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5035_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_5036_ = 0;
v___x_5037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_5038_ = l_Lean_registerTraceClass(v___x_5035_, v___x_5036_, v___x_5037_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_5040_;
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
