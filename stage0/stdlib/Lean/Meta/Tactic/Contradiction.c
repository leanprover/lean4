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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "elimEmptyInductive, number subgoals: "};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "elimEmptyInductive out-of-fuel"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__5 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__5_value;
static lean_once_cell_t l_Lean_Meta_ElimEmptyInductive_elim___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__1 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__2 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__3 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__4 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.MetavarContext"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__0_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.isLevelMVarAssignable"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__1 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__1_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unknown universe metavariable "};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__2 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_1184__boxed_163_; size_t v_x_1185__boxed_164_; lean_object* v_res_165_; 
v_x_1184__boxed_163_ = lean_unbox_usize(v_x_159_);
lean_dec(v_x_159_);
v_x_1185__boxed_164_ = lean_unbox_usize(v_x_160_);
lean_dec(v_x_160_);
v_res_165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_158_, v_x_1184__boxed_163_, v_x_1185__boxed_164_, v_x_161_, v_x_162_);
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
lean_object* v___x_177_; lean_object* v_mctx_178_; lean_object* v_cache_179_; lean_object* v_zetaDeltaFVarIds_180_; lean_object* v_postponed_181_; lean_object* v_diag_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_209_; 
v___x_177_ = lean_st_ref_take(v___y_175_);
v_mctx_178_ = lean_ctor_get(v___x_177_, 0);
v_cache_179_ = lean_ctor_get(v___x_177_, 1);
v_zetaDeltaFVarIds_180_ = lean_ctor_get(v___x_177_, 2);
v_postponed_181_ = lean_ctor_get(v___x_177_, 3);
v_diag_182_ = lean_ctor_get(v___x_177_, 4);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_209_ == 0)
{
v___x_184_ = v___x_177_;
v_isShared_185_ = v_isSharedCheck_209_;
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
v_isShared_185_ = v_isSharedCheck_209_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_depth_186_; lean_object* v_levelAssignDepth_187_; lean_object* v_mvarCounter_188_; lean_object* v_lDepth_189_; lean_object* v_decls_190_; lean_object* v_userNames_191_; lean_object* v_lAssignment_192_; lean_object* v_eAssignment_193_; lean_object* v_dAssignment_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_208_; 
v_depth_186_ = lean_ctor_get(v_mctx_178_, 0);
v_levelAssignDepth_187_ = lean_ctor_get(v_mctx_178_, 1);
v_mvarCounter_188_ = lean_ctor_get(v_mctx_178_, 2);
v_lDepth_189_ = lean_ctor_get(v_mctx_178_, 3);
v_decls_190_ = lean_ctor_get(v_mctx_178_, 4);
v_userNames_191_ = lean_ctor_get(v_mctx_178_, 5);
v_lAssignment_192_ = lean_ctor_get(v_mctx_178_, 6);
v_eAssignment_193_ = lean_ctor_get(v_mctx_178_, 7);
v_dAssignment_194_ = lean_ctor_get(v_mctx_178_, 8);
v_isSharedCheck_208_ = !lean_is_exclusive(v_mctx_178_);
if (v_isSharedCheck_208_ == 0)
{
v___x_196_ = v_mctx_178_;
v_isShared_197_ = v_isSharedCheck_208_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_dAssignment_194_);
lean_inc(v_eAssignment_193_);
lean_inc(v_lAssignment_192_);
lean_inc(v_userNames_191_);
lean_inc(v_decls_190_);
lean_inc(v_lDepth_189_);
lean_inc(v_mvarCounter_188_);
lean_inc(v_levelAssignDepth_187_);
lean_inc(v_depth_186_);
lean_dec(v_mctx_178_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_208_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_193_, v_mvarId_173_, v_val_174_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 7, v___x_198_);
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_depth_186_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_levelAssignDepth_187_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_mvarCounter_188_);
lean_ctor_set(v_reuseFailAlloc_207_, 3, v_lDepth_189_);
lean_ctor_set(v_reuseFailAlloc_207_, 4, v_decls_190_);
lean_ctor_set(v_reuseFailAlloc_207_, 5, v_userNames_191_);
lean_ctor_set(v_reuseFailAlloc_207_, 6, v_lAssignment_192_);
lean_ctor_set(v_reuseFailAlloc_207_, 7, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_207_, 8, v_dAssignment_194_);
v___x_200_ = v_reuseFailAlloc_207_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_200_);
v___x_202_ = v___x_184_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_cache_179_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_zetaDeltaFVarIds_180_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_postponed_181_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_diag_182_);
v___x_202_ = v_reuseFailAlloc_206_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_st_ref_set(v___y_175_, v___x_202_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object* v_mvarId_210_, lean_object* v_val_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_210_, v_val_211_, v___y_212_);
lean_dec(v___y_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object* v_mvarId_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___x_222_; 
lean_inc(v_mvarId_216_);
v___x_222_ = l_Lean_MVarId_getType(v_mvarId_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_267_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_267_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_267_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_267_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___f_227_; lean_object* v___x_228_; 
v___f_227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
v___x_228_ = lean_find_expr(v___f_227_, v_a_223_);
lean_dec(v_a_223_);
if (lean_obj_tag(v___x_228_) == 1)
{
lean_object* v_val_229_; lean_object* v___x_230_; 
lean_del_object(v___x_225_);
v_val_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_229_);
lean_dec_ref(v___x_228_);
lean_inc(v_mvarId_216_);
v___x_230_ = l_Lean_MVarId_getType(v_mvarId_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v___x_230_);
v___x_232_ = l_Lean_Expr_appArg_x21(v_val_229_);
lean_dec(v_val_229_);
lean_inc(v_a_218_);
v___x_233_ = l_Lean_Meta_mkFalseElim(v_a_231_, v___x_232_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_244_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref(v___x_233_);
v___x_235_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_216_, v_a_234_, v_a_218_);
lean_dec(v_a_218_);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v___x_235_, 0);
lean_dec(v_unused_245_);
v___x_237_ = v___x_235_;
v_isShared_238_ = v_isSharedCheck_244_;
goto v_resetjp_236_;
}
else
{
lean_dec(v___x_235_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_244_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_239_ = 1;
v___x_240_ = lean_box(v___x_239_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_240_);
v___x_242_ = v___x_237_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_a_218_);
lean_dec(v_mvarId_216_);
v_a_246_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_233_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_233_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec(v_val_229_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_mvarId_216_);
v_a_254_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_230_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_230_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
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
uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
lean_dec(v___x_228_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_mvarId_216_);
v___x_262_ = 0;
v___x_263_ = lean_box(v___x_262_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_263_);
v___x_265_ = v___x_225_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_mvarId_216_);
v_a_268_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_222_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_222_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object* v_mvarId_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object* v_mvarId_283_, lean_object* v_val_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_283_, v_val_284_, v___y_286_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object* v_mvarId_291_, lean_object* v_val_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(v_mvarId_291_, v_val_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object* v_00_u03b2_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_x_300_, v_x_301_, v_x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_304_, lean_object* v_x_305_, size_t v_x_306_, size_t v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_305_, v_x_306_, v_x_307_, v_x_308_, v_x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
size_t v_x_1557__boxed_317_; size_t v_x_1558__boxed_318_; lean_object* v_res_319_; 
v_x_1557__boxed_317_ = lean_unbox_usize(v_x_313_);
lean_dec(v_x_313_);
v_x_1558__boxed_318_ = lean_unbox_usize(v_x_314_);
lean_dec(v_x_314_);
v_res_319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_311_, v_x_312_, v_x_1557__boxed_317_, v_x_1558__boxed_318_, v_x_315_, v_x_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_320_, lean_object* v_n_321_, lean_object* v_k_322_, lean_object* v_v_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v_n_321_, v_k_322_, v_v_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_325_, size_t v_depth_326_, lean_object* v_keys_327_, lean_object* v_vals_328_, lean_object* v_heq_329_, lean_object* v_i_330_, lean_object* v_entries_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_326_, v_keys_327_, v_vals_328_, v_i_330_, v_entries_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_333_, lean_object* v_depth_334_, lean_object* v_keys_335_, lean_object* v_vals_336_, lean_object* v_heq_337_, lean_object* v_i_338_, lean_object* v_entries_339_){
_start:
{
size_t v_depth_boxed_340_; lean_object* v_res_341_; 
v_depth_boxed_340_ = lean_unbox_usize(v_depth_334_);
lean_dec(v_depth_334_);
v_res_341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_333_, v_depth_boxed_340_, v_keys_335_, v_vals_336_, v_heq_337_, v_i_338_, v_entries_339_);
lean_dec_ref(v_vals_336_);
lean_dec_ref(v_keys_335_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_343_, v_x_344_, v_x_345_, v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* v_fvarId_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_358_; 
lean_inc_ref(v_a_349_);
v___x_358_ = l_Lean_FVarId_getType___redArg(v_fvarId_348_, v_a_349_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref(v___x_358_);
lean_inc(v_a_352_);
v___x_360_ = l_Lean_Meta_whnfD(v_a_359_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_387_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_387_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_387_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_387_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Expr_getAppFn(v_a_361_);
lean_dec(v_a_361_);
if (lean_obj_tag(v___x_365_) == 4)
{
lean_object* v_declName_366_; lean_object* v___x_367_; lean_object* v_env_368_; uint8_t v___x_369_; lean_object* v___x_370_; 
v_declName_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_declName_366_);
lean_dec_ref(v___x_365_);
v___x_367_ = lean_st_ref_get(v_a_352_);
lean_dec(v_a_352_);
v_env_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_env_368_);
lean_dec(v___x_367_);
v___x_369_ = 0;
v___x_370_ = l_Lean_Environment_find_x3f(v_env_368_, v_declName_366_, v___x_369_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_del_object(v___x_363_);
goto v___jp_354_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref(v___x_370_);
if (lean_obj_tag(v_val_371_) == 5)
{
lean_object* v_val_372_; lean_object* v_numIndices_373_; lean_object* v_ctors_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_val_372_ = lean_ctor_get(v_val_371_, 0);
lean_inc_ref(v_val_372_);
lean_dec_ref(v_val_371_);
v_numIndices_373_ = lean_ctor_get(v_val_372_, 2);
lean_inc(v_numIndices_373_);
v_ctors_374_ = lean_ctor_get(v_val_372_, 4);
lean_inc(v_ctors_374_);
lean_dec_ref(v_val_372_);
v___x_375_ = l_List_lengthTR___redArg(v_ctors_374_);
lean_dec(v_ctors_374_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_nat_dec_eq(v___x_375_, v___x_376_);
lean_dec(v___x_375_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_378_ = lean_nat_dec_lt(v___x_376_, v_numIndices_373_);
lean_dec(v_numIndices_373_);
v___x_379_ = lean_box(v___x_378_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_379_);
v___x_381_ = v___x_363_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_385_; 
lean_dec(v_numIndices_373_);
v___x_383_ = lean_box(v___x_377_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_383_);
v___x_385_ = v___x_363_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
lean_dec(v_val_371_);
lean_del_object(v___x_363_);
goto v___jp_354_;
}
}
}
else
{
lean_dec_ref(v___x_365_);
lean_del_object(v___x_363_);
lean_dec(v_a_352_);
goto v___jp_354_;
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_a_352_);
v_a_388_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_360_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_360_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
v_a_396_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_358_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_358_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
v___jp_354_:
{
uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = 0;
v___x_356_ = lean_box(v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object* v_fvarId_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object* v_s_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_SavedState_restore___redArg(v_s_411_, v___y_414_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object* v_s_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(v_s_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v_s_419_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object* v_x_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = lean_apply_6(v_x_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, lean_box(0));
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* v_mvarId_451_, lean_object* v_x_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___f_459_; lean_object* v___x_460_; 
v___f_459_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_459_, 0, v_x_452_);
lean_closure_set(v___f_459_, 1, v___y_453_);
v___x_460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_451_, v___f_459_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
return v___x_460_;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object* v_mvarId_469_, lean_object* v_x_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_469_, v_x_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object* v_00_u03b1_478_, lean_object* v_mvarId_479_, lean_object* v_x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_479_, v_x_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object* v_00_u03b1_488_, lean_object* v_mvarId_489_, lean_object* v_x_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(v_00_u03b1_488_, v_mvarId_489_, v_x_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_options_504_; uint8_t v_hasTrace_505_; 
v_options_504_ = lean_ctor_get(v___y_502_, 2);
v_hasTrace_505_ = lean_ctor_get_uint8(v_options_504_, sizeof(void*)*1);
if (v_hasTrace_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_cls_501_);
v___x_506_ = lean_box(v_hasTrace_505_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
else
{
lean_object* v_inheritedTraceOptions_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_inheritedTraceOptions_508_ = lean_ctor_get(v___y_502_, 13);
v___x_509_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_510_ = l_Lean_Name_append(v___x_509_, v_cls_501_);
v___x_511_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_508_, v_options_504_, v___x_510_);
lean_dec(v___x_510_);
v___x_512_ = lean_box(v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_514_, v___y_515_);
lean_dec_ref(v___y_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_518_, v___y_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5(lean_object* v_x_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Meta_saveState___redArg(v___y_537_, v___y_539_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___y_544_; lean_object* v___y_545_; uint8_t v___y_546_; lean_object* v___y_565_; lean_object* v_a_566_; lean_object* v___x_569_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref(v___x_541_);
lean_inc(v___y_539_);
lean_inc(v___y_537_);
v___x_569_ = lean_apply_6(v_x_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, lean_box(0));
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; uint8_t v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
v___x_571_ = lean_unbox(v_a_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_dec_ref(v___x_569_);
v___x_572_ = l_Lean_Meta_SavedState_restore___redArg(v_a_542_, v___y_537_, v___y_539_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec(v_a_542_);
lean_dec(v___y_539_);
lean_dec(v___y_537_);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_572_, 0);
lean_dec(v_unused_580_);
v___x_574_ = v___x_572_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_dec(v___x_572_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v_a_570_);
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_570_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_a_570_);
v_a_581_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_572_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_572_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
lean_inc(v_a_581_);
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v___y_565_ = v___x_586_;
v_a_566_ = v_a_581_;
goto v___jp_564_;
}
}
}
}
else
{
lean_dec(v_a_570_);
lean_dec(v_a_542_);
lean_dec(v___y_539_);
lean_dec(v___y_537_);
return v___x_569_;
}
}
else
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_589_);
v___y_565_ = v___x_569_;
v_a_566_ = v_a_589_;
goto v___jp_564_;
}
v___jp_543_:
{
if (v___y_546_ == 0)
{
lean_object* v___x_547_; 
lean_dec_ref(v___y_544_);
v___x_547_ = l_Lean_Meta_SavedState_restore___redArg(v_a_542_, v___y_537_, v___y_539_);
lean_dec(v___y_539_);
lean_dec(v___y_537_);
lean_dec(v_a_542_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_547_, 0);
lean_dec(v_unused_555_);
v___x_549_ = v___x_547_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_dec(v___x_547_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 1);
lean_ctor_set(v___x_549_, 0, v___y_545_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___y_545_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v___y_545_);
v_a_556_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_547_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_547_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_dec_ref(v___y_545_);
lean_dec(v_a_542_);
lean_dec(v___y_539_);
lean_dec(v___y_537_);
return v___y_544_;
}
}
v___jp_564_:
{
uint8_t v___x_567_; 
v___x_567_ = l_Lean_Exception_isInterrupt(v_a_566_);
if (v___x_567_ == 0)
{
uint8_t v___x_568_; 
lean_inc_ref(v_a_566_);
v___x_568_ = l_Lean_Exception_isRuntime(v_a_566_);
v___y_544_ = v___y_565_;
v___y_545_ = v_a_566_;
v___y_546_ = v___x_568_;
goto v___jp_543_;
}
else
{
v___y_544_ = v___y_565_;
v___y_545_ = v_a_566_;
v___y_546_ = v___x_567_;
goto v___jp_543_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v_x_534_);
v_a_590_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_541_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_541_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5___boxed(lean_object* v_x_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5(v_x_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4(lean_object* v_msgData_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; lean_object* v_env_613_; lean_object* v___x_614_; lean_object* v_mctx_615_; lean_object* v_lctx_616_; lean_object* v_options_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_612_ = lean_st_ref_get(v___y_610_);
v_env_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc_ref(v_env_613_);
lean_dec(v___x_612_);
v___x_614_ = lean_st_ref_get(v___y_608_);
v_mctx_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_mctx_615_);
lean_dec(v___x_614_);
v_lctx_616_ = lean_ctor_get(v___y_607_, 2);
v_options_617_ = lean_ctor_get(v___y_609_, 2);
lean_inc_ref(v_options_617_);
lean_inc_ref(v_lctx_616_);
v___x_618_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_618_, 0, v_env_613_);
lean_ctor_set(v___x_618_, 1, v_mctx_615_);
lean_ctor_set(v___x_618_, 2, v_lctx_616_);
lean_ctor_set(v___x_618_, 3, v_options_617_);
v___x_619_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v_msgData_606_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4___boxed(lean_object* v_msgData_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4(v_msgData_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_627_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_628_; double v___x_629_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_float_of_nat(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(lean_object* v_cls_633_, lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_ref_640_; lean_object* v___x_641_; lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_686_; 
v_ref_640_ = lean_ctor_get(v___y_637_, 5);
v___x_641_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4(v_msg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_686_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_686_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_686_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v_traceState_647_; lean_object* v_env_648_; lean_object* v_nextMacroScope_649_; lean_object* v_ngen_650_; lean_object* v_auxDeclNGen_651_; lean_object* v_cache_652_; lean_object* v_messages_653_; lean_object* v_infoState_654_; lean_object* v_snapshotTasks_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_685_; 
v___x_646_ = lean_st_ref_take(v___y_638_);
v_traceState_647_ = lean_ctor_get(v___x_646_, 4);
v_env_648_ = lean_ctor_get(v___x_646_, 0);
v_nextMacroScope_649_ = lean_ctor_get(v___x_646_, 1);
v_ngen_650_ = lean_ctor_get(v___x_646_, 2);
v_auxDeclNGen_651_ = lean_ctor_get(v___x_646_, 3);
v_cache_652_ = lean_ctor_get(v___x_646_, 5);
v_messages_653_ = lean_ctor_get(v___x_646_, 6);
v_infoState_654_ = lean_ctor_get(v___x_646_, 7);
v_snapshotTasks_655_ = lean_ctor_get(v___x_646_, 8);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_685_ == 0)
{
v___x_657_ = v___x_646_;
v_isShared_658_ = v_isSharedCheck_685_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snapshotTasks_655_);
lean_inc(v_infoState_654_);
lean_inc(v_messages_653_);
lean_inc(v_cache_652_);
lean_inc(v_traceState_647_);
lean_inc(v_auxDeclNGen_651_);
lean_inc(v_ngen_650_);
lean_inc(v_nextMacroScope_649_);
lean_inc(v_env_648_);
lean_dec(v___x_646_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_685_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint64_t v_tid_659_; lean_object* v_traces_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_684_; 
v_tid_659_ = lean_ctor_get_uint64(v_traceState_647_, sizeof(void*)*1);
v_traces_660_ = lean_ctor_get(v_traceState_647_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_traceState_647_);
if (v_isSharedCheck_684_ == 0)
{
v___x_662_ = v_traceState_647_;
v_isShared_663_ = v_isSharedCheck_684_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_traces_660_);
lean_dec(v_traceState_647_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_684_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; double v___x_665_; uint8_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_664_ = lean_box(0);
v___x_665_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0);
v___x_666_ = 0;
v___x_667_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__1));
v___x_668_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_668_, 0, v_cls_633_);
lean_ctor_set(v___x_668_, 1, v___x_664_);
lean_ctor_set(v___x_668_, 2, v___x_667_);
lean_ctor_set_float(v___x_668_, sizeof(void*)*3, v___x_665_);
lean_ctor_set_float(v___x_668_, sizeof(void*)*3 + 8, v___x_665_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*3 + 16, v___x_666_);
v___x_669_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__2));
v___x_670_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v_a_642_);
lean_ctor_set(v___x_670_, 2, v___x_669_);
lean_inc(v_ref_640_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_ref_640_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_PersistentArray_push___redArg(v_traces_660_, v___x_671_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_672_);
v___x_674_ = v___x_662_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_672_);
lean_ctor_set_uint64(v_reuseFailAlloc_683_, sizeof(void*)*1, v_tid_659_);
v___x_674_ = v_reuseFailAlloc_683_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v___x_674_);
v___x_676_ = v___x_657_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_env_648_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_nextMacroScope_649_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_ngen_650_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_auxDeclNGen_651_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_682_, 5, v_cache_652_);
lean_ctor_set(v_reuseFailAlloc_682_, 6, v_messages_653_);
lean_ctor_set(v_reuseFailAlloc_682_, 7, v_infoState_654_);
lean_ctor_set(v_reuseFailAlloc_682_, 8, v_snapshotTasks_655_);
v___x_676_ = v_reuseFailAlloc_682_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_677_ = lean_st_ref_set(v___y_638_, v___x_676_);
v___x_678_ = lean_box(0);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_678_);
v___x_680_ = v___x_644_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___boxed(lean_object* v_cls_687_, lean_object* v_msg_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(v_cls_687_, v_msg_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_702_, lean_object* v_mvarId_703_, lean_object* v_fields_704_, lean_object* v_sz_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
size_t v_sz_boxed_715_; size_t v___x_16242__boxed_716_; uint8_t v___x_16244__boxed_717_; lean_object* v_res_718_; 
v_sz_boxed_715_ = lean_unbox_usize(v_sz_705_);
lean_dec(v_sz_705_);
v___x_16242__boxed_716_ = lean_unbox_usize(v___x_706_);
lean_dec(v___x_706_);
v___x_16244__boxed_717_ = lean_unbox(v___x_708_);
v_res_718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_702_, v_mvarId_703_, v_fields_704_, v_sz_boxed_715_, v___x_16242__boxed_716_, v___x_707_, v___x_16244__boxed_717_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec_ref(v_fields_704_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_719_, lean_object* v_as_720_, size_t v_sz_721_, size_t v_i_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = lean_usize_dec_lt(v_i_722_, v_sz_721_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v_b_723_);
return v___x_731_;
}
else
{
lean_object* v_a_732_; lean_object* v_toInductionSubgoal_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_b_723_);
v_a_732_ = lean_array_uget(v_as_720_, v_i_722_);
v_toInductionSubgoal_733_ = lean_ctor_get(v_a_732_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_a_732_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v_a_732_, 1);
lean_dec(v_unused_775_);
v___x_735_ = v_a_732_;
v_isShared_736_ = v_isSharedCheck_774_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_toInductionSubgoal_733_);
lean_dec(v_a_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_774_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_mvarId_737_; lean_object* v_fields_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; size_t v_sz_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___f_747_; lean_object* v___x_748_; 
v_mvarId_737_ = lean_ctor_get(v_toInductionSubgoal_733_, 0);
lean_inc(v_mvarId_737_);
v_fields_738_ = lean_ctor_get(v_toInductionSubgoal_733_, 1);
lean_inc_ref(v_fields_738_);
v___x_739_ = lean_box(0);
v___x_740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_nat_dec_eq(v_val_719_, v___x_741_);
v_sz_743_ = lean_array_size(v_fields_738_);
v___x_744_ = lean_box_usize(v_sz_743_);
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_746_ = lean_box(v___x_742_);
lean_inc(v_mvarId_737_);
v___f_747_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_747_, 0, v_toInductionSubgoal_733_);
lean_closure_set(v___f_747_, 1, v_mvarId_737_);
lean_closure_set(v___f_747_, 2, v_fields_738_);
lean_closure_set(v___f_747_, 3, v___x_744_);
lean_closure_set(v___f_747_, 4, v___x_745_);
lean_closure_set(v___f_747_, 5, v___x_740_);
lean_closure_set(v___f_747_, 6, v___x_746_);
lean_inc(v___y_728_);
lean_inc_ref(v___y_727_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
lean_inc(v___y_724_);
v___x_748_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_737_, v___f_747_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_765_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_765_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_765_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_765_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
uint8_t v___x_753_; 
v___x_753_ = lean_unbox(v_a_749_);
lean_dec(v_a_749_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
v___x_754_ = lean_box(v___x_742_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_739_);
lean_ctor_set(v___x_735_, 0, v___x_755_);
v___x_757_ = v___x_735_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_739_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_757_);
v___x_759_ = v___x_751_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
size_t v___x_762_; size_t v___x_763_; 
lean_del_object(v___x_751_);
lean_del_object(v___x_735_);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_add(v_i_722_, v___x_762_);
v_i_722_ = v___x_763_;
v_b_723_ = v___x_740_;
goto _start;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_del_object(v___x_735_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
v_a_766_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_748_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_748_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_786_, lean_object* v_fvarId_787_, lean_object* v___x_788_, uint8_t v___x_789_, lean_object* v___x_790_, lean_object* v_val_791_, uint8_t v___x_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_795_);
lean_inc_ref(v___y_794_);
v___x_799_ = l_Lean_MVarId_cases(v_mvarId_786_, v_fvarId_787_, v___x_788_, v___x_789_, v___x_790_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
v___x_833_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_834_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_833_, v___y_796_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_857_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_857_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_857_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_857_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___x_839_; 
v___x_839_ = lean_unbox(v_a_835_);
lean_dec(v_a_835_);
if (v___x_839_ == 0)
{
lean_del_object(v___x_837_);
v___y_802_ = v___y_793_;
v___y_803_ = v___y_794_;
v___y_804_ = v___y_795_;
v___y_805_ = v___y_796_;
v___y_806_ = v___y_797_;
goto v___jp_801_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_840_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_841_ = lean_array_get_size(v_a_800_);
v___x_842_ = l_Nat_reprFast(v___x_841_);
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 3);
lean_ctor_set(v___x_837_, 0, v___x_842_);
v___x_844_ = v___x_837_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_856_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = l_Lean_MessageData_ofFormat(v___x_844_);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_840_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(v___x_833_, v___x_846_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_dec_ref(v___x_847_);
v___y_802_ = v___y_793_;
v___y_803_ = v___y_794_;
v___y_804_ = v___y_795_;
v___y_805_ = v___y_796_;
v___y_806_ = v___y_797_;
goto v___jp_801_;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_a_800_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_800_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
return v___x_834_;
}
v___jp_801_:
{
lean_object* v___x_807_; size_t v_sz_808_; size_t v___x_809_; lean_object* v___x_810_; 
v___x_807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_808_ = lean_array_size(v_a_800_);
v___x_809_ = ((size_t)0ULL);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_791_, v_a_800_, v_sz_808_, v___x_809_, v___x_807_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v_a_800_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_824_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_824_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_824_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_824_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_fst_815_; 
v_fst_815_ = lean_ctor_get(v_a_811_, 0);
lean_inc(v_fst_815_);
lean_dec(v_a_811_);
if (lean_obj_tag(v_fst_815_) == 0)
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_box(v___x_792_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
else
{
lean_object* v_val_820_; lean_object* v___x_822_; 
v_val_820_ = lean_ctor_get(v_fst_815_, 0);
lean_inc(v_val_820_);
lean_dec_ref(v_fst_815_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v_val_820_);
v___x_822_ = v___x_813_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_val_820_);
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
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
v_a_825_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_810_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_810_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_900_; 
lean_dec(v___y_793_);
v_a_858_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_900_ == 0)
{
v___x_860_ = v___x_799_;
v_isShared_861_ = v_isSharedCheck_900_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_799_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_900_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
uint8_t v___y_863_; uint8_t v___x_898_; 
v___x_898_ = l_Lean_Exception_isInterrupt(v_a_858_);
if (v___x_898_ == 0)
{
uint8_t v___x_899_; 
lean_inc(v_a_858_);
v___x_899_ = l_Lean_Exception_isRuntime(v_a_858_);
v___y_863_ = v___x_899_;
goto v___jp_862_;
}
else
{
v___y_863_ = v___x_898_;
goto v___jp_862_;
}
v___jp_862_:
{
if (v___y_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_del_object(v___x_860_);
v___x_864_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_865_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_864_, v___y_796_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_894_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_894_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_894_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_894_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
uint8_t v___x_870_; 
v___x_870_ = lean_unbox(v_a_866_);
lean_dec(v_a_866_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_873_; 
lean_dec(v_a_858_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
v___x_871_ = lean_box(v___x_789_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_871_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_del_object(v___x_868_);
v___x_875_ = l_Lean_Exception_toMessageData(v_a_858_);
v___x_876_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(v___x_864_, v___x_875_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_884_; 
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v___x_876_, 0);
lean_dec(v_unused_885_);
v___x_878_ = v___x_876_;
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
else
{
lean_dec(v___x_876_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_box(v___x_789_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_880_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v_a_886_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_876_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_876_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
else
{
lean_dec(v_a_858_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v___x_865_;
}
}
else
{
lean_object* v___x_896_; 
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
if (v_isShared_861_ == 0)
{
v___x_896_ = v___x_860_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_858_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_901_, lean_object* v_fvarId_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v_val_906_, lean_object* v___x_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
uint8_t v___x_16364__boxed_914_; uint8_t v___x_16367__boxed_915_; lean_object* v_res_916_; 
v___x_16364__boxed_914_ = lean_unbox(v___x_904_);
v___x_16367__boxed_915_ = lean_unbox(v___x_907_);
v_res_916_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_901_, v_fvarId_902_, v___x_903_, v___x_16364__boxed_914_, v___x_905_, v_val_906_, v___x_16367__boxed_915_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v_val_906_);
return v_res_916_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__6(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__5));
v___x_919_ = l_Lean_stringToMessageData(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_920_, lean_object* v_fvarId_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_932_ = lean_st_ref_get(v_a_922_);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_nat_dec_eq(v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___f_944_; lean_object* v___x_945_; 
v___x_935_ = lean_st_ref_take(v_a_922_);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_sub(v___x_935_, v___x_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_st_ref_set(v_a_922_, v___x_937_);
v___x_939_ = 1;
v___x_940_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_941_ = lean_box(0);
v___x_942_ = lean_box(v___x_934_);
v___x_943_ = lean_box(v___x_939_);
v___f_944_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_944_, 0, v_mvarId_920_);
lean_closure_set(v___f_944_, 1, v_fvarId_921_);
lean_closure_set(v___f_944_, 2, v___x_940_);
lean_closure_set(v___f_944_, 3, v___x_942_);
lean_closure_set(v___f_944_, 4, v___x_941_);
lean_closure_set(v___f_944_, 5, v___x_932_);
lean_closure_set(v___f_944_, 6, v___x_943_);
v___x_945_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5(v___f_944_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v___x_932_);
lean_dec(v_a_922_);
lean_dec(v_fvarId_921_);
lean_dec(v_mvarId_920_);
v___x_946_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_947_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_946_, v_a_925_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; uint8_t v___x_949_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref(v___x_947_);
v___x_949_ = lean_unbox(v_a_948_);
lean_dec(v_a_948_);
if (v___x_949_ == 0)
{
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
goto v___jp_928_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__6, &l_Lean_Meta_ElimEmptyInductive_elim___closed__6_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__6);
v___x_951_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(v___x_946_, v___x_950_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_dec_ref(v___x_951_);
goto v___jp_928_;
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v___x_947_;
}
}
v___jp_928_:
{
uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = 0;
v___x_930_ = lean_box(v___x_929_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_960_, lean_object* v___x_961_, lean_object* v_as_962_, size_t v_sz_963_, size_t v_i_964_, lean_object* v_b_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_a_973_; uint8_t v___x_977_; 
v___x_977_ = lean_usize_dec_lt(v_i_964_, v_sz_963_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___x_961_);
lean_dec_ref(v___x_960_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v_b_965_);
return v___x_978_;
}
else
{
lean_object* v_subst_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_a_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
lean_dec_ref(v_b_965_);
v_subst_979_ = lean_ctor_get(v___x_960_, 2);
v___x_980_ = lean_box(0);
v___x_981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_982_ = lean_array_uget_borrowed(v_as_962_, v_i_964_);
lean_inc(v_subst_979_);
v___x_983_ = l_Lean_Meta_FVarSubst_apply(v_subst_979_, v_a_982_);
v___x_984_ = l_Lean_Expr_isFVar(v___x_983_);
if (v___x_984_ == 0)
{
lean_dec_ref(v___x_983_);
v_a_973_ = v___x_981_;
goto v___jp_972_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = l_Lean_Expr_fvarId_x21(v___x_983_);
lean_dec_ref(v___x_983_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___x_985_);
v___x_986_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_985_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; uint8_t v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref(v___x_986_);
v___x_988_ = lean_unbox(v_a_987_);
lean_dec(v_a_987_);
if (v___x_988_ == 0)
{
lean_dec(v___x_985_);
v_a_973_ = v___x_981_;
goto v___jp_972_;
}
else
{
lean_object* v___x_989_; 
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc(v___x_961_);
v___x_989_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_961_, v___x_985_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1000_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1000_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1000_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___x_994_; 
v___x_994_ = lean_unbox(v_a_990_);
if (v___x_994_ == 0)
{
lean_del_object(v___x_992_);
lean_dec(v_a_990_);
v_a_973_ = v___x_981_;
goto v___jp_972_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___x_961_);
lean_dec_ref(v___x_960_);
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v_a_990_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_980_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_996_);
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___x_961_);
lean_dec_ref(v___x_960_);
v_a_1001_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_989_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_989_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v___x_985_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___x_961_);
lean_dec_ref(v___x_960_);
v_a_1009_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_986_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_986_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
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
}
v___jp_972_:
{
size_t v___x_974_; size_t v___x_975_; 
v___x_974_ = ((size_t)1ULL);
v___x_975_ = lean_usize_add(v_i_964_, v___x_974_);
v_i_964_ = v___x_975_;
v_b_965_ = v_a_973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_1017_, lean_object* v_mvarId_1018_, lean_object* v_fields_1019_, size_t v_sz_1020_, size_t v___x_1021_, lean_object* v___x_1022_, uint8_t v___x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_1017_, v_mvarId_1018_, v_fields_1019_, v_sz_1020_, v___x_1021_, v___x_1022_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1044_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1044_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1044_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_fst_1035_; 
v_fst_1035_ = lean_ctor_get(v_a_1031_, 0);
lean_inc(v_fst_1035_);
lean_dec(v_a_1031_);
if (lean_obj_tag(v_fst_1035_) == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_box(v___x_1023_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1036_);
v___x_1038_ = v___x_1033_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
lean_object* v_val_1040_; lean_object* v___x_1042_; 
v_val_1040_ = lean_ctor_get(v_fst_1035_, 0);
lean_inc(v_val_1040_);
lean_dec_ref(v_fst_1035_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v_val_1040_);
v___x_1042_ = v___x_1033_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_val_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1030_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1030_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1053_, lean_object* v_as_1054_, lean_object* v_sz_1055_, lean_object* v_i_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
size_t v_sz_boxed_1064_; size_t v_i_boxed_1065_; lean_object* v_res_1066_; 
v_sz_boxed_1064_ = lean_unbox_usize(v_sz_1055_);
lean_dec(v_sz_1055_);
v_i_boxed_1065_ = lean_unbox_usize(v_i_1056_);
lean_dec(v_i_1056_);
v_res_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1053_, v_as_1054_, v_sz_boxed_1064_, v_i_boxed_1065_, v_b_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec_ref(v_as_1054_);
lean_dec(v_val_1053_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1067_, lean_object* v___x_1068_, lean_object* v_as_1069_, lean_object* v_sz_1070_, lean_object* v_i_1071_, lean_object* v_b_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
size_t v_sz_boxed_1079_; size_t v_i_boxed_1080_; lean_object* v_res_1081_; 
v_sz_boxed_1079_ = lean_unbox_usize(v_sz_1070_);
lean_dec(v_sz_1070_);
v_i_boxed_1080_ = lean_unbox_usize(v_i_1071_);
lean_dec(v_i_1071_);
v_res_1081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1067_, v___x_1068_, v_as_1069_, v_sz_boxed_1079_, v_i_boxed_1080_, v_b_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec_ref(v_as_1069_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1082_, lean_object* v_fvarId_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1082_, v_fvarId_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* v_cls_1091_, lean_object* v_msg_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(v_cls_1091_, v_msg_1092_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_cls_1100_, lean_object* v_msg_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_cls_1100_, v_msg_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Meta_saveState___redArg(v___y_1111_, v___y_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___y_1118_; lean_object* v___y_1119_; uint8_t v___y_1120_; lean_object* v___y_1139_; lean_object* v_a_1140_; lean_object* v___x_1143_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref(v___x_1115_);
lean_inc(v___y_1113_);
lean_inc(v___y_1111_);
v___x_1143_ = lean_apply_5(v_x_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, lean_box(0));
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; uint8_t v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
v___x_1145_ = lean_unbox(v_a_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_dec_ref(v___x_1143_);
v___x_1146_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1116_, v___y_1111_, v___y_1113_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_a_1116_);
lean_dec(v___y_1113_);
lean_dec(v___y_1111_);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1146_, 0);
lean_dec(v_unused_1154_);
v___x_1148_ = v___x_1146_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1146_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1144_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_a_1144_);
v_a_1155_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1146_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1146_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
lean_inc(v_a_1155_);
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
v___y_1139_ = v___x_1160_;
v_a_1140_ = v_a_1155_;
goto v___jp_1138_;
}
}
}
}
else
{
lean_dec(v_a_1144_);
lean_dec(v_a_1116_);
lean_dec(v___y_1113_);
lean_dec(v___y_1111_);
return v___x_1143_;
}
}
else
{
lean_object* v_a_1163_; 
v_a_1163_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1163_);
v___y_1139_ = v___x_1143_;
v_a_1140_ = v_a_1163_;
goto v___jp_1138_;
}
v___jp_1117_:
{
if (v___y_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_dec_ref(v___y_1119_);
v___x_1121_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1116_, v___y_1111_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec(v___y_1111_);
lean_dec(v_a_1116_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1121_, 0);
lean_dec(v_unused_1129_);
v___x_1123_ = v___x_1121_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v___x_1121_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 1);
lean_ctor_set(v___x_1123_, 0, v___y_1118_);
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___y_1118_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___y_1118_);
v_a_1130_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1121_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1121_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_dec_ref(v___y_1118_);
lean_dec(v_a_1116_);
lean_dec(v___y_1113_);
lean_dec(v___y_1111_);
return v___y_1119_;
}
}
v___jp_1138_:
{
uint8_t v___x_1141_; 
v___x_1141_ = l_Lean_Exception_isInterrupt(v_a_1140_);
if (v___x_1141_ == 0)
{
uint8_t v___x_1142_; 
lean_inc_ref(v_a_1140_);
v___x_1142_ = l_Lean_Exception_isRuntime(v_a_1140_);
v___y_1118_ = v_a_1140_;
v___y_1119_ = v___y_1139_;
v___y_1120_ = v___x_1142_;
goto v___jp_1117_;
}
else
{
v___y_1118_ = v_a_1140_;
v___y_1119_ = v___y_1139_;
v___y_1120_ = v___x_1141_;
goto v___jp_1117_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v_x_1109_);
v_a_1164_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1115_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1115_);
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
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1179_, v_x_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1186_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1186_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1203_, lean_object* v_x_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1203_, v_x_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1211_, lean_object* v_mvarId_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1212_, v_x_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_mvarId_1221_, lean_object* v_x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1220_, v_mvarId_1221_, v_x_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1229_, lean_object* v_fuel_1230_, lean_object* v_fvarId_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
v___x_1237_ = l_Lean_MVarId_exfalso(v_mvarId_1229_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = lean_st_mk_ref(v_fuel_1230_);
lean_inc(v___x_1239_);
v___x_1240_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1238_, v_fvarId_1231_, v___x_1239_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = lean_st_ref_get(v___x_1239_);
lean_dec(v___x_1239_);
lean_dec(v___x_1245_);
if (v_isShared_1244_ == 0)
{
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1241_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
lean_dec(v___x_1239_);
return v___x_1240_;
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v_fvarId_1231_);
lean_dec(v_fuel_1230_);
v_a_1250_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1237_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1237_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1258_, lean_object* v_fuel_1259_, lean_object* v_fvarId_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1258_, v_fuel_1259_, v_fvarId_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1267_, lean_object* v___f_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
v___x_1274_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1267_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; uint8_t v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
v___x_1276_ = lean_unbox(v_a_1275_);
lean_dec(v_a_1275_);
if (v___x_1276_ == 0)
{
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec_ref(v___f_1268_);
return v___x_1274_;
}
else
{
lean_object* v___x_1277_; 
lean_dec_ref(v___x_1274_);
v___x_1277_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
return v___x_1277_;
}
}
else
{
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec_ref(v___f_1268_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1278_, lean_object* v___f_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1278_, v___f_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1286_, lean_object* v_fvarId_1287_, lean_object* v_fuel_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v___f_1294_; lean_object* v___f_1295_; lean_object* v___x_1296_; 
lean_inc(v_fvarId_1287_);
lean_inc(v_mvarId_1286_);
v___f_1294_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1294_, 0, v_mvarId_1286_);
lean_closure_set(v___f_1294_, 1, v_fuel_1288_);
lean_closure_set(v___f_1294_, 2, v_fvarId_1287_);
v___f_1295_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1295_, 0, v_fvarId_1287_);
lean_closure_set(v___f_1295_, 1, v___f_1294_);
v___x_1296_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1286_, v___f_1295_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1297_, lean_object* v_fvarId_1298_, lean_object* v_fuel_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1297_, v_fvarId_1298_, v_fuel_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1306_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1308_){
_start:
{
uint8_t v_res_1309_; lean_object* v_r_1310_; 
v_res_1309_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1308_);
v_r_1310_ = lean_box(v_res_1309_);
return v_r_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1311_, lean_object* v_acc_1312_){
_start:
{
if (lean_obj_tag(v_e_1311_) == 7)
{
lean_object* v_binderType_1313_; lean_object* v_body_1314_; uint8_t v___y_1316_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_binderType_1313_ = lean_ctor_get(v_e_1311_, 1);
v_body_1314_ = lean_ctor_get(v_e_1311_, 2);
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = lean_expr_has_loose_bvar(v_body_1314_, v___x_1320_);
if (v___x_1321_ == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Lean_Expr_isEq(v_binderType_1313_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_Expr_isHEq(v_binderType_1313_);
v___y_1316_ = v___x_1323_;
goto v___jp_1315_;
}
else
{
v___y_1316_ = v___x_1322_;
goto v___jp_1315_;
}
}
else
{
uint8_t v___x_1324_; 
v___x_1324_ = 0;
v___y_1316_ = v___x_1324_;
goto v___jp_1315_;
}
v___jp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_box(v___y_1316_);
v___x_1318_ = lean_array_push(v_acc_1312_, v___x_1317_);
v_e_1311_ = v_body_1314_;
v_acc_1312_ = v___x_1318_;
goto _start;
}
}
else
{
return v_acc_1312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1325_, lean_object* v_acc_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1325_, v_acc_1326_);
lean_dec_ref(v_e_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1330_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1332_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1330_, v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_Meta_mkGenDiseqMask(v_e_1333_);
lean_dec_ref(v_e_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___f_1342_; lean_object* v___x_5852__overap_1343_; lean_object* v___x_1344_; 
v___f_1342_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_5852__overap_1343_ = lean_panic_fn(v___f_1342_, v_msg_1336_);
v___x_1344_ = lean_apply_5(v___x_5852__overap_1343_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, lean_box(0));
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = l_Lean_Expr_hasMVar(v_e_1352_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_e_1352_);
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; lean_object* v_mctx_1358_; lean_object* v___x_1359_; lean_object* v_fst_1360_; lean_object* v_snd_1361_; lean_object* v___x_1362_; lean_object* v_cache_1363_; lean_object* v_zetaDeltaFVarIds_1364_; lean_object* v_postponed_1365_; lean_object* v_diag_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1375_; 
v___x_1357_ = lean_st_ref_get(v___y_1353_);
v_mctx_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc_ref(v_mctx_1358_);
lean_dec(v___x_1357_);
v___x_1359_ = l_Lean_instantiateMVarsCore(v_mctx_1358_, v_e_1352_);
v_fst_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_fst_1360_);
v_snd_1361_ = lean_ctor_get(v___x_1359_, 1);
lean_inc(v_snd_1361_);
lean_dec_ref(v___x_1359_);
v___x_1362_ = lean_st_ref_take(v___y_1353_);
v_cache_1363_ = lean_ctor_get(v___x_1362_, 1);
v_zetaDeltaFVarIds_1364_ = lean_ctor_get(v___x_1362_, 2);
v_postponed_1365_ = lean_ctor_get(v___x_1362_, 3);
v_diag_1366_ = lean_ctor_get(v___x_1362_, 4);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1362_, 0);
lean_dec(v_unused_1376_);
v___x_1368_ = v___x_1362_;
v_isShared_1369_ = v_isSharedCheck_1375_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_diag_1366_);
lean_inc(v_postponed_1365_);
lean_inc(v_zetaDeltaFVarIds_1364_);
lean_inc(v_cache_1363_);
lean_dec(v___x_1362_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1375_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v_snd_1361_);
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_snd_1361_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_cache_1363_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_zetaDeltaFVarIds_1364_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_postponed_1365_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_diag_1366_);
v___x_1371_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_st_ref_set(v___y_1353_, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_fst_1360_);
return v___x_1373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1377_, v___y_1378_);
lean_dec(v___y_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1381_, v___y_1383_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(lean_object* v_k_1395_, uint8_t v_allowLevelAssignments_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1396_, v_k_1395_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1402_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1402_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg___boxed(lean_object* v_k_1419_, lean_object* v_allowLevelAssignments_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1426_; lean_object* v_res_1427_; 
v_allowLevelAssignments_boxed_1426_ = lean_unbox(v_allowLevelAssignments_1420_);
v_res_1427_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(v_k_1419_, v_allowLevelAssignments_boxed_1426_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4(lean_object* v_00_u03b1_1428_, lean_object* v_k_1429_, uint8_t v_allowLevelAssignments_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(v_k_1429_, v_allowLevelAssignments_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_k_1438_, lean_object* v_allowLevelAssignments_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1445_; lean_object* v_res_1446_; 
v_allowLevelAssignments_boxed_1445_ = lean_unbox(v_allowLevelAssignments_1439_);
v_res_1446_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4(v_00_u03b1_1437_, v_k_1438_, v_allowLevelAssignments_boxed_1445_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(lean_object* v_keys_1447_, lean_object* v_vals_1448_, lean_object* v_i_1449_, lean_object* v_k_1450_){
_start:
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = lean_array_get_size(v_keys_1447_);
v___x_1452_ = lean_nat_dec_lt(v_i_1449_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_dec(v_i_1449_);
v___x_1453_ = lean_box(0);
return v___x_1453_;
}
else
{
lean_object* v_k_x27_1454_; uint8_t v___x_1455_; 
v_k_x27_1454_ = lean_array_fget_borrowed(v_keys_1447_, v_i_1449_);
v___x_1455_ = l_Lean_instBEqLevelMVarId_beq(v_k_1450_, v_k_x27_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_nat_add(v_i_1449_, v___x_1456_);
lean_dec(v_i_1449_);
v_i_1449_ = v___x_1457_;
goto _start;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_array_fget_borrowed(v_vals_1448_, v_i_1449_);
lean_dec(v_i_1449_);
lean_inc(v___x_1459_);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_keys_1461_, lean_object* v_vals_1462_, lean_object* v_i_1463_, lean_object* v_k_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(v_keys_1461_, v_vals_1462_, v_i_1463_, v_k_1464_);
lean_dec(v_k_1464_);
lean_dec_ref(v_vals_1462_);
lean_dec_ref(v_keys_1461_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_x_1466_, size_t v_x_1467_, lean_object* v_x_1468_){
_start:
{
if (lean_obj_tag(v_x_1466_) == 0)
{
lean_object* v_es_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1490_; 
v_es_1469_ = lean_ctor_get(v_x_1466_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_x_1466_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1471_ = v_x_1466_;
v_isShared_1472_ = v_isSharedCheck_1490_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_es_1469_);
lean_dec(v_x_1466_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1490_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; lean_object* v_j_1477_; lean_object* v___x_1478_; 
v___x_1473_ = lean_box(2);
v___x_1474_ = ((size_t)5ULL);
v___x_1475_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1476_ = lean_usize_land(v_x_1467_, v___x_1475_);
v_j_1477_ = lean_usize_to_nat(v___x_1476_);
v___x_1478_ = lean_array_get(v___x_1473_, v_es_1469_, v_j_1477_);
lean_dec(v_j_1477_);
lean_dec_ref(v_es_1469_);
switch(lean_obj_tag(v___x_1478_))
{
case 0:
{
lean_object* v_key_1479_; lean_object* v_val_1480_; uint8_t v___x_1481_; 
v_key_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_key_1479_);
v_val_1480_ = lean_ctor_get(v___x_1478_, 1);
lean_inc(v_val_1480_);
lean_dec_ref(v___x_1478_);
v___x_1481_ = l_Lean_instBEqLevelMVarId_beq(v_x_1468_, v_key_1479_);
lean_dec(v_key_1479_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_dec(v_val_1480_);
lean_del_object(v___x_1471_);
v___x_1482_ = lean_box(0);
return v___x_1482_;
}
else
{
lean_object* v___x_1484_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 1);
lean_ctor_set(v___x_1471_, 0, v_val_1480_);
v___x_1484_ = v___x_1471_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_val_1480_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
case 1:
{
lean_object* v_node_1486_; size_t v___x_1487_; 
lean_del_object(v___x_1471_);
v_node_1486_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_node_1486_);
lean_dec_ref(v___x_1478_);
v___x_1487_ = lean_usize_shift_right(v_x_1467_, v___x_1474_);
v_x_1466_ = v_node_1486_;
v_x_1467_ = v___x_1487_;
goto _start;
}
default: 
{
lean_object* v___x_1489_; 
lean_del_object(v___x_1471_);
v___x_1489_ = lean_box(0);
return v___x_1489_;
}
}
}
}
else
{
lean_object* v_ks_1491_; lean_object* v_vs_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_ks_1491_ = lean_ctor_get(v_x_1466_, 0);
lean_inc_ref(v_ks_1491_);
v_vs_1492_ = lean_ctor_get(v_x_1466_, 1);
lean_inc_ref(v_vs_1492_);
lean_dec_ref(v_x_1466_);
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(v_ks_1491_, v_vs_1492_, v___x_1493_, v_x_1468_);
lean_dec_ref(v_vs_1492_);
lean_dec_ref(v_ks_1491_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
size_t v_x_9857__boxed_1498_; lean_object* v_res_1499_; 
v_x_9857__boxed_1498_ = lean_unbox_usize(v_x_1496_);
lean_dec(v_x_1496_);
v_res_1499_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(v_x_1495_, v_x_9857__boxed_1498_, v_x_1497_);
lean_dec(v_x_1497_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
uint64_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = l_Lean_instHashableLevelMVarId_hash(v_x_1501_);
v___x_1503_ = lean_uint64_to_usize(v___x_1502_);
v___x_1504_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(v_x_1500_, v___x_1503_, v_x_1501_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_x_1505_, lean_object* v_x_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(v_x_1505_, v_x_1506_);
lean_dec(v_x_1506_);
return v_res_1507_;
}
}
static lean_object* _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(lean_object* v_msg_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_toApplicative_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1583_; 
v___x_1519_ = lean_obj_once(&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0, &l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0_once, _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0);
v___x_1520_ = l_ReaderT_instMonad___redArg(v___x_1519_);
v_toApplicative_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v___x_1520_, 1);
lean_dec(v_unused_1584_);
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1583_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_toApplicative_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1583_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_toFunctor_1525_; lean_object* v_toSeq_1526_; lean_object* v_toSeqLeft_1527_; lean_object* v_toSeqRight_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1581_; 
v_toFunctor_1525_ = lean_ctor_get(v_toApplicative_1521_, 0);
v_toSeq_1526_ = lean_ctor_get(v_toApplicative_1521_, 2);
v_toSeqLeft_1527_ = lean_ctor_get(v_toApplicative_1521_, 3);
v_toSeqRight_1528_ = lean_ctor_get(v_toApplicative_1521_, 4);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_toApplicative_1521_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; 
v_unused_1582_ = lean_ctor_get(v_toApplicative_1521_, 1);
lean_dec(v_unused_1582_);
v___x_1530_ = v_toApplicative_1521_;
v_isShared_1531_ = v_isSharedCheck_1581_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_toSeqRight_1528_);
lean_inc(v_toSeqLeft_1527_);
lean_inc(v_toSeq_1526_);
lean_inc(v_toFunctor_1525_);
lean_dec(v_toApplicative_1521_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1581_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___f_1532_; lean_object* v___f_1533_; lean_object* v___f_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; lean_object* v___f_1537_; lean_object* v___f_1538_; lean_object* v___f_1539_; lean_object* v___x_1541_; 
v___f_1532_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__1));
v___f_1533_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__2));
lean_inc_ref(v_toFunctor_1525_);
v___f_1534_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1534_, 0, v_toFunctor_1525_);
v___f_1535_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1535_, 0, v_toFunctor_1525_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___f_1534_);
lean_ctor_set(v___x_1536_, 1, v___f_1535_);
v___f_1537_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1537_, 0, v_toSeqRight_1528_);
v___f_1538_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1538_, 0, v_toSeqLeft_1527_);
v___f_1539_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1539_, 0, v_toSeq_1526_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 4, v___f_1537_);
lean_ctor_set(v___x_1530_, 3, v___f_1538_);
lean_ctor_set(v___x_1530_, 2, v___f_1539_);
lean_ctor_set(v___x_1530_, 1, v___f_1532_);
lean_ctor_set(v___x_1530_, 0, v___x_1536_);
v___x_1541_ = v___x_1530_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v___f_1532_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v___f_1539_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v___f_1538_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v___f_1537_);
v___x_1541_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 1, v___f_1533_);
lean_ctor_set(v___x_1523_, 0, v___x_1541_);
v___x_1543_ = v___x_1523_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___f_1533_);
v___x_1543_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; lean_object* v_toApplicative_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1577_; 
v___x_1544_ = l_ReaderT_instMonad___redArg(v___x_1543_);
v_toApplicative_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; 
v_unused_1578_ = lean_ctor_get(v___x_1544_, 1);
lean_dec(v_unused_1578_);
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1577_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_toApplicative_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1577_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_toFunctor_1549_; lean_object* v_toSeq_1550_; lean_object* v_toSeqLeft_1551_; lean_object* v_toSeqRight_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1575_; 
v_toFunctor_1549_ = lean_ctor_get(v_toApplicative_1545_, 0);
v_toSeq_1550_ = lean_ctor_get(v_toApplicative_1545_, 2);
v_toSeqLeft_1551_ = lean_ctor_get(v_toApplicative_1545_, 3);
v_toSeqRight_1552_ = lean_ctor_get(v_toApplicative_1545_, 4);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_toApplicative_1545_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_toApplicative_1545_, 1);
lean_dec(v_unused_1576_);
v___x_1554_ = v_toApplicative_1545_;
v_isShared_1555_ = v_isSharedCheck_1575_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_toSeqRight_1552_);
lean_inc(v_toSeqLeft_1551_);
lean_inc(v_toSeq_1550_);
lean_inc(v_toFunctor_1549_);
lean_dec(v_toApplicative_1545_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1575_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___f_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___f_1561_; lean_object* v___f_1562_; lean_object* v___f_1563_; lean_object* v___x_1565_; 
v___f_1556_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__3));
v___f_1557_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__4));
lean_inc_ref(v_toFunctor_1549_);
v___f_1558_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1558_, 0, v_toFunctor_1549_);
v___f_1559_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1559_, 0, v_toFunctor_1549_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___f_1558_);
lean_ctor_set(v___x_1560_, 1, v___f_1559_);
v___f_1561_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1561_, 0, v_toSeqRight_1552_);
v___f_1562_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1562_, 0, v_toSeqLeft_1551_);
v___f_1563_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1563_, 0, v_toSeq_1550_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v___f_1561_);
lean_ctor_set(v___x_1554_, 3, v___f_1562_);
lean_ctor_set(v___x_1554_, 2, v___f_1563_);
lean_ctor_set(v___x_1554_, 1, v___f_1556_);
lean_ctor_set(v___x_1554_, 0, v___x_1560_);
v___x_1565_ = v___x_1554_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v___f_1556_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v___f_1563_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v___f_1562_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v___f_1561_);
v___x_1565_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v___f_1557_);
lean_ctor_set(v___x_1547_, 0, v___x_1565_);
v___x_1567_ = v___x_1547_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___f_1557_);
v___x_1567_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_9485__overap_1571_; lean_object* v___x_1572_; 
v___x_1568_ = 0;
v___x_1569_ = lean_box(v___x_1568_);
v___x_1570_ = l_instInhabitedOfMonad___redArg(v___x_1567_, v___x_1569_);
v___x_9485__overap_1571_ = lean_panic_fn(v___x_1570_, v_msg_1513_);
v___x_1572_ = lean_apply_5(v___x_9485__overap_1571_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, lean_box(0));
return v___x_1572_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_msg_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(v_msg_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(lean_object* v_mvarId_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v_mctx_1602_; lean_object* v_levelAssignDepth_1603_; lean_object* v_lDepth_1604_; lean_object* v___x_1605_; 
v___x_1601_ = lean_st_ref_get(v___y_1597_);
v_mctx_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc_ref(v_mctx_1602_);
lean_dec(v___x_1601_);
v_levelAssignDepth_1603_ = lean_ctor_get(v_mctx_1602_, 1);
lean_inc(v_levelAssignDepth_1603_);
v_lDepth_1604_ = lean_ctor_get(v_mctx_1602_, 3);
lean_inc_ref(v_lDepth_1604_);
lean_dec_ref(v_mctx_1602_);
v___x_1605_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(v_lDepth_1604_, v_mvarId_1595_);
if (lean_obj_tag(v___x_1605_) == 1)
{
lean_object* v_val_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v_mvarId_1595_);
v_val_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1615_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_val_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1615_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
uint8_t v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1610_ = lean_nat_dec_le(v_levelAssignDepth_1603_, v_val_1606_);
lean_dec(v_val_1606_);
lean_dec(v_levelAssignDepth_1603_);
v___x_1611_ = lean_box(v___x_1610_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set_tag(v___x_1608_, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1611_);
v___x_1613_ = v___x_1608_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v___x_1605_);
lean_dec(v_levelAssignDepth_1603_);
v___x_1616_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__0));
v___x_1617_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__1));
v___x_1618_ = lean_unsigned_to_nat(451u);
v___x_1619_ = lean_unsigned_to_nat(14u);
v___x_1620_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__2));
v___x_1621_ = 1;
v___x_1622_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1595_, v___x_1621_);
v___x_1623_ = lean_string_append(v___x_1620_, v___x_1622_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = l_mkPanicMessageWithDecl(v___x_1616_, v___x_1617_, v___x_1618_, v___x_1619_, v___x_1623_);
lean_dec_ref(v___x_1623_);
v___x_1625_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(v___x_1624_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___boxed(lean_object* v_mvarId_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(v_mvarId_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(lean_object* v_x_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___y_1640_; lean_object* v___y_1641_; uint8_t v_a_1642_; lean_object* v_lvl_u2081_1648_; lean_object* v_lvl_u2082_1649_; 
switch(lean_obj_tag(v_x_1633_))
{
case 1:
{
lean_object* v_a_1656_; uint8_t v___x_1657_; 
v_a_1656_ = lean_ctor_get(v_x_1633_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v_x_1633_);
v___x_1657_ = l_Lean_Level_hasMVar(v_a_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v_a_1656_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
v___x_1658_ = lean_box(v___x_1657_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
else
{
v_x_1633_ = v_a_1656_;
goto _start;
}
}
case 2:
{
lean_object* v_a_1661_; lean_object* v_a_1662_; 
v_a_1661_ = lean_ctor_get(v_x_1633_, 0);
lean_inc(v_a_1661_);
v_a_1662_ = lean_ctor_get(v_x_1633_, 1);
lean_inc(v_a_1662_);
lean_dec_ref(v_x_1633_);
v_lvl_u2081_1648_ = v_a_1661_;
v_lvl_u2082_1649_ = v_a_1662_;
goto v___jp_1647_;
}
case 3:
{
lean_object* v_a_1663_; lean_object* v_a_1664_; 
v_a_1663_ = lean_ctor_get(v_x_1633_, 0);
lean_inc(v_a_1663_);
v_a_1664_ = lean_ctor_get(v_x_1633_, 1);
lean_inc(v_a_1664_);
lean_dec_ref(v_x_1633_);
v_lvl_u2081_1648_ = v_a_1663_;
v_lvl_u2082_1649_ = v_a_1664_;
goto v___jp_1647_;
}
case 5:
{
lean_object* v_a_1665_; lean_object* v___x_1666_; 
v_a_1665_ = lean_ctor_get(v_x_1633_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v_x_1633_);
v___x_1666_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(v_a_1665_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1666_;
}
default: 
{
uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_x_1633_);
v___x_1667_ = 0;
v___x_1668_ = lean_box(v___x_1667_);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
v___jp_1639_:
{
if (v_a_1642_ == 0)
{
uint8_t v___x_1643_; 
lean_dec_ref(v___y_1641_);
v___x_1643_ = l_Lean_Level_hasMVar(v___y_1640_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v___y_1640_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
v___x_1644_ = lean_box(v___x_1643_);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
return v___x_1645_;
}
else
{
v_x_1633_ = v___y_1640_;
goto _start;
}
}
else
{
lean_dec(v___y_1640_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v___y_1641_;
}
}
v___jp_1647_:
{
uint8_t v___x_1650_; 
v___x_1650_ = l_Lean_Level_hasMVar(v_lvl_u2081_1648_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec(v_lvl_u2081_1648_);
v___x_1651_ = lean_box(v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
v___y_1640_ = v_lvl_u2082_1649_;
v___y_1641_ = v___x_1652_;
v_a_1642_ = v___x_1650_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1653_; 
lean_inc(v___y_1637_);
lean_inc_ref(v___y_1636_);
lean_inc(v___y_1635_);
lean_inc_ref(v___y_1634_);
v___x_1653_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(v_lvl_u2081_1648_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; uint8_t v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
v___x_1655_ = lean_unbox(v_a_1654_);
lean_dec(v_a_1654_);
v___y_1640_ = v_lvl_u2082_1649_;
v___y_1641_ = v___x_1653_;
v_a_1642_ = v___x_1655_;
goto v___jp_1639_;
}
else
{
lean_dec(v_lvl_u2082_1649_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v___x_1653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4___boxed(lean_object* v_x_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(v_x_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
v___x_1683_ = 0;
v___x_1684_ = lean_box(v___x_1683_);
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
return v___x_1685_;
}
else
{
lean_object* v_head_1686_; lean_object* v_tail_1687_; lean_object* v___x_1688_; 
v_head_1686_ = lean_ctor_get(v_x_1677_, 0);
lean_inc(v_head_1686_);
v_tail_1687_ = lean_ctor_get(v_x_1677_, 1);
lean_inc(v_tail_1687_);
lean_dec_ref(v_x_1677_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
v___x_1688_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(v_head_1686_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
v___x_1690_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
if (v___x_1690_ == 0)
{
lean_dec_ref(v___x_1688_);
v_x_1677_ = v_tail_1687_;
goto _start;
}
else
{
lean_dec(v_tail_1687_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v___x_1688_;
}
}
else
{
lean_dec(v_tail_1687_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v___x_1688_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5___boxed(lean_object* v_x_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(v_x_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(lean_object* v_mvarId_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v_mctx_1703_; lean_object* v_decl_1704_; lean_object* v_depth_1705_; lean_object* v_depth_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1702_ = lean_st_ref_get(v___y_1700_);
v_mctx_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc_ref(v_mctx_1703_);
lean_dec(v___x_1702_);
lean_inc_ref(v_mctx_1703_);
v_decl_1704_ = l_Lean_MetavarContext_getDecl(v_mctx_1703_, v_mvarId_1699_);
v_depth_1705_ = lean_ctor_get(v_decl_1704_, 3);
lean_inc(v_depth_1705_);
lean_dec_ref(v_decl_1704_);
v_depth_1706_ = lean_ctor_get(v_mctx_1703_, 0);
lean_inc(v_depth_1706_);
lean_dec_ref(v_mctx_1703_);
v___x_1707_ = lean_nat_dec_eq(v_depth_1705_, v_depth_1706_);
lean_dec(v_depth_1706_);
lean_dec(v_depth_1705_);
v___x_1708_ = lean_box(v___x_1707_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg___boxed(lean_object* v_mvarId_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(v_mvarId_1710_, v___y_1711_);
lean_dec(v___y_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_x_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___y_1721_; lean_object* v___y_1722_; uint8_t v_a_1723_; lean_object* v_d_1729_; lean_object* v_b_1730_; 
switch(lean_obj_tag(v_x_1714_))
{
case 2:
{
lean_object* v_mvarId_1737_; lean_object* v___x_1738_; 
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec_ref(v___y_1715_);
v_mvarId_1737_ = lean_ctor_get(v_x_1714_, 0);
lean_inc(v_mvarId_1737_);
lean_dec_ref(v_x_1714_);
v___x_1738_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(v_mvarId_1737_, v___y_1716_);
lean_dec(v___y_1716_);
return v___x_1738_;
}
case 3:
{
lean_object* v_u_1739_; lean_object* v___x_1740_; 
v_u_1739_ = lean_ctor_get(v_x_1714_, 0);
lean_inc(v_u_1739_);
lean_dec_ref(v_x_1714_);
v___x_1740_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(v_u_1739_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1740_;
}
case 4:
{
lean_object* v_us_1741_; lean_object* v___x_1742_; 
v_us_1741_ = lean_ctor_get(v_x_1714_, 1);
lean_inc(v_us_1741_);
lean_dec_ref(v_x_1714_);
v___x_1742_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(v_us_1741_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1742_;
}
case 5:
{
lean_object* v_fn_1743_; lean_object* v_arg_1744_; lean_object* v___y_1746_; uint8_t v_a_1747_; uint8_t v___x_1752_; 
v_fn_1743_ = lean_ctor_get(v_x_1714_, 0);
lean_inc_ref(v_fn_1743_);
v_arg_1744_ = lean_ctor_get(v_x_1714_, 1);
lean_inc_ref(v_arg_1744_);
lean_dec_ref(v_x_1714_);
v___x_1752_ = l_Lean_Expr_hasMVar(v_fn_1743_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec_ref(v_fn_1743_);
v___x_1753_ = lean_box(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
v___y_1746_ = v___x_1754_;
v_a_1747_ = v___x_1752_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1755_; 
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
v___x_1755_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_fn_1743_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; uint8_t v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
v___x_1757_ = lean_unbox(v_a_1756_);
lean_dec(v_a_1756_);
v___y_1746_ = v___x_1755_;
v_a_1747_ = v___x_1757_;
goto v___jp_1745_;
}
else
{
lean_dec_ref(v_arg_1744_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v___x_1755_;
}
}
v___jp_1745_:
{
if (v_a_1747_ == 0)
{
uint8_t v___x_1748_; 
lean_dec_ref(v___y_1746_);
v___x_1748_ = l_Lean_Expr_hasMVar(v_arg_1744_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec_ref(v_arg_1744_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
v___x_1749_ = lean_box(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
else
{
v_x_1714_ = v_arg_1744_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1744_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v___y_1746_;
}
}
}
case 6:
{
lean_object* v_binderType_1758_; lean_object* v_body_1759_; 
v_binderType_1758_ = lean_ctor_get(v_x_1714_, 1);
lean_inc_ref(v_binderType_1758_);
v_body_1759_ = lean_ctor_get(v_x_1714_, 2);
lean_inc_ref(v_body_1759_);
lean_dec_ref(v_x_1714_);
v_d_1729_ = v_binderType_1758_;
v_b_1730_ = v_body_1759_;
goto v___jp_1728_;
}
case 7:
{
lean_object* v_binderType_1760_; lean_object* v_body_1761_; 
v_binderType_1760_ = lean_ctor_get(v_x_1714_, 1);
lean_inc_ref(v_binderType_1760_);
v_body_1761_ = lean_ctor_get(v_x_1714_, 2);
lean_inc_ref(v_body_1761_);
lean_dec_ref(v_x_1714_);
v_d_1729_ = v_binderType_1760_;
v_b_1730_ = v_body_1761_;
goto v___jp_1728_;
}
case 8:
{
lean_object* v_type_1762_; lean_object* v_value_1763_; lean_object* v_body_1764_; lean_object* v___y_1766_; uint8_t v_a_1767_; lean_object* v___y_1773_; uint8_t v_a_1774_; uint8_t v___x_1781_; 
v_type_1762_ = lean_ctor_get(v_x_1714_, 1);
lean_inc_ref(v_type_1762_);
v_value_1763_ = lean_ctor_get(v_x_1714_, 2);
lean_inc_ref(v_value_1763_);
v_body_1764_ = lean_ctor_get(v_x_1714_, 3);
lean_inc_ref(v_body_1764_);
lean_dec_ref(v_x_1714_);
v___x_1781_ = l_Lean_Expr_hasMVar(v_type_1762_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec_ref(v_type_1762_);
v___x_1782_ = lean_box(v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
v___y_1773_ = v___x_1783_;
v_a_1774_ = v___x_1781_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1784_; 
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
v___x_1784_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_type_1762_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; uint8_t v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
v___x_1786_ = lean_unbox(v_a_1785_);
lean_dec(v_a_1785_);
v___y_1773_ = v___x_1784_;
v_a_1774_ = v___x_1786_;
goto v___jp_1772_;
}
else
{
lean_dec_ref(v_body_1764_);
lean_dec_ref(v_value_1763_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v___x_1784_;
}
}
v___jp_1765_:
{
if (v_a_1767_ == 0)
{
uint8_t v___x_1768_; 
lean_dec_ref(v___y_1766_);
v___x_1768_ = l_Lean_Expr_hasMVar(v_body_1764_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v_body_1764_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
v___x_1769_ = lean_box(v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
else
{
v_x_1714_ = v_body_1764_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1764_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v___y_1766_;
}
}
v___jp_1772_:
{
if (v_a_1774_ == 0)
{
uint8_t v___x_1775_; 
lean_dec_ref(v___y_1773_);
v___x_1775_ = l_Lean_Expr_hasMVar(v_value_1763_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec_ref(v_value_1763_);
v___x_1776_ = lean_box(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
v___y_1766_ = v___x_1777_;
v_a_1767_ = v___x_1775_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1778_; 
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
v___x_1778_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_value_1763_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; uint8_t v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
v___x_1780_ = lean_unbox(v_a_1779_);
lean_dec(v_a_1779_);
v___y_1766_ = v___x_1778_;
v_a_1767_ = v___x_1780_;
goto v___jp_1765_;
}
else
{
lean_dec_ref(v_body_1764_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v___x_1778_;
}
}
}
else
{
lean_dec_ref(v_body_1764_);
lean_dec_ref(v_value_1763_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v___y_1773_;
}
}
}
case 10:
{
lean_object* v_expr_1787_; uint8_t v___x_1788_; 
v_expr_1787_ = lean_ctor_get(v_x_1714_, 1);
lean_inc_ref(v_expr_1787_);
lean_dec_ref(v_x_1714_);
v___x_1788_ = l_Lean_Expr_hasMVar(v_expr_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v_expr_1787_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
v___x_1789_ = lean_box(v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
else
{
v_x_1714_ = v_expr_1787_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_1792_; uint8_t v___x_1793_; 
v_struct_1792_ = lean_ctor_get(v_x_1714_, 2);
lean_inc_ref(v_struct_1792_);
lean_dec_ref(v_x_1714_);
v___x_1793_ = l_Lean_Expr_hasMVar(v_struct_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v_struct_1792_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
v___x_1794_ = lean_box(v___x_1793_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
else
{
v_x_1714_ = v_struct_1792_;
goto _start;
}
}
default: 
{
uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec_ref(v_x_1714_);
v___x_1797_ = 0;
v___x_1798_ = lean_box(v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
}
v___jp_1720_:
{
if (v_a_1723_ == 0)
{
uint8_t v___x_1724_; 
lean_dec_ref(v___y_1722_);
v___x_1724_ = l_Lean_Expr_hasMVar(v___y_1721_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
v___x_1725_ = lean_box(v___x_1724_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
else
{
v_x_1714_ = v___y_1721_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v___y_1722_;
}
}
v___jp_1728_:
{
uint8_t v___x_1731_; 
v___x_1731_ = l_Lean_Expr_hasMVar(v_d_1729_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec_ref(v_d_1729_);
v___x_1732_ = lean_box(v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
v___y_1721_ = v_b_1730_;
v___y_1722_ = v___x_1733_;
v_a_1723_ = v___x_1731_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_1734_; 
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
v___x_1734_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_d_1729_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; uint8_t v___x_1736_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
v___x_1736_ = lean_unbox(v_a_1735_);
lean_dec(v_a_1735_);
v___y_1721_ = v_b_1730_;
v___y_1722_ = v___x_1734_;
v_a_1723_ = v___x_1736_;
goto v___jp_1720_;
}
else
{
lean_dec_ref(v_b_1730_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v___x_1734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_x_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1809_, size_t v_sz_1810_, size_t v_i_1811_, lean_object* v_b_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_a_1819_; uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_lt(v_i_1811_, v_sz_1810_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_b_1812_);
return v___x_1824_;
}
else
{
lean_object* v_snd_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1987_; 
v_snd_1825_ = lean_ctor_get(v_b_1812_, 1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_b_1812_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v_b_1812_, 0);
lean_dec(v_unused_1988_);
v___x_1827_ = v_b_1812_;
v_isShared_1828_ = v_isSharedCheck_1987_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_snd_1825_);
lean_dec(v_b_1812_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1987_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_array_1829_; lean_object* v_start_1830_; lean_object* v_stop_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_array_1829_ = lean_ctor_get(v_snd_1825_, 0);
v_start_1830_ = lean_ctor_get(v_snd_1825_, 1);
v_stop_1831_ = lean_ctor_get(v_snd_1825_, 2);
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_nat_dec_lt(v_start_1830_, v_stop_1831_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1835_; 
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1832_);
v___x_1835_ = v___x_1827_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_snd_1825_);
v___x_1835_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
else
{
lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1983_; 
lean_inc(v_stop_1831_);
lean_inc(v_start_1830_);
lean_inc_ref(v_array_1829_);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_snd_1825_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; lean_object* v_unused_1985_; lean_object* v_unused_1986_; 
v_unused_1984_ = lean_ctor_get(v_snd_1825_, 2);
lean_dec(v_unused_1984_);
v_unused_1985_ = lean_ctor_get(v_snd_1825_, 1);
lean_dec(v_unused_1985_);
v_unused_1986_ = lean_ctor_get(v_snd_1825_, 0);
lean_dec(v_unused_1986_);
v___x_1839_ = v_snd_1825_;
v_isShared_1840_ = v_isSharedCheck_1983_;
goto v_resetjp_1838_;
}
else
{
lean_dec(v_snd_1825_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1983_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1841_ = lean_array_fget(v_array_1829_, v_start_1830_);
v___x_1842_ = lean_unsigned_to_nat(1u);
v___x_1843_ = lean_nat_add(v_start_1830_, v___x_1842_);
lean_dec(v_start_1830_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___x_1843_);
v___x_1845_ = v___x_1839_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_array_1829_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_stop_1831_);
v___x_1845_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_unbox(v___x_1841_);
lean_dec(v___x_1841_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1848_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1845_);
lean_ctor_set(v___x_1827_, 0, v___x_1832_);
v___x_1848_ = v___x_1827_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1845_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
v_a_1819_ = v___x_1848_;
goto v___jp_1818_;
}
}
else
{
lean_object* v_a_1850_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___x_1922_; 
v_a_1850_ = lean_array_uget_borrowed(v_as_1809_, v_i_1811_);
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
lean_inc(v_a_1850_);
v___x_1922_ = lean_infer_type(v_a_1850_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1924_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref(v___x_1922_);
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
v___x_1924_ = l_Lean_Meta_matchEq_x3f(v_a_1923_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1924_);
if (lean_obj_tag(v_a_1925_) == 1)
{
lean_object* v_val_1926_; lean_object* v_snd_1927_; lean_object* v_fst_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1964_; 
v_val_1926_ = lean_ctor_get(v_a_1925_, 0);
lean_inc(v_val_1926_);
lean_dec_ref(v_a_1925_);
v_snd_1927_ = lean_ctor_get(v_val_1926_, 1);
lean_inc(v_snd_1927_);
lean_dec(v_val_1926_);
v_fst_1928_ = lean_ctor_get(v_snd_1927_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_snd_1927_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v_snd_1927_, 1);
lean_dec(v_unused_1965_);
v___x_1930_ = v_snd_1927_;
v_isShared_1931_ = v_isSharedCheck_1964_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_fst_1928_);
lean_dec(v_snd_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1964_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; 
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
v___x_1932_ = l_Lean_Meta_mkEqRefl(v_fst_1928_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
lean_inc(v_a_1850_);
v___x_1934_ = l_Lean_Meta_isExprDefEq(v_a_1850_, v_a_1933_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1947_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1947_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1947_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_unbox(v_a_1935_);
lean_dec(v_a_1935_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
lean_del_object(v___x_1827_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v___x_1940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v___x_1845_);
lean_ctor_set(v___x_1930_, 0, v___x_1940_);
v___x_1942_ = v___x_1930_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1845_);
v___x_1942_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1942_);
v___x_1944_ = v___x_1937_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_del_object(v___x_1937_);
lean_del_object(v___x_1930_);
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
v___y_1852_ = v___y_1813_;
v___y_1853_ = v___y_1814_;
v___y_1854_ = v___y_1815_;
v___y_1855_ = v___y_1816_;
goto v___jp_1851_;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_del_object(v___x_1930_);
lean_dec_ref(v___x_1845_);
lean_del_object(v___x_1827_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v_a_1948_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1934_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1934_);
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
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_del_object(v___x_1930_);
lean_dec_ref(v___x_1845_);
lean_del_object(v___x_1827_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v_a_1956_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1932_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1932_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
else
{
lean_dec(v_a_1925_);
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
lean_inc(v___y_1814_);
lean_inc_ref(v___y_1813_);
v___y_1852_ = v___y_1813_;
v___y_1853_ = v___y_1814_;
v___y_1854_ = v___y_1815_;
v___y_1855_ = v___y_1816_;
goto v___jp_1851_;
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v___x_1845_);
lean_del_object(v___x_1827_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v_a_1966_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1924_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1924_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v___x_1845_);
lean_del_object(v___x_1827_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v_a_1974_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1922_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1922_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
v___jp_1851_:
{
lean_object* v___x_1856_; 
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v___y_1853_);
lean_inc_ref(v___y_1852_);
lean_inc(v_a_1850_);
v___x_1856_ = lean_infer_type(v_a_1850_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v___y_1853_);
lean_inc_ref(v___y_1852_);
v___x_1858_ = l_Lean_Meta_matchHEq_x3f(v_a_1857_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
if (lean_obj_tag(v_a_1859_) == 1)
{
lean_object* v_val_1860_; lean_object* v_snd_1861_; lean_object* v_fst_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1901_; 
lean_del_object(v___x_1827_);
v_val_1860_ = lean_ctor_get(v_a_1859_, 0);
lean_inc(v_val_1860_);
lean_dec_ref(v_a_1859_);
v_snd_1861_ = lean_ctor_get(v_val_1860_, 1);
lean_inc(v_snd_1861_);
lean_dec(v_val_1860_);
v_fst_1862_ = lean_ctor_get(v_snd_1861_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_snd_1861_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v_snd_1861_, 1);
lean_dec(v_unused_1902_);
v___x_1864_ = v_snd_1861_;
v_isShared_1865_ = v_isSharedCheck_1901_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_fst_1862_);
lean_dec(v_snd_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1901_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; 
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v___y_1853_);
lean_inc_ref(v___y_1852_);
v___x_1866_ = l_Lean_Meta_mkHEqRefl(v_fst_1862_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref(v___x_1866_);
lean_inc(v_a_1850_);
v___x_1868_ = l_Lean_Meta_isExprDefEq(v_a_1850_, v_a_1867_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1884_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_unbox(v_a_1869_);
lean_dec(v_a_1869_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v___x_1874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 1, v___x_1845_);
lean_ctor_set(v___x_1864_, 0, v___x_1874_);
v___x_1876_ = v___x_1864_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1845_);
v___x_1876_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1878_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1876_);
v___x_1878_ = v___x_1871_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v___x_1882_; 
lean_del_object(v___x_1871_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 1, v___x_1845_);
lean_ctor_set(v___x_1864_, 0, v___x_1832_);
v___x_1882_ = v___x_1864_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1845_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
v_a_1819_ = v___x_1882_;
goto v___jp_1818_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_del_object(v___x_1864_);
lean_dec_ref(v___x_1845_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v_a_1885_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1868_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1868_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_del_object(v___x_1864_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec_ref(v___x_1845_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v_a_1893_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1866_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1866_);
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
else
{
lean_object* v___x_1904_; 
lean_dec(v_a_1859_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1845_);
lean_ctor_set(v___x_1827_, 0, v___x_1832_);
v___x_1904_ = v___x_1827_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1845_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
v_a_1819_ = v___x_1904_;
goto v___jp_1818_;
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec_ref(v___x_1845_);
lean_del_object(v___x_1827_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v_a_1906_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1858_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1858_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec_ref(v___x_1845_);
lean_del_object(v___x_1827_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
v_a_1914_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1856_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1856_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
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
v___jp_1818_:
{
size_t v___x_1820_; size_t v___x_1821_; 
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1811_, v___x_1820_);
v_i_1811_ = v___x_1821_;
v_b_1812_ = v_a_1819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1989_, lean_object* v_sz_1990_, lean_object* v_i_1991_, lean_object* v_b_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
size_t v_sz_boxed_1998_; size_t v_i_boxed_1999_; lean_object* v_res_2000_; 
v_sz_boxed_1998_ = lean_unbox_usize(v_sz_1990_);
lean_dec(v_sz_1990_);
v_i_boxed_1999_ = lean_unbox_usize(v_i_1991_);
lean_dec(v_i_1991_);
v_res_2000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1989_, v_sz_boxed_1998_, v_i_boxed_1999_, v_b_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec_ref(v_as_1989_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_2001_, uint8_t v___x_2002_, lean_object* v_localDecl_2003_, lean_object* v_mvarId_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
lean_inc(v___y_2008_);
lean_inc_ref(v___y_2007_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc_ref(v___x_2001_);
v___x_2010_ = l_Lean_Meta_forallMetaTelescope(v___x_2001_, v___x_2002_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v_fst_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2101_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_2010_);
v_fst_2012_ = lean_ctor_get(v_a_2011_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_a_2011_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v_a_2011_, 1);
lean_dec(v_unused_2102_);
v___x_2014_ = v_a_2011_;
v_isShared_2015_ = v_isSharedCheck_2101_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_fst_2012_);
lean_dec(v_a_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2101_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2016_ = l_Lean_Meta_mkGenDiseqMask(v___x_2001_);
lean_dec_ref(v___x_2001_);
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = lean_array_get_size(v___x_2016_);
v___x_2019_ = l_Array_toSubarray___redArg(v___x_2016_, v___x_2017_, v___x_2018_);
v___x_2020_ = lean_box(0);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 1, v___x_2019_);
lean_ctor_set(v___x_2014_, 0, v___x_2020_);
v___x_2022_ = v___x_2014_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2019_);
v___x_2022_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
size_t v_sz_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v_sz_2023_ = lean_array_size(v_fst_2012_);
v___x_2024_ = ((size_t)0ULL);
lean_inc(v___y_2008_);
lean_inc_ref(v___y_2007_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_2012_, v_sz_2023_, v___x_2024_, v___x_2022_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2091_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2091_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2091_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_fst_2030_; 
v_fst_2030_ = lean_ctor_get(v_a_2026_, 0);
lean_inc(v_fst_2030_);
lean_dec(v_a_2026_);
if (lean_obj_tag(v_fst_2030_) == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2086_; 
lean_del_object(v___x_2028_);
v___x_2031_ = l_Lean_LocalDecl_toExpr(v_localDecl_2003_);
v___x_2032_ = l_Lean_mkAppN(v___x_2031_, v_fst_2012_);
lean_dec(v_fst_2012_);
v___x_2033_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2032_, v___y_2006_);
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2086_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2086_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; 
lean_inc(v___y_2008_);
lean_inc_ref(v___y_2007_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v_a_2034_);
v___x_2038_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_a_2034_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2077_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2077_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2077_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
uint8_t v___x_2043_; 
v___x_2043_ = lean_unbox(v_a_2039_);
lean_dec(v_a_2039_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_del_object(v___x_2041_);
v___x_2044_ = l_Lean_MVarId_getType(v_mvarId_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v___x_2046_ = l_Lean_Meta_mkFalseElim(v_a_2045_, v_a_2034_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2057_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 1);
lean_ctor_set(v___x_2036_, 0, v_a_2047_);
v___x_2052_ = v___x_2036_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2054_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2052_);
v___x_2054_ = v___x_2049_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_del_object(v___x_2036_);
v_a_2058_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2046_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2046_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_2036_);
lean_dec(v_a_2034_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
v_a_2066_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2044_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2044_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v___x_2075_; 
lean_del_object(v___x_2036_);
lean_dec(v_a_2034_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v_mvarId_2004_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2020_);
v___x_2075_ = v___x_2041_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2020_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_del_object(v___x_2036_);
lean_dec(v_a_2034_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v_mvarId_2004_);
v_a_2078_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2038_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2038_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_object* v_val_2087_; lean_object* v___x_2089_; 
lean_dec(v_fst_2012_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v_mvarId_2004_);
lean_dec_ref(v_localDecl_2003_);
v_val_2087_ = lean_ctor_get(v_fst_2030_, 0);
lean_inc(v_val_2087_);
lean_dec_ref(v_fst_2030_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v_val_2087_);
v___x_2089_ = v___x_2028_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_val_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v_fst_2012_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v_mvarId_2004_);
lean_dec_ref(v_localDecl_2003_);
v_a_2092_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2025_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2025_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v_mvarId_2004_);
lean_dec_ref(v_localDecl_2003_);
lean_dec_ref(v___x_2001_);
v_a_2103_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2010_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2010_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_2111_, lean_object* v___x_2112_, lean_object* v_localDecl_2113_, lean_object* v_mvarId_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
uint8_t v___x_10811__boxed_2120_; lean_object* v_res_2121_; 
v___x_10811__boxed_2120_ = lean_unbox(v___x_2112_);
v_res_2121_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_2111_, v___x_10811__boxed_2120_, v_localDecl_2113_, v_mvarId_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v_res_2121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_2126_ = lean_unsigned_to_nat(2u);
v___x_2127_ = lean_unsigned_to_nat(120u);
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_2129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_2130_ = l_mkPanicMessageWithDecl(v___x_2129_, v___x_2128_, v___x_2127_, v___x_2126_, v___x_2125_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_2131_, lean_object* v_localDecl_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = l_Lean_LocalDecl_type(v_localDecl_2132_);
lean_inc_ref(v___x_2138_);
v___x_2139_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec_ref(v___x_2138_);
lean_dec_ref(v_localDecl_2132_);
lean_dec(v_mvarId_2131_);
v___x_2140_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_2141_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_2140_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
return v___x_2141_;
}
else
{
uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___f_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2142_ = 0;
v___x_2143_ = lean_box(v___x_2142_);
lean_inc(v_mvarId_2131_);
v___f_2144_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2144_, 0, v___x_2138_);
lean_closure_set(v___f_2144_, 1, v___x_2143_);
lean_closure_set(v___f_2144_, 2, v_localDecl_2132_);
lean_closure_set(v___f_2144_, 3, v_mvarId_2131_);
v___x_2145_ = 0;
lean_inc(v_a_2134_);
v___x_2146_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(v___f_2144_, v___x_2145_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2166_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2166_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2166_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
if (lean_obj_tag(v_a_2147_) == 1)
{
lean_object* v_val_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2160_; 
lean_del_object(v___x_2149_);
v_val_2151_ = lean_ctor_get(v_a_2147_, 0);
lean_inc(v_val_2151_);
lean_dec_ref(v_a_2147_);
v___x_2152_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2131_, v_val_2151_, v_a_2134_);
lean_dec(v_a_2134_);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2152_, 0);
lean_dec(v_unused_2161_);
v___x_2154_ = v___x_2152_;
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
else
{
lean_dec(v___x_2152_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = lean_box(v___x_2139_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2156_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_dec(v_a_2147_);
lean_dec(v_a_2134_);
lean_dec(v_mvarId_2131_);
v___x_2162_ = lean_box(v___x_2145_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2162_);
v___x_2164_ = v___x_2149_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
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
lean_dec(v_a_2134_);
lean_dec(v_mvarId_2131_);
v_a_2167_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2146_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2146_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_2175_, lean_object* v_localDecl_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2175_, v_localDecl_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(lean_object* v_mvarId_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(v_mvarId_2183_, v___y_2185_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___boxed(lean_object* v_mvarId_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(v_mvarId_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(v_x_2198_, v_x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b2_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7(v_00_u03b2_2201_, v_x_2202_, v_x_2203_);
lean_dec(v_x_2203_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_2205_, lean_object* v_x_2206_, size_t v_x_2207_, lean_object* v_x_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(v_x_2206_, v_x_2207_, v_x_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b2_2210_, lean_object* v_x_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_){
_start:
{
size_t v_x_11175__boxed_2214_; lean_object* v_res_2215_; 
v_x_11175__boxed_2214_ = lean_unbox_usize(v_x_2212_);
lean_dec(v_x_2212_);
v_res_2215_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9(v_00_u03b2_2210_, v_x_2211_, v_x_11175__boxed_2214_, v_x_2213_);
lean_dec(v_x_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* v_00_u03b2_2216_, lean_object* v_keys_2217_, lean_object* v_vals_2218_, lean_object* v_heq_2219_, lean_object* v_i_2220_, lean_object* v_k_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(v_keys_2217_, v_vals_2218_, v_i_2220_, v_k_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b2_2223_, lean_object* v_keys_2224_, lean_object* v_vals_2225_, lean_object* v_heq_2226_, lean_object* v_i_2227_, lean_object* v_k_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11(v_00_u03b2_2223_, v_keys_2224_, v_vals_2225_, v_heq_2226_, v_i_2227_, v_k_2228_);
lean_dec(v_k_2228_);
lean_dec_ref(v_vals_2225_);
lean_dec_ref(v_keys_2224_);
return v_res_2229_;
}
}
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1(void){
_start:
{
uint8_t v___x_2233_; uint64_t v___x_2234_; 
v___x_2233_ = 1;
v___x_2234_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_box(0);
v___x_2244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6));
v___x_2245_ = l_Lean_mkConst(v___x_2244_, v___x_2243_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2246_; lean_object* v_dummy_2247_; 
v___x_2246_ = lean_box(0);
v_dummy_2247_ = l_Lean_Expr_sort___override(v___x_2246_);
return v_dummy_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_2248_, lean_object* v_mvarId_2249_, lean_object* v_as_2250_, size_t v_sz_2251_, size_t v_i_2252_, lean_object* v_b_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_lt(v_i_2252_, v_sz_2251_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v_b_2253_);
return v___x_2260_;
}
else
{
lean_object* v_snd_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2929_; 
v_snd_2261_ = lean_ctor_get(v_b_2253_, 1);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_b_2253_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; 
v_unused_2930_ = lean_ctor_get(v_b_2253_, 0);
lean_dec(v_unused_2930_);
v___x_2263_ = v_b_2253_;
v_isShared_2264_ = v_isSharedCheck_2929_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_snd_2261_);
lean_dec(v_b_2253_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2929_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v_a_2266_; lean_object* v___x_2272_; lean_object* v_a_2274_; lean_object* v_a_2279_; 
v___x_2272_ = lean_box(0);
v_a_2279_ = lean_array_uget(v_as_2250_, v_i_2252_);
if (lean_obj_tag(v_a_2279_) == 0)
{
lean_del_object(v___x_2263_);
v_a_2274_ = v_snd_2261_;
goto v___jp_2273_;
}
else
{
lean_object* v_val_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2928_; 
v_val_2280_ = lean_ctor_get(v_a_2279_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_a_2279_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2282_ = v_a_2279_;
v_isShared_2283_ = v_isSharedCheck_2928_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_val_2280_);
lean_dec(v_a_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2928_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___x_2325_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; uint8_t v___y_2352_; uint8_t v___x_2353_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; uint8_t v___y_2359_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; uint8_t v___y_2365_; uint8_t v___y_2366_; uint8_t v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; uint8_t v___y_2380_; uint8_t v___y_2381_; uint8_t v___y_2382_; 
v___x_2284_ = lean_box(0);
v___x_2325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2353_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2280_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2397_; uint8_t v___y_2399_; uint8_t v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; uint8_t v___y_2413_; uint8_t v___y_2414_; uint8_t v___y_2415_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; uint8_t v___y_2422_; uint8_t v___y_2423_; lean_object* v_a_2424_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; uint8_t v___y_2432_; uint8_t v___y_2433_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2523_; uint8_t v___y_2524_; uint8_t v___y_2525_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; uint8_t v___y_2532_; uint8_t v___y_2533_; uint8_t v___y_2534_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; uint8_t v___y_2541_; uint8_t v___y_2542_; uint8_t v___y_2543_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; uint8_t v___y_2560_; uint8_t v___y_2561_; uint8_t v___y_2562_; uint8_t v___y_2564_; uint8_t v_isHEq_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; uint8_t v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; uint8_t v_isEq_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___x_2865_; 
v___x_2397_ = l_Lean_LocalDecl_type(v_val_2280_);
lean_inc(v___y_2257_);
lean_inc_ref(v___y_2256_);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
lean_inc_ref(v___x_2397_);
v___x_2865_ = l_Lean_Meta_matchNot_x3f(v___x_2397_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref(v___x_2865_);
if (lean_obj_tag(v_a_2866_) == 1)
{
lean_object* v_val_2867_; lean_object* v___x_2868_; 
v_val_2867_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_val_2867_);
lean_dec_ref(v_a_2866_);
lean_inc(v___y_2257_);
lean_inc_ref(v___y_2256_);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
v___x_2868_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2867_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref(v___x_2868_);
if (lean_obj_tag(v_a_2869_) == 1)
{
lean_object* v_val_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2911_; 
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec_ref(v_config_2248_);
v_val_2870_ = lean_ctor_get(v_a_2869_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_a_2869_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2872_ = v_a_2869_;
v_isShared_2873_ = v_isSharedCheck_2911_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_val_2870_);
lean_dec(v_a_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2911_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; 
lean_inc(v_mvarId_2249_);
v___x_2874_ = l_Lean_MVarId_getType(v_mvarId_2249_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = l_Lean_LocalDecl_toExpr(v_val_2280_);
v___x_2877_ = l_Lean_mkFVar(v_val_2870_);
v___x_2878_ = l_Lean_Expr_app___override(v___x_2876_, v___x_2877_);
lean_inc(v___y_2255_);
v___x_2879_ = l_Lean_Meta_mkFalseElim(v_a_2875_, v___x_2878_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2249_, v_a_2880_, v___y_2255_);
lean_dec(v___y_2255_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v___x_2882_; lean_object* v___x_2884_; 
lean_dec_ref(v___x_2881_);
v___x_2882_ = lean_box(v___x_2259_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2882_);
v___x_2884_ = v___x_2872_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; 
v___x_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
lean_ctor_set(v___x_2885_, 1, v___x_2284_);
v_a_2266_ = v___x_2885_;
goto v___jp_2265_;
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_del_object(v___x_2872_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v_a_2887_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2881_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2881_);
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
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_del_object(v___x_2872_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2255_);
lean_dec(v_mvarId_2249_);
v_a_2895_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2879_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2879_);
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
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_del_object(v___x_2872_);
lean_dec(v_val_2870_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
v_a_2903_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2874_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2874_);
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
}
else
{
lean_dec(v_a_2869_);
lean_inc(v___y_2257_);
lean_inc_ref(v___y_2256_);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
v___y_2731_ = v___y_2254_;
v___y_2732_ = v___y_2255_;
v___y_2733_ = v___y_2256_;
v___y_2734_ = v___y_2257_;
goto v___jp_2730_;
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2912_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2868_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2868_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_dec(v_a_2866_);
lean_inc(v___y_2257_);
lean_inc_ref(v___y_2256_);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
v___y_2731_ = v___y_2254_;
v___y_2732_ = v___y_2255_;
v___y_2733_ = v___y_2256_;
v___y_2734_ = v___y_2257_;
goto v___jp_2730_;
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2920_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2865_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2865_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
v___jp_2398_:
{
uint8_t v_genDiseq_2405_; 
v_genDiseq_2405_ = lean_ctor_get_uint8(v_config_2248_, sizeof(void*)*1 + 2);
if (v_genDiseq_2405_ == 0)
{
lean_dec_ref(v___x_2397_);
v___y_2376_ = v___y_2404_;
v___y_2377_ = v___y_2401_;
v___y_2378_ = v___y_2403_;
v___y_2379_ = v___y_2402_;
v___y_2380_ = v___y_2400_;
v___y_2381_ = v___y_2399_;
v___y_2382_ = v___x_2353_;
goto v___jp_2375_;
}
else
{
uint8_t v___x_2406_; 
v___x_2406_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2397_);
v___y_2376_ = v___y_2404_;
v___y_2377_ = v___y_2401_;
v___y_2378_ = v___y_2403_;
v___y_2379_ = v___y_2402_;
v___y_2380_ = v___y_2400_;
v___y_2381_ = v___y_2399_;
v___y_2382_ = v___x_2406_;
goto v___jp_2375_;
}
}
v___jp_2407_:
{
if (v___y_2415_ == 0)
{
lean_dec_ref(v___y_2411_);
v___y_2399_ = v___y_2414_;
v___y_2400_ = v___y_2413_;
v___y_2401_ = v___y_2410_;
v___y_2402_ = v___y_2409_;
v___y_2403_ = v___y_2408_;
v___y_2404_ = v___y_2412_;
goto v___jp_2398_;
}
else
{
lean_object* v___x_2416_; 
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec_ref(v___x_2397_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___y_2411_);
return v___x_2416_;
}
}
v___jp_2417_:
{
uint8_t v___x_2425_; 
v___x_2425_ = l_Lean_Exception_isInterrupt(v_a_2424_);
if (v___x_2425_ == 0)
{
uint8_t v___x_2426_; 
lean_inc_ref(v_a_2424_);
v___x_2426_ = l_Lean_Exception_isRuntime(v_a_2424_);
v___y_2408_ = v___y_2418_;
v___y_2409_ = v___y_2419_;
v___y_2410_ = v___y_2420_;
v___y_2411_ = v_a_2424_;
v___y_2412_ = v___y_2421_;
v___y_2413_ = v___y_2423_;
v___y_2414_ = v___y_2422_;
v___y_2415_ = v___x_2426_;
goto v___jp_2407_;
}
else
{
v___y_2408_ = v___y_2418_;
v___y_2409_ = v___y_2419_;
v___y_2410_ = v___y_2420_;
v___y_2411_ = v_a_2424_;
v___y_2412_ = v___y_2421_;
v___y_2413_ = v___y_2423_;
v___y_2414_ = v___y_2422_;
v___y_2415_ = v___x_2425_;
goto v___jp_2407_;
}
}
v___jp_2427_:
{
lean_object* v___x_2434_; 
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2428_);
lean_inc(v___y_2429_);
lean_inc_ref(v___y_2430_);
lean_inc_ref(v___x_2397_);
v___x_2434_ = l_Lean_Meta_mkDecide(v___x_2397_, v___y_2430_, v___y_2429_, v___y_2428_, v___y_2431_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; uint8_t v_foApprox_2437_; uint8_t v_ctxApprox_2438_; uint8_t v_quasiPatternApprox_2439_; uint8_t v_constApprox_2440_; uint8_t v_isDefEqStuckEx_2441_; uint8_t v_unificationHints_2442_; uint8_t v_proofIrrelevance_2443_; uint8_t v_assignSyntheticOpaque_2444_; uint8_t v_offsetCnstrs_2445_; uint8_t v_etaStruct_2446_; uint8_t v_univApprox_2447_; uint8_t v_iota_2448_; uint8_t v_beta_2449_; uint8_t v_proj_2450_; uint8_t v_zeta_2451_; uint8_t v_zetaDelta_2452_; uint8_t v_zetaUnused_2453_; uint8_t v_zetaHave_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2516_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = l_Lean_Meta_Context_config(v___y_2430_);
v_foApprox_2437_ = lean_ctor_get_uint8(v___x_2436_, 0);
v_ctxApprox_2438_ = lean_ctor_get_uint8(v___x_2436_, 1);
v_quasiPatternApprox_2439_ = lean_ctor_get_uint8(v___x_2436_, 2);
v_constApprox_2440_ = lean_ctor_get_uint8(v___x_2436_, 3);
v_isDefEqStuckEx_2441_ = lean_ctor_get_uint8(v___x_2436_, 4);
v_unificationHints_2442_ = lean_ctor_get_uint8(v___x_2436_, 5);
v_proofIrrelevance_2443_ = lean_ctor_get_uint8(v___x_2436_, 6);
v_assignSyntheticOpaque_2444_ = lean_ctor_get_uint8(v___x_2436_, 7);
v_offsetCnstrs_2445_ = lean_ctor_get_uint8(v___x_2436_, 8);
v_etaStruct_2446_ = lean_ctor_get_uint8(v___x_2436_, 10);
v_univApprox_2447_ = lean_ctor_get_uint8(v___x_2436_, 11);
v_iota_2448_ = lean_ctor_get_uint8(v___x_2436_, 12);
v_beta_2449_ = lean_ctor_get_uint8(v___x_2436_, 13);
v_proj_2450_ = lean_ctor_get_uint8(v___x_2436_, 14);
v_zeta_2451_ = lean_ctor_get_uint8(v___x_2436_, 15);
v_zetaDelta_2452_ = lean_ctor_get_uint8(v___x_2436_, 16);
v_zetaUnused_2453_ = lean_ctor_get_uint8(v___x_2436_, 17);
v_zetaHave_2454_ = lean_ctor_get_uint8(v___x_2436_, 18);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2456_ = v___x_2436_;
v_isShared_2457_ = v_isSharedCheck_2516_;
goto v_resetjp_2455_;
}
else
{
lean_dec(v___x_2436_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2516_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
uint8_t v_trackZetaDelta_2458_; lean_object* v_zetaDeltaSet_2459_; lean_object* v_lctx_2460_; lean_object* v_localInstances_2461_; lean_object* v_defEqCtx_x3f_2462_; lean_object* v_synthPendingDepth_2463_; lean_object* v_canUnfold_x3f_2464_; uint8_t v_univApprox_2465_; uint8_t v_inTypeClassResolution_2466_; uint8_t v_cacheInferType_2467_; uint8_t v___x_2468_; lean_object* v_config_2470_; 
v_trackZetaDelta_2458_ = lean_ctor_get_uint8(v___y_2430_, sizeof(void*)*7);
v_zetaDeltaSet_2459_ = lean_ctor_get(v___y_2430_, 1);
v_lctx_2460_ = lean_ctor_get(v___y_2430_, 2);
v_localInstances_2461_ = lean_ctor_get(v___y_2430_, 3);
v_defEqCtx_x3f_2462_ = lean_ctor_get(v___y_2430_, 4);
v_synthPendingDepth_2463_ = lean_ctor_get(v___y_2430_, 5);
v_canUnfold_x3f_2464_ = lean_ctor_get(v___y_2430_, 6);
v_univApprox_2465_ = lean_ctor_get_uint8(v___y_2430_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2466_ = lean_ctor_get_uint8(v___y_2430_, sizeof(void*)*7 + 2);
v_cacheInferType_2467_ = lean_ctor_get_uint8(v___y_2430_, sizeof(void*)*7 + 3);
v___x_2468_ = 1;
if (v_isShared_2457_ == 0)
{
v_config_2470_ = v___x_2456_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 0, v_foApprox_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 1, v_ctxApprox_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 2, v_quasiPatternApprox_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 3, v_constApprox_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 4, v_isDefEqStuckEx_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 5, v_unificationHints_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 6, v_proofIrrelevance_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 7, v_assignSyntheticOpaque_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 8, v_offsetCnstrs_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 10, v_etaStruct_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 11, v_univApprox_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 12, v_iota_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 13, v_beta_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 14, v_proj_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 15, v_zeta_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 16, v_zetaDelta_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 17, v_zetaUnused_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, 18, v_zetaHave_2454_);
v_config_2470_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
uint64_t v___x_2471_; uint64_t v___x_2472_; uint64_t v___x_2473_; uint64_t v___x_2474_; uint64_t v___x_2475_; uint64_t v_key_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_ctor_set_uint8(v_config_2470_, 9, v___x_2468_);
v___x_2471_ = l_Lean_Meta_Context_configKey(v___y_2430_);
v___x_2472_ = 2ULL;
v___x_2473_ = lean_uint64_shift_right(v___x_2471_, v___x_2472_);
v___x_2474_ = lean_uint64_shift_left(v___x_2473_, v___x_2472_);
v___x_2475_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_2476_ = lean_uint64_lor(v___x_2474_, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2477_, 0, v_config_2470_);
lean_ctor_set_uint64(v___x_2477_, sizeof(void*)*1, v_key_2476_);
lean_inc(v_canUnfold_x3f_2464_);
lean_inc(v_synthPendingDepth_2463_);
lean_inc(v_defEqCtx_x3f_2462_);
lean_inc_ref(v_localInstances_2461_);
lean_inc_ref(v_lctx_2460_);
lean_inc(v_zetaDeltaSet_2459_);
v___x_2478_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v_zetaDeltaSet_2459_);
lean_ctor_set(v___x_2478_, 2, v_lctx_2460_);
lean_ctor_set(v___x_2478_, 3, v_localInstances_2461_);
lean_ctor_set(v___x_2478_, 4, v_defEqCtx_x3f_2462_);
lean_ctor_set(v___x_2478_, 5, v_synthPendingDepth_2463_);
lean_ctor_set(v___x_2478_, 6, v_canUnfold_x3f_2464_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*7, v_trackZetaDelta_2458_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*7 + 1, v_univApprox_2465_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2466_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*7 + 3, v_cacheInferType_2467_);
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2428_);
lean_inc(v___y_2429_);
lean_inc(v_a_2435_);
v___x_2479_ = lean_whnf(v_a_2435_, v___x_2478_, v___y_2429_, v___y_2428_, v___y_2431_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref(v___x_2479_);
v___x_2481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_2482_ = l_Lean_Expr_isConstOf(v_a_2480_, v___x_2481_);
lean_dec(v_a_2480_);
if (v___x_2482_ == 0)
{
lean_dec(v_a_2435_);
v___y_2399_ = v___y_2433_;
v___y_2400_ = v___y_2432_;
v___y_2401_ = v___y_2430_;
v___y_2402_ = v___y_2429_;
v___y_2403_ = v___y_2428_;
v___y_2404_ = v___y_2431_;
goto v___jp_2398_;
}
else
{
lean_object* v___x_2483_; 
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2428_);
lean_inc(v___y_2429_);
lean_inc_ref(v___y_2430_);
lean_inc(v_a_2435_);
v___x_2483_ = l_Lean_Meta_mkEqRefl(v_a_2435_, v___y_2430_, v___y_2429_, v___y_2428_, v___y_2431_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2485_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref(v___x_2483_);
lean_inc(v_mvarId_2249_);
v___x_2485_ = l_Lean_MVarId_getType(v_mvarId_2249_, v___y_2430_, v___y_2429_, v___y_2428_, v___y_2431_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v_nargs_2487_; lean_object* v___x_2488_; lean_object* v_dummy_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref(v___x_2485_);
v_nargs_2487_ = l_Lean_Expr_getAppNumArgs(v_a_2435_);
v___x_2488_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2489_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2487_);
v___x_2490_ = lean_mk_array(v_nargs_2487_, v_dummy_2489_);
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_sub(v_nargs_2487_, v___x_2491_);
lean_dec(v_nargs_2487_);
v___x_2493_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2435_, v___x_2490_, v___x_2492_);
v___x_2494_ = lean_array_push(v___x_2493_, v_a_2484_);
v___x_2495_ = l_Lean_mkAppN(v___x_2488_, v___x_2494_);
lean_dec_ref(v___x_2494_);
lean_inc(v_val_2280_);
v___x_2496_ = l_Lean_LocalDecl_toExpr(v_val_2280_);
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2428_);
lean_inc(v___y_2429_);
lean_inc_ref(v___y_2430_);
v___x_2497_ = l_Lean_Meta_mkAbsurd(v_a_2486_, v___x_2496_, v___x_2495_, v___y_2430_, v___y_2429_, v___y_2428_, v___y_2431_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref(v___x_2497_);
lean_inc(v_mvarId_2249_);
v___x_2499_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2249_, v_a_2498_, v___y_2429_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec_ref(v___x_2397_);
lean_dec(v_val_2280_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2508_ == 0)
{
lean_object* v_unused_2509_; 
v_unused_2509_ = lean_ctor_get(v___x_2499_, 0);
lean_dec(v_unused_2509_);
v___x_2501_ = v___x_2499_;
v_isShared_2502_ = v_isSharedCheck_2508_;
goto v_resetjp_2500_;
}
else
{
lean_dec(v___x_2499_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2508_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = lean_box(v___x_2259_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 1);
lean_ctor_set(v___x_2501_, 0, v___x_2503_);
v___x_2505_ = v___x_2501_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2284_);
v_a_2266_ = v___x_2506_;
goto v___jp_2265_;
}
}
}
else
{
lean_object* v_a_2510_; 
v_a_2510_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2499_);
v___y_2418_ = v___y_2428_;
v___y_2419_ = v___y_2429_;
v___y_2420_ = v___y_2430_;
v___y_2421_ = v___y_2431_;
v___y_2422_ = v___y_2433_;
v___y_2423_ = v___y_2432_;
v_a_2424_ = v_a_2510_;
goto v___jp_2417_;
}
}
else
{
lean_object* v_a_2511_; 
v_a_2511_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2511_);
lean_dec_ref(v___x_2497_);
v___y_2418_ = v___y_2428_;
v___y_2419_ = v___y_2429_;
v___y_2420_ = v___y_2430_;
v___y_2421_ = v___y_2431_;
v___y_2422_ = v___y_2433_;
v___y_2423_ = v___y_2432_;
v_a_2424_ = v_a_2511_;
goto v___jp_2417_;
}
}
else
{
lean_object* v_a_2512_; 
lean_dec(v_a_2484_);
lean_dec(v_a_2435_);
v_a_2512_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___x_2485_);
v___y_2418_ = v___y_2428_;
v___y_2419_ = v___y_2429_;
v___y_2420_ = v___y_2430_;
v___y_2421_ = v___y_2431_;
v___y_2422_ = v___y_2433_;
v___y_2423_ = v___y_2432_;
v_a_2424_ = v_a_2512_;
goto v___jp_2417_;
}
}
else
{
lean_object* v_a_2513_; 
lean_dec(v_a_2435_);
v_a_2513_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2513_);
lean_dec_ref(v___x_2483_);
v___y_2418_ = v___y_2428_;
v___y_2419_ = v___y_2429_;
v___y_2420_ = v___y_2430_;
v___y_2421_ = v___y_2431_;
v___y_2422_ = v___y_2433_;
v___y_2423_ = v___y_2432_;
v_a_2424_ = v_a_2513_;
goto v___jp_2417_;
}
}
}
else
{
lean_object* v_a_2514_; 
lean_dec(v_a_2435_);
v_a_2514_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2479_);
v___y_2418_ = v___y_2428_;
v___y_2419_ = v___y_2429_;
v___y_2420_ = v___y_2430_;
v___y_2421_ = v___y_2431_;
v___y_2422_ = v___y_2433_;
v___y_2423_ = v___y_2432_;
v_a_2424_ = v_a_2514_;
goto v___jp_2417_;
}
}
}
}
else
{
lean_object* v_a_2517_; 
v_a_2517_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2517_);
lean_dec_ref(v___x_2434_);
v___y_2418_ = v___y_2428_;
v___y_2419_ = v___y_2429_;
v___y_2420_ = v___y_2430_;
v___y_2421_ = v___y_2431_;
v___y_2422_ = v___y_2433_;
v___y_2423_ = v___y_2432_;
v_a_2424_ = v_a_2517_;
goto v___jp_2417_;
}
}
v___jp_2518_:
{
if (v___y_2525_ == 0)
{
v___y_2399_ = v___y_2524_;
v___y_2400_ = v___y_2523_;
v___y_2401_ = v___y_2521_;
v___y_2402_ = v___y_2520_;
v___y_2403_ = v___y_2519_;
v___y_2404_ = v___y_2522_;
goto v___jp_2398_;
}
else
{
v___y_2428_ = v___y_2519_;
v___y_2429_ = v___y_2520_;
v___y_2430_ = v___y_2521_;
v___y_2431_ = v___y_2522_;
v___y_2432_ = v___y_2523_;
v___y_2433_ = v___y_2524_;
goto v___jp_2427_;
}
}
v___jp_2526_:
{
if (v___y_2534_ == 0)
{
lean_dec_ref(v___y_2531_);
v___y_2519_ = v___y_2527_;
v___y_2520_ = v___y_2528_;
v___y_2521_ = v___y_2529_;
v___y_2522_ = v___y_2530_;
v___y_2523_ = v___y_2533_;
v___y_2524_ = v___y_2532_;
v___y_2525_ = v___x_2353_;
goto v___jp_2518_;
}
else
{
uint8_t v___x_2535_; 
v___x_2535_ = l_Lean_Expr_hasFVar(v___y_2531_);
lean_dec_ref(v___y_2531_);
if (v___x_2535_ == 0)
{
v___y_2428_ = v___y_2527_;
v___y_2429_ = v___y_2528_;
v___y_2430_ = v___y_2529_;
v___y_2431_ = v___y_2530_;
v___y_2432_ = v___y_2533_;
v___y_2433_ = v___y_2532_;
goto v___jp_2427_;
}
else
{
v___y_2519_ = v___y_2527_;
v___y_2520_ = v___y_2528_;
v___y_2521_ = v___y_2529_;
v___y_2522_ = v___y_2530_;
v___y_2523_ = v___y_2533_;
v___y_2524_ = v___y_2532_;
v___y_2525_ = v___x_2353_;
goto v___jp_2518_;
}
}
}
v___jp_2536_:
{
lean_object* v___x_2544_; 
lean_inc_ref(v___x_2397_);
v___x_2544_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2397_, v___y_2538_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; uint8_t v___x_2546_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v___x_2546_ = l_Lean_Expr_hasMVar(v_a_2545_);
if (v___x_2546_ == 0)
{
v___y_2527_ = v___y_2537_;
v___y_2528_ = v___y_2538_;
v___y_2529_ = v___y_2539_;
v___y_2530_ = v___y_2540_;
v___y_2531_ = v_a_2545_;
v___y_2532_ = v___y_2541_;
v___y_2533_ = v___y_2542_;
v___y_2534_ = v___y_2543_;
goto v___jp_2526_;
}
else
{
v___y_2527_ = v___y_2537_;
v___y_2528_ = v___y_2538_;
v___y_2529_ = v___y_2539_;
v___y_2530_ = v___y_2540_;
v___y_2531_ = v_a_2545_;
v___y_2532_ = v___y_2541_;
v___y_2533_ = v___y_2542_;
v___y_2534_ = v___x_2353_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec_ref(v___x_2397_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2547_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2544_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2544_);
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
v___jp_2555_:
{
if (v___y_2562_ == 0)
{
v___y_2399_ = v___y_2561_;
v___y_2400_ = v___y_2560_;
v___y_2401_ = v___y_2558_;
v___y_2402_ = v___y_2557_;
v___y_2403_ = v___y_2556_;
v___y_2404_ = v___y_2559_;
goto v___jp_2398_;
}
else
{
v___y_2537_ = v___y_2556_;
v___y_2538_ = v___y_2557_;
v___y_2539_ = v___y_2558_;
v___y_2540_ = v___y_2559_;
v___y_2541_ = v___y_2561_;
v___y_2542_ = v___y_2560_;
v___y_2543_ = v___y_2562_;
goto v___jp_2536_;
}
}
v___jp_2563_:
{
uint8_t v_useDecide_2570_; 
v_useDecide_2570_ = lean_ctor_get_uint8(v_config_2248_, sizeof(void*)*1);
if (v_useDecide_2570_ == 0)
{
v___y_2556_ = v___y_2568_;
v___y_2557_ = v___y_2567_;
v___y_2558_ = v___y_2566_;
v___y_2559_ = v___y_2569_;
v___y_2560_ = v_isHEq_2565_;
v___y_2561_ = v___y_2564_;
v___y_2562_ = v___x_2353_;
goto v___jp_2555_;
}
else
{
uint8_t v___x_2571_; 
v___x_2571_ = l_Lean_Expr_hasFVar(v___x_2397_);
if (v___x_2571_ == 0)
{
v___y_2537_ = v___y_2568_;
v___y_2538_ = v___y_2567_;
v___y_2539_ = v___y_2566_;
v___y_2540_ = v___y_2569_;
v___y_2541_ = v___y_2564_;
v___y_2542_ = v_isHEq_2565_;
v___y_2543_ = v_useDecide_2570_;
goto v___jp_2536_;
}
else
{
v___y_2556_ = v___y_2568_;
v___y_2557_ = v___y_2567_;
v___y_2558_ = v___y_2566_;
v___y_2559_ = v___y_2569_;
v___y_2560_ = v_isHEq_2565_;
v___y_2561_ = v___y_2564_;
v___y_2562_ = v___x_2353_;
goto v___jp_2555_;
}
}
}
v___jp_2572_:
{
lean_object* v___x_2580_; 
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2578_);
lean_inc(v___y_2577_);
lean_inc_ref(v___y_2579_);
v___x_2580_ = l_Lean_Meta_isExprDefEq(v___y_2573_, v___y_2574_, v___y_2579_, v___y_2577_, v___y_2578_, v___y_2575_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; uint8_t v___x_2582_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref(v___x_2580_);
v___x_2582_ = lean_unbox(v_a_2581_);
lean_dec(v_a_2581_);
if (v___x_2582_ == 0)
{
v___y_2564_ = v___y_2576_;
v_isHEq_2565_ = v___x_2259_;
v___y_2566_ = v___y_2579_;
v___y_2567_ = v___y_2577_;
v___y_2568_ = v___y_2578_;
v___y_2569_ = v___y_2575_;
goto v___jp_2563_;
}
else
{
lean_object* v___x_2583_; 
lean_dec_ref(v___x_2397_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_config_2248_);
lean_inc(v_mvarId_2249_);
v___x_2583_ = l_Lean_MVarId_getType(v_mvarId_2249_, v___y_2579_, v___y_2577_, v___y_2578_, v___y_2575_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref(v___x_2583_);
v___x_2585_ = l_Lean_LocalDecl_toExpr(v_val_2280_);
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2578_);
lean_inc(v___y_2577_);
lean_inc_ref(v___y_2579_);
v___x_2586_ = l_Lean_Meta_mkEqOfHEq(v___x_2585_, v___x_2259_, v___y_2579_, v___y_2577_, v___y_2578_, v___y_2575_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2588_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref(v___x_2586_);
lean_inc(v___y_2577_);
v___x_2588_ = l_Lean_Meta_mkNoConfusion(v_a_2584_, v_a_2587_, v___y_2579_, v___y_2577_, v___y_2578_, v___y_2575_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2249_, v_a_2589_, v___y_2577_);
lean_dec(v___y_2577_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref(v___x_2590_);
v___x_2591_ = lean_box(v___x_2259_);
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v___x_2284_);
v_a_2266_ = v___x_2593_;
goto v___jp_2265_;
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v_a_2594_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2590_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2590_);
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
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v___y_2577_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2602_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2588_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2588_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_a_2584_);
lean_dec_ref(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2575_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2610_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2586_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2586_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2575_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2618_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2583_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2583_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec_ref(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2575_);
lean_dec_ref(v___x_2397_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2626_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2580_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2580_);
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
v___jp_2634_:
{
lean_object* v___x_2640_; 
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
lean_inc_ref(v___x_2397_);
v___x_2640_ = l_Lean_Meta_matchHEq_x3f(v___x_2397_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v___x_2640_);
if (lean_obj_tag(v_a_2641_) == 1)
{
lean_object* v_val_2642_; lean_object* v_snd_2643_; lean_object* v_snd_2644_; lean_object* v_fst_2645_; lean_object* v_fst_2646_; lean_object* v_fst_2647_; lean_object* v_snd_2648_; lean_object* v___x_2649_; 
v_val_2642_ = lean_ctor_get(v_a_2641_, 0);
lean_inc(v_val_2642_);
lean_dec_ref(v_a_2641_);
v_snd_2643_ = lean_ctor_get(v_val_2642_, 1);
lean_inc(v_snd_2643_);
v_snd_2644_ = lean_ctor_get(v_snd_2643_, 1);
lean_inc(v_snd_2644_);
v_fst_2645_ = lean_ctor_get(v_val_2642_, 0);
lean_inc(v_fst_2645_);
lean_dec(v_val_2642_);
v_fst_2646_ = lean_ctor_get(v_snd_2643_, 0);
lean_inc(v_fst_2646_);
lean_dec(v_snd_2643_);
v_fst_2647_ = lean_ctor_get(v_snd_2644_, 0);
lean_inc(v_fst_2647_);
v_snd_2648_ = lean_ctor_get(v_snd_2644_, 1);
lean_inc(v_snd_2648_);
lean_dec(v_snd_2644_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
v___x_2649_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2646_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref(v___x_2649_);
if (lean_obj_tag(v_a_2650_) == 1)
{
lean_object* v_val_2651_; lean_object* v___x_2652_; 
v_val_2651_ = lean_ctor_get(v_a_2650_, 0);
lean_inc(v_val_2651_);
lean_dec_ref(v_a_2650_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
v___x_2652_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2648_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
if (lean_obj_tag(v_a_2653_) == 1)
{
lean_object* v_toConstantVal_2654_; lean_object* v_val_2655_; lean_object* v_toConstantVal_2656_; lean_object* v_name_2657_; lean_object* v_name_2658_; uint8_t v___x_2659_; 
v_toConstantVal_2654_ = lean_ctor_get(v_val_2651_, 0);
lean_inc_ref(v_toConstantVal_2654_);
lean_dec(v_val_2651_);
v_val_2655_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_val_2655_);
lean_dec_ref(v_a_2653_);
v_toConstantVal_2656_ = lean_ctor_get(v_val_2655_, 0);
lean_inc_ref(v_toConstantVal_2656_);
lean_dec(v_val_2655_);
v_name_2657_ = lean_ctor_get(v_toConstantVal_2654_, 0);
lean_inc(v_name_2657_);
lean_dec_ref(v_toConstantVal_2654_);
v_name_2658_ = lean_ctor_get(v_toConstantVal_2656_, 0);
lean_inc(v_name_2658_);
lean_dec_ref(v_toConstantVal_2656_);
v___x_2659_ = lean_name_eq(v_name_2657_, v_name_2658_);
lean_dec(v_name_2658_);
lean_dec(v_name_2657_);
if (v___x_2659_ == 0)
{
v___y_2573_ = v_fst_2645_;
v___y_2574_ = v_fst_2647_;
v___y_2575_ = v___y_2639_;
v___y_2576_ = v_isEq_2635_;
v___y_2577_ = v___y_2637_;
v___y_2578_ = v___y_2638_;
v___y_2579_ = v___y_2636_;
goto v___jp_2572_;
}
else
{
if (v___x_2353_ == 0)
{
lean_dec(v_fst_2647_);
lean_dec(v_fst_2645_);
v___y_2564_ = v_isEq_2635_;
v_isHEq_2565_ = v___x_2259_;
v___y_2566_ = v___y_2636_;
v___y_2567_ = v___y_2637_;
v___y_2568_ = v___y_2638_;
v___y_2569_ = v___y_2639_;
goto v___jp_2563_;
}
else
{
v___y_2573_ = v_fst_2645_;
v___y_2574_ = v_fst_2647_;
v___y_2575_ = v___y_2639_;
v___y_2576_ = v_isEq_2635_;
v___y_2577_ = v___y_2637_;
v___y_2578_ = v___y_2638_;
v___y_2579_ = v___y_2636_;
goto v___jp_2572_;
}
}
}
else
{
lean_dec(v_a_2653_);
lean_dec(v_val_2651_);
lean_dec(v_fst_2647_);
lean_dec(v_fst_2645_);
v___y_2564_ = v_isEq_2635_;
v_isHEq_2565_ = v___x_2259_;
v___y_2566_ = v___y_2636_;
v___y_2567_ = v___y_2637_;
v___y_2568_ = v___y_2638_;
v___y_2569_ = v___y_2639_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v_val_2651_);
lean_dec(v_fst_2647_);
lean_dec(v_fst_2645_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v___x_2397_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2660_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2652_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2652_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_dec(v_a_2650_);
lean_dec(v_snd_2648_);
lean_dec(v_fst_2647_);
lean_dec(v_fst_2645_);
v___y_2564_ = v_isEq_2635_;
v_isHEq_2565_ = v___x_2259_;
v___y_2566_ = v___y_2636_;
v___y_2567_ = v___y_2637_;
v___y_2568_ = v___y_2638_;
v___y_2569_ = v___y_2639_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_snd_2648_);
lean_dec(v_fst_2647_);
lean_dec(v_fst_2645_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v___x_2397_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2668_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2649_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2649_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_dec(v_a_2641_);
v___y_2564_ = v_isEq_2635_;
v_isHEq_2565_ = v___x_2353_;
v___y_2566_ = v___y_2636_;
v___y_2567_ = v___y_2637_;
v___y_2568_ = v___y_2638_;
v___y_2569_ = v___y_2639_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v___x_2397_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2676_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2640_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2640_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
v___jp_2684_:
{
lean_object* v___x_2689_; 
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v___y_2686_);
lean_inc_ref(v___y_2685_);
lean_inc_ref(v___x_2397_);
v___x_2689_ = l_Lean_Meta_matchEq_x3f(v___x_2397_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref(v___x_2689_);
if (lean_obj_tag(v_a_2690_) == 1)
{
lean_object* v_val_2691_; lean_object* v_snd_2692_; lean_object* v_fst_2693_; lean_object* v_snd_2694_; lean_object* v___x_2695_; 
v_val_2691_ = lean_ctor_get(v_a_2690_, 0);
lean_inc(v_val_2691_);
lean_dec_ref(v_a_2690_);
v_snd_2692_ = lean_ctor_get(v_val_2691_, 1);
lean_inc(v_snd_2692_);
lean_dec(v_val_2691_);
v_fst_2693_ = lean_ctor_get(v_snd_2692_, 0);
lean_inc(v_fst_2693_);
v_snd_2694_ = lean_ctor_get(v_snd_2692_, 1);
lean_inc(v_snd_2694_);
lean_dec(v_snd_2692_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v___y_2686_);
lean_inc_ref(v___y_2685_);
v___x_2695_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2693_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
if (lean_obj_tag(v_a_2696_) == 1)
{
lean_object* v_val_2697_; lean_object* v___x_2698_; 
v_val_2697_ = lean_ctor_get(v_a_2696_, 0);
lean_inc(v_val_2697_);
lean_dec_ref(v_a_2696_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v___y_2686_);
lean_inc_ref(v___y_2685_);
v___x_2698_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2694_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2698_);
if (lean_obj_tag(v_a_2699_) == 1)
{
lean_object* v_toConstantVal_2700_; lean_object* v_val_2701_; lean_object* v_toConstantVal_2702_; lean_object* v_name_2703_; lean_object* v_name_2704_; uint8_t v___x_2705_; 
v_toConstantVal_2700_ = lean_ctor_get(v_val_2697_, 0);
lean_inc_ref(v_toConstantVal_2700_);
lean_dec(v_val_2697_);
v_val_2701_ = lean_ctor_get(v_a_2699_, 0);
lean_inc(v_val_2701_);
lean_dec_ref(v_a_2699_);
v_toConstantVal_2702_ = lean_ctor_get(v_val_2701_, 0);
lean_inc_ref(v_toConstantVal_2702_);
lean_dec(v_val_2701_);
v_name_2703_ = lean_ctor_get(v_toConstantVal_2700_, 0);
lean_inc(v_name_2703_);
lean_dec_ref(v_toConstantVal_2700_);
v_name_2704_ = lean_ctor_get(v_toConstantVal_2702_, 0);
lean_inc(v_name_2704_);
lean_dec_ref(v_toConstantVal_2702_);
v___x_2705_ = lean_name_eq(v_name_2703_, v_name_2704_);
lean_dec(v_name_2704_);
lean_dec(v_name_2703_);
if (v___x_2705_ == 0)
{
lean_dec_ref(v___x_2397_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_config_2248_);
v___y_2286_ = v___y_2688_;
v___y_2287_ = v___y_2687_;
v___y_2288_ = v___y_2685_;
v___y_2289_ = v___y_2686_;
goto v___jp_2285_;
}
else
{
if (v___x_2353_ == 0)
{
lean_del_object(v___x_2282_);
v_isEq_2635_ = v___x_2259_;
v___y_2636_ = v___y_2685_;
v___y_2637_ = v___y_2686_;
v___y_2638_ = v___y_2687_;
v___y_2639_ = v___y_2688_;
goto v___jp_2634_;
}
else
{
lean_dec_ref(v___x_2397_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_config_2248_);
v___y_2286_ = v___y_2688_;
v___y_2287_ = v___y_2687_;
v___y_2288_ = v___y_2685_;
v___y_2289_ = v___y_2686_;
goto v___jp_2285_;
}
}
}
else
{
lean_dec(v_a_2699_);
lean_dec(v_val_2697_);
lean_del_object(v___x_2282_);
v_isEq_2635_ = v___x_2259_;
v___y_2636_ = v___y_2685_;
v___y_2637_ = v___y_2686_;
v___y_2638_ = v___y_2687_;
v___y_2639_ = v___y_2688_;
goto v___jp_2634_;
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v_val_2697_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2706_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2698_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2698_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_dec(v_a_2696_);
lean_dec(v_snd_2694_);
lean_del_object(v___x_2282_);
v_isEq_2635_ = v___x_2259_;
v___y_2636_ = v___y_2685_;
v___y_2637_ = v___y_2686_;
v___y_2638_ = v___y_2687_;
v___y_2639_ = v___y_2688_;
goto v___jp_2634_;
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_snd_2694_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2714_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2695_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2695_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_dec(v_a_2690_);
lean_del_object(v___x_2282_);
v_isEq_2635_ = v___x_2353_;
v___y_2636_ = v___y_2685_;
v___y_2637_ = v___y_2686_;
v___y_2638_ = v___y_2687_;
v___y_2639_ = v___y_2688_;
goto v___jp_2634_;
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2722_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2689_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2689_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
v___jp_2730_:
{
lean_object* v___x_2735_; 
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc_ref(v___x_2397_);
v___x_2735_ = l_refutableHasNotBit_x3f(v___x_2397_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref(v___x_2735_);
if (lean_obj_tag(v_a_2736_) == 1)
{
lean_object* v_val_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_config_2248_);
v_val_2737_ = lean_ctor_get(v_a_2736_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_a_2736_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2739_ = v_a_2736_;
v_isShared_2740_ = v_isSharedCheck_2776_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_val_2737_);
lean_dec(v_a_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2776_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; 
lean_inc(v_mvarId_2249_);
v___x_2741_ = l_Lean_MVarId_getType(v_mvarId_2249_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref(v___x_2741_);
v___x_2743_ = l_Lean_LocalDecl_toExpr(v_val_2280_);
lean_inc(v___y_2732_);
v___x_2744_ = l_Lean_Meta_mkAbsurd(v_a_2742_, v_val_2737_, v___x_2743_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
v___x_2746_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2249_, v_a_2745_, v___y_2732_);
lean_dec(v___y_2732_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
lean_dec_ref(v___x_2746_);
v___x_2747_ = lean_box(v___x_2259_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2747_);
v___x_2749_ = v___x_2739_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
lean_ctor_set(v___x_2750_, 1, v___x_2284_);
v_a_2266_ = v___x_2750_;
goto v___jp_2265_;
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_del_object(v___x_2739_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v_a_2752_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2746_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2746_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_del_object(v___x_2739_);
lean_dec(v___y_2732_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2760_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2744_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2744_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_del_object(v___x_2739_);
lean_dec(v_val_2737_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2768_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2741_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2741_);
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
}
else
{
lean_object* v___x_2777_; 
lean_dec(v_a_2736_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc_ref(v___x_2397_);
v___x_2777_ = l_Lean_Meta_matchNe_x3f(v___x_2397_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref(v___x_2777_);
if (lean_obj_tag(v_a_2778_) == 1)
{
lean_object* v_val_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2848_; 
v_val_2779_ = lean_ctor_get(v_a_2778_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_a_2778_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2781_ = v_a_2778_;
v_isShared_2782_ = v_isSharedCheck_2848_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_val_2779_);
lean_dec(v_a_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2848_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_snd_2783_; lean_object* v_fst_2784_; lean_object* v_snd_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2847_; 
v_snd_2783_ = lean_ctor_get(v_val_2779_, 1);
lean_inc(v_snd_2783_);
lean_dec(v_val_2779_);
v_fst_2784_ = lean_ctor_get(v_snd_2783_, 0);
v_snd_2785_ = lean_ctor_get(v_snd_2783_, 1);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_snd_2783_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2787_ = v_snd_2783_;
v_isShared_2788_ = v_isSharedCheck_2847_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_snd_2785_);
lean_inc(v_fst_2784_);
lean_dec(v_snd_2783_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2847_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; 
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
lean_inc(v_fst_2784_);
v___x_2789_ = l_Lean_Meta_isExprDefEq(v_fst_2784_, v_snd_2785_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; uint8_t v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref(v___x_2789_);
v___x_2791_ = lean_unbox(v_a_2790_);
lean_dec(v_a_2790_);
if (v___x_2791_ == 0)
{
lean_del_object(v___x_2787_);
lean_dec(v_fst_2784_);
lean_del_object(v___x_2781_);
v___y_2685_ = v___y_2731_;
v___y_2686_ = v___y_2732_;
v___y_2687_ = v___y_2733_;
v___y_2688_ = v___y_2734_;
goto v___jp_2684_;
}
else
{
lean_object* v___x_2792_; 
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_config_2248_);
lean_inc(v_mvarId_2249_);
v___x_2792_ = l_Lean_MVarId_getType(v_mvarId_2249_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref(v___x_2792_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
lean_inc(v___y_2732_);
lean_inc_ref(v___y_2731_);
v___x_2794_ = l_Lean_Meta_mkEqRefl(v_fst_2784_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref(v___x_2794_);
v___x_2796_ = l_Lean_LocalDecl_toExpr(v_val_2280_);
lean_inc(v___y_2732_);
v___x_2797_ = l_Lean_Meta_mkAbsurd(v_a_2793_, v_a_2795_, v___x_2796_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref(v___x_2797_);
v___x_2799_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2249_, v_a_2798_, v___y_2732_);
lean_dec(v___y_2732_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
lean_dec_ref(v___x_2799_);
v___x_2800_ = lean_box(v___x_2259_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2800_);
v___x_2802_ = v___x_2781_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2804_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 1, v___x_2284_);
lean_ctor_set(v___x_2787_, 0, v___x_2802_);
v___x_2804_ = v___x_2787_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___x_2284_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
v_a_2266_ = v___x_2804_;
goto v___jp_2265_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_del_object(v___x_2787_);
lean_del_object(v___x_2781_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v_a_2807_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2799_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2799_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_del_object(v___x_2787_);
lean_del_object(v___x_2781_);
lean_dec(v___y_2732_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2815_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2797_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2797_);
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
lean_dec(v_a_2793_);
lean_del_object(v___x_2787_);
lean_del_object(v___x_2781_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2823_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2794_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2794_);
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
lean_del_object(v___x_2787_);
lean_dec(v_fst_2784_);
lean_del_object(v___x_2781_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2831_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2792_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2792_);
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
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_del_object(v___x_2787_);
lean_dec(v_fst_2784_);
lean_del_object(v___x_2781_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2839_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2789_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2789_);
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
}
else
{
lean_dec(v_a_2778_);
v___y_2685_ = v___y_2731_;
v___y_2686_ = v___y_2732_;
v___y_2687_ = v___y_2733_;
v___y_2688_ = v___y_2734_;
goto v___jp_2684_;
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2849_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2777_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2777_);
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
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2857_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2735_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2735_);
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
}
else
{
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v_a_2274_ = v___x_2325_;
goto v___jp_2273_;
}
v___jp_2285_:
{
lean_object* v___x_2290_; 
lean_inc(v_mvarId_2249_);
v___x_2290_ = l_Lean_MVarId_getType(v_mvarId_2249_, v___y_2288_, v___y_2289_, v___y_2287_, v___y_2286_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref(v___x_2290_);
v___x_2292_ = l_Lean_LocalDecl_toExpr(v_val_2280_);
lean_inc(v___y_2289_);
v___x_2293_ = l_Lean_Meta_mkNoConfusion(v_a_2291_, v___x_2292_, v___y_2288_, v___y_2289_, v___y_2287_, v___y_2286_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref(v___x_2293_);
v___x_2295_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2249_, v_a_2294_, v___y_2289_);
lean_dec(v___y_2289_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
lean_dec_ref(v___x_2295_);
v___x_2296_ = lean_box(v___x_2259_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2296_);
v___x_2298_ = v___x_2282_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2284_);
v_a_2266_ = v___x_2299_;
goto v___jp_2265_;
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_del_object(v___x_2282_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v_a_2301_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2295_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2295_);
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
lean_dec(v___y_2289_);
lean_del_object(v___x_2282_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2309_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2293_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2293_);
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
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_del_object(v___x_2282_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v_mvarId_2249_);
v_a_2317_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2290_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2290_);
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
v___jp_2326_:
{
lean_object* v_searchFuel_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_searchFuel_2331_ = lean_ctor_get(v_config_2248_, 0);
v___x_2332_ = l_Lean_LocalDecl_fvarId(v_val_2280_);
lean_dec(v_val_2280_);
lean_inc(v_searchFuel_2331_);
lean_inc(v_mvarId_2249_);
v___x_2333_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2249_, v___x_2332_, v_searchFuel_2331_, v___y_2327_, v___y_2330_, v___y_2328_, v___y_2329_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; uint8_t v___x_2335_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = lean_unbox(v_a_2334_);
lean_dec(v_a_2334_);
if (v___x_2335_ == 0)
{
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v_a_2274_ = v___x_2325_;
goto v___jp_2273_;
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v___x_2336_ = lean_box(v___x_2259_);
v___x_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
lean_ctor_set(v___x_2338_, 1, v___x_2284_);
v_a_2266_ = v___x_2338_;
goto v___jp_2265_;
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2339_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2333_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2333_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
v___jp_2347_:
{
if (v___y_2352_ == 0)
{
lean_dec(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v_a_2274_ = v___x_2325_;
goto v___jp_2273_;
}
else
{
v___y_2327_ = v___y_2348_;
v___y_2328_ = v___y_2349_;
v___y_2329_ = v___y_2350_;
v___y_2330_ = v___y_2351_;
goto v___jp_2326_;
}
}
v___jp_2354_:
{
if (v___y_2359_ == 0)
{
v___y_2327_ = v___y_2355_;
v___y_2328_ = v___y_2356_;
v___y_2329_ = v___y_2357_;
v___y_2330_ = v___y_2358_;
goto v___jp_2326_;
}
else
{
v___y_2348_ = v___y_2355_;
v___y_2349_ = v___y_2356_;
v___y_2350_ = v___y_2357_;
v___y_2351_ = v___y_2358_;
v___y_2352_ = v___x_2353_;
goto v___jp_2347_;
}
}
v___jp_2360_:
{
if (v___y_2366_ == 0)
{
v___y_2348_ = v___y_2361_;
v___y_2349_ = v___y_2362_;
v___y_2350_ = v___y_2363_;
v___y_2351_ = v___y_2364_;
v___y_2352_ = v___x_2353_;
goto v___jp_2347_;
}
else
{
v___y_2355_ = v___y_2361_;
v___y_2356_ = v___y_2362_;
v___y_2357_ = v___y_2363_;
v___y_2358_ = v___y_2364_;
v___y_2359_ = v___y_2365_;
goto v___jp_2354_;
}
}
v___jp_2367_:
{
uint8_t v_emptyType_2374_; 
v_emptyType_2374_ = lean_ctor_get_uint8(v_config_2248_, sizeof(void*)*1 + 1);
if (v_emptyType_2374_ == 0)
{
v___y_2361_ = v___y_2370_;
v___y_2362_ = v___y_2372_;
v___y_2363_ = v___y_2373_;
v___y_2364_ = v___y_2371_;
v___y_2365_ = v___y_2369_;
v___y_2366_ = v___x_2353_;
goto v___jp_2360_;
}
else
{
if (v___y_2368_ == 0)
{
v___y_2355_ = v___y_2370_;
v___y_2356_ = v___y_2372_;
v___y_2357_ = v___y_2373_;
v___y_2358_ = v___y_2371_;
v___y_2359_ = v___y_2369_;
goto v___jp_2354_;
}
else
{
v___y_2361_ = v___y_2370_;
v___y_2362_ = v___y_2372_;
v___y_2363_ = v___y_2373_;
v___y_2364_ = v___y_2371_;
v___y_2365_ = v___y_2369_;
v___y_2366_ = v___x_2353_;
goto v___jp_2360_;
}
}
}
v___jp_2375_:
{
if (v___y_2382_ == 0)
{
v___y_2368_ = v___y_2381_;
v___y_2369_ = v___y_2380_;
v___y_2370_ = v___y_2377_;
v___y_2371_ = v___y_2379_;
v___y_2372_ = v___y_2378_;
v___y_2373_ = v___y_2376_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2383_; 
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2378_);
lean_inc(v___y_2379_);
lean_inc_ref(v___y_2377_);
lean_inc(v_val_2280_);
lean_inc(v_mvarId_2249_);
v___x_2383_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2249_, v_val_2280_, v___y_2377_, v___y_2379_, v___y_2378_, v___y_2376_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; uint8_t v___x_2385_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = lean_unbox(v_a_2384_);
lean_dec(v_a_2384_);
if (v___x_2385_ == 0)
{
v___y_2368_ = v___y_2381_;
v___y_2369_ = v___y_2380_;
v___y_2370_ = v___y_2377_;
v___y_2371_ = v___y_2379_;
v___y_2372_ = v___y_2378_;
v___y_2373_ = v___y_2376_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v_val_2280_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v___x_2386_ = lean_box(v___x_2259_);
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v___x_2284_);
v_a_2266_ = v___x_2388_;
goto v___jp_2265_;
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v_val_2280_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v_mvarId_2249_);
lean_dec_ref(v_config_2248_);
v_a_2389_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2383_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2383_);
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
}
}
v___jp_2265_:
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_a_2266_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2267_);
v___x_2269_ = v___x_2263_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_snd_2261_);
v___x_2269_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
}
v___jp_2273_:
{
lean_object* v___x_2275_; size_t v___x_2276_; size_t v___x_2277_; 
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2272_);
lean_ctor_set(v___x_2275_, 1, v_a_2274_);
v___x_2276_ = ((size_t)1ULL);
v___x_2277_ = lean_usize_add(v_i_2252_, v___x_2276_);
v_i_2252_ = v___x_2277_;
v_b_2253_ = v___x_2275_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2931_, lean_object* v_mvarId_2932_, lean_object* v_as_2933_, lean_object* v_sz_2934_, lean_object* v_i_2935_, lean_object* v_b_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
size_t v_sz_boxed_2942_; size_t v_i_boxed_2943_; lean_object* v_res_2944_; 
v_sz_boxed_2942_ = lean_unbox_usize(v_sz_2934_);
lean_dec(v_sz_2934_);
v_i_boxed_2943_ = lean_unbox_usize(v_i_2935_);
lean_dec(v_i_2935_);
v_res_2944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2931_, v_mvarId_2932_, v_as_2933_, v_sz_boxed_2942_, v_i_boxed_2943_, v_b_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec_ref(v_as_2933_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2945_, lean_object* v_mvarId_2946_, lean_object* v_as_2947_, size_t v_sz_2948_, size_t v_i_2949_, lean_object* v_b_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v___x_2956_; 
v___x_2956_ = lean_usize_dec_lt(v_i_2949_, v_sz_2948_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; 
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_b_2950_);
return v___x_2957_;
}
else
{
lean_object* v_snd_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_3626_; 
v_snd_2958_ = lean_ctor_get(v_b_2950_, 1);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_b_2950_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v_b_2950_, 0);
lean_dec(v_unused_3627_);
v___x_2960_ = v_b_2950_;
v_isShared_2961_ = v_isSharedCheck_3626_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_snd_2958_);
lean_dec(v_b_2950_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_3626_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v_a_2963_; lean_object* v___x_2969_; lean_object* v_a_2971_; lean_object* v_a_2976_; 
v___x_2969_ = lean_box(0);
v_a_2976_ = lean_array_uget(v_as_2947_, v_i_2949_);
if (lean_obj_tag(v_a_2976_) == 0)
{
lean_del_object(v___x_2960_);
v_a_2971_ = v_snd_2958_;
goto v___jp_2970_;
}
else
{
lean_object* v_val_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3625_; 
v_val_2977_ = lean_ctor_get(v_a_2976_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_a_2976_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_2979_ = v_a_2976_;
v_isShared_2980_ = v_isSharedCheck_3625_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_val_2977_);
lean_dec(v_a_2976_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3625_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___x_3022_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; uint8_t v___y_3049_; uint8_t v___x_3050_; lean_object* v___y_3052_; uint8_t v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3058_; uint8_t v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; uint8_t v___y_3063_; uint8_t v___y_3065_; uint8_t v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3073_; uint8_t v___y_3074_; uint8_t v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; uint8_t v___y_3079_; 
v___x_2981_ = lean_box(0);
v___x_3022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_3050_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2977_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3094_; uint8_t v___y_3096_; uint8_t v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3105_; uint8_t v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; uint8_t v___y_3110_; lean_object* v___y_3111_; uint8_t v___y_3112_; lean_object* v___y_3115_; uint8_t v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; uint8_t v___y_3119_; lean_object* v___y_3120_; lean_object* v_a_3121_; lean_object* v___y_3125_; uint8_t v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; uint8_t v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3216_; uint8_t v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; uint8_t v___y_3220_; lean_object* v___y_3221_; uint8_t v___y_3222_; lean_object* v___y_3224_; uint8_t v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; uint8_t v___y_3229_; lean_object* v___y_3230_; uint8_t v___y_3231_; lean_object* v___y_3234_; uint8_t v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; uint8_t v___y_3238_; lean_object* v___y_3239_; uint8_t v___y_3240_; lean_object* v___y_3253_; uint8_t v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; lean_object* v___y_3258_; uint8_t v___y_3259_; uint8_t v___y_3261_; uint8_t v_isHEq_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; uint8_t v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; uint8_t v_isEq_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___x_3562_; 
v___x_3094_ = l_Lean_LocalDecl_type(v_val_2977_);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2951_);
lean_inc_ref(v___x_3094_);
v___x_3562_ = l_Lean_Meta_matchNot_x3f(v___x_3094_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref(v___x_3562_);
if (lean_obj_tag(v_a_3563_) == 1)
{
lean_object* v_val_3564_; lean_object* v___x_3565_; 
v_val_3564_ = lean_ctor_get(v_a_3563_, 0);
lean_inc(v_val_3564_);
lean_dec_ref(v_a_3563_);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2951_);
v___x_3565_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3564_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref(v___x_3565_);
if (lean_obj_tag(v_a_3566_) == 1)
{
lean_object* v_val_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3608_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec_ref(v_config_2945_);
v_val_3567_ = lean_ctor_get(v_a_3566_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_a_3566_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3569_ = v_a_3566_;
v_isShared_3570_ = v_isSharedCheck_3608_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_val_3567_);
lean_dec(v_a_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3608_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; 
lean_inc(v_mvarId_2946_);
v___x_3571_ = l_Lean_MVarId_getType(v_mvarId_2946_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3572_);
lean_dec_ref(v___x_3571_);
v___x_3573_ = l_Lean_LocalDecl_toExpr(v_val_2977_);
v___x_3574_ = l_Lean_mkFVar(v_val_3567_);
v___x_3575_ = l_Lean_Expr_app___override(v___x_3573_, v___x_3574_);
lean_inc(v___y_2952_);
v___x_3576_ = l_Lean_Meta_mkFalseElim(v_a_3572_, v___x_3575_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3578_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref(v___x_3576_);
v___x_3578_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2946_, v_a_3577_, v___y_2952_);
lean_dec(v___y_2952_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3581_; 
lean_dec_ref(v___x_3578_);
v___x_3579_ = lean_box(v___x_2956_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3579_);
v___x_3581_ = v___x_3569_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; 
v___x_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
lean_ctor_set(v___x_3582_, 1, v___x_2981_);
v_a_2963_ = v___x_3582_;
goto v___jp_2962_;
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_del_object(v___x_3569_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
v_a_3584_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3578_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3578_);
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
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_del_object(v___x_3569_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2952_);
lean_dec(v_mvarId_2946_);
v_a_3592_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3576_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3576_);
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
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_del_object(v___x_3569_);
lean_dec(v_val_3567_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
v_a_3600_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3571_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3571_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
else
{
lean_dec(v_a_3566_);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2951_);
v___y_3428_ = v___y_2951_;
v___y_3429_ = v___y_2952_;
v___y_3430_ = v___y_2953_;
v___y_3431_ = v___y_2954_;
goto v___jp_3427_;
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3609_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3565_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3565_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_dec(v_a_3563_);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2951_);
v___y_3428_ = v___y_2951_;
v___y_3429_ = v___y_2952_;
v___y_3430_ = v___y_2953_;
v___y_3431_ = v___y_2954_;
goto v___jp_3427_;
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3617_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3562_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3562_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
v___jp_3095_:
{
uint8_t v_genDiseq_3102_; 
v_genDiseq_3102_ = lean_ctor_get_uint8(v_config_2945_, sizeof(void*)*1 + 2);
if (v_genDiseq_3102_ == 0)
{
lean_dec_ref(v___x_3094_);
v___y_3073_ = v___y_3099_;
v___y_3074_ = v___y_3096_;
v___y_3075_ = v___y_3097_;
v___y_3076_ = v___y_3100_;
v___y_3077_ = v___y_3101_;
v___y_3078_ = v___y_3098_;
v___y_3079_ = v___x_3050_;
goto v___jp_3072_;
}
else
{
uint8_t v___x_3103_; 
v___x_3103_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3094_);
v___y_3073_ = v___y_3099_;
v___y_3074_ = v___y_3096_;
v___y_3075_ = v___y_3097_;
v___y_3076_ = v___y_3100_;
v___y_3077_ = v___y_3101_;
v___y_3078_ = v___y_3098_;
v___y_3079_ = v___x_3103_;
goto v___jp_3072_;
}
}
v___jp_3104_:
{
if (v___y_3112_ == 0)
{
lean_dec_ref(v___y_3109_);
v___y_3096_ = v___y_3106_;
v___y_3097_ = v___y_3110_;
v___y_3098_ = v___y_3108_;
v___y_3099_ = v___y_3105_;
v___y_3100_ = v___y_3111_;
v___y_3101_ = v___y_3107_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3113_; 
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec(v___y_3105_);
lean_dec_ref(v___x_3094_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v___x_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___y_3109_);
return v___x_3113_;
}
}
v___jp_3114_:
{
uint8_t v___x_3122_; 
v___x_3122_ = l_Lean_Exception_isInterrupt(v_a_3121_);
if (v___x_3122_ == 0)
{
uint8_t v___x_3123_; 
lean_inc_ref(v_a_3121_);
v___x_3123_ = l_Lean_Exception_isRuntime(v_a_3121_);
v___y_3105_ = v___y_3115_;
v___y_3106_ = v___y_3116_;
v___y_3107_ = v___y_3117_;
v___y_3108_ = v___y_3118_;
v___y_3109_ = v_a_3121_;
v___y_3110_ = v___y_3119_;
v___y_3111_ = v___y_3120_;
v___y_3112_ = v___x_3123_;
goto v___jp_3104_;
}
else
{
v___y_3105_ = v___y_3115_;
v___y_3106_ = v___y_3116_;
v___y_3107_ = v___y_3117_;
v___y_3108_ = v___y_3118_;
v___y_3109_ = v_a_3121_;
v___y_3110_ = v___y_3119_;
v___y_3111_ = v___y_3120_;
v___y_3112_ = v___x_3122_;
goto v___jp_3104_;
}
}
v___jp_3124_:
{
lean_object* v___x_3131_; 
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3130_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3128_);
lean_inc_ref(v___x_3094_);
v___x_3131_ = l_Lean_Meta_mkDecide(v___x_3094_, v___y_3128_, v___y_3125_, v___y_3130_, v___y_3127_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3133_; uint8_t v_foApprox_3134_; uint8_t v_ctxApprox_3135_; uint8_t v_quasiPatternApprox_3136_; uint8_t v_constApprox_3137_; uint8_t v_isDefEqStuckEx_3138_; uint8_t v_unificationHints_3139_; uint8_t v_proofIrrelevance_3140_; uint8_t v_assignSyntheticOpaque_3141_; uint8_t v_offsetCnstrs_3142_; uint8_t v_etaStruct_3143_; uint8_t v_univApprox_3144_; uint8_t v_iota_3145_; uint8_t v_beta_3146_; uint8_t v_proj_3147_; uint8_t v_zeta_3148_; uint8_t v_zetaDelta_3149_; uint8_t v_zetaUnused_3150_; uint8_t v_zetaHave_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3213_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref(v___x_3131_);
v___x_3133_ = l_Lean_Meta_Context_config(v___y_3128_);
v_foApprox_3134_ = lean_ctor_get_uint8(v___x_3133_, 0);
v_ctxApprox_3135_ = lean_ctor_get_uint8(v___x_3133_, 1);
v_quasiPatternApprox_3136_ = lean_ctor_get_uint8(v___x_3133_, 2);
v_constApprox_3137_ = lean_ctor_get_uint8(v___x_3133_, 3);
v_isDefEqStuckEx_3138_ = lean_ctor_get_uint8(v___x_3133_, 4);
v_unificationHints_3139_ = lean_ctor_get_uint8(v___x_3133_, 5);
v_proofIrrelevance_3140_ = lean_ctor_get_uint8(v___x_3133_, 6);
v_assignSyntheticOpaque_3141_ = lean_ctor_get_uint8(v___x_3133_, 7);
v_offsetCnstrs_3142_ = lean_ctor_get_uint8(v___x_3133_, 8);
v_etaStruct_3143_ = lean_ctor_get_uint8(v___x_3133_, 10);
v_univApprox_3144_ = lean_ctor_get_uint8(v___x_3133_, 11);
v_iota_3145_ = lean_ctor_get_uint8(v___x_3133_, 12);
v_beta_3146_ = lean_ctor_get_uint8(v___x_3133_, 13);
v_proj_3147_ = lean_ctor_get_uint8(v___x_3133_, 14);
v_zeta_3148_ = lean_ctor_get_uint8(v___x_3133_, 15);
v_zetaDelta_3149_ = lean_ctor_get_uint8(v___x_3133_, 16);
v_zetaUnused_3150_ = lean_ctor_get_uint8(v___x_3133_, 17);
v_zetaHave_3151_ = lean_ctor_get_uint8(v___x_3133_, 18);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3153_ = v___x_3133_;
v_isShared_3154_ = v_isSharedCheck_3213_;
goto v_resetjp_3152_;
}
else
{
lean_dec(v___x_3133_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3213_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
uint8_t v_trackZetaDelta_3155_; lean_object* v_zetaDeltaSet_3156_; lean_object* v_lctx_3157_; lean_object* v_localInstances_3158_; lean_object* v_defEqCtx_x3f_3159_; lean_object* v_synthPendingDepth_3160_; lean_object* v_canUnfold_x3f_3161_; uint8_t v_univApprox_3162_; uint8_t v_inTypeClassResolution_3163_; uint8_t v_cacheInferType_3164_; uint8_t v___x_3165_; lean_object* v_config_3167_; 
v_trackZetaDelta_3155_ = lean_ctor_get_uint8(v___y_3128_, sizeof(void*)*7);
v_zetaDeltaSet_3156_ = lean_ctor_get(v___y_3128_, 1);
v_lctx_3157_ = lean_ctor_get(v___y_3128_, 2);
v_localInstances_3158_ = lean_ctor_get(v___y_3128_, 3);
v_defEqCtx_x3f_3159_ = lean_ctor_get(v___y_3128_, 4);
v_synthPendingDepth_3160_ = lean_ctor_get(v___y_3128_, 5);
v_canUnfold_x3f_3161_ = lean_ctor_get(v___y_3128_, 6);
v_univApprox_3162_ = lean_ctor_get_uint8(v___y_3128_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3163_ = lean_ctor_get_uint8(v___y_3128_, sizeof(void*)*7 + 2);
v_cacheInferType_3164_ = lean_ctor_get_uint8(v___y_3128_, sizeof(void*)*7 + 3);
v___x_3165_ = 1;
if (v_isShared_3154_ == 0)
{
v_config_3167_ = v___x_3153_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 0, v_foApprox_3134_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 1, v_ctxApprox_3135_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 2, v_quasiPatternApprox_3136_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 3, v_constApprox_3137_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 4, v_isDefEqStuckEx_3138_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 5, v_unificationHints_3139_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 6, v_proofIrrelevance_3140_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 7, v_assignSyntheticOpaque_3141_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 8, v_offsetCnstrs_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 10, v_etaStruct_3143_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 11, v_univApprox_3144_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 12, v_iota_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 13, v_beta_3146_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 14, v_proj_3147_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 15, v_zeta_3148_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 16, v_zetaDelta_3149_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 17, v_zetaUnused_3150_);
lean_ctor_set_uint8(v_reuseFailAlloc_3212_, 18, v_zetaHave_3151_);
v_config_3167_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
uint64_t v___x_3168_; uint64_t v___x_3169_; uint64_t v___x_3170_; uint64_t v___x_3171_; uint64_t v___x_3172_; uint64_t v_key_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_ctor_set_uint8(v_config_3167_, 9, v___x_3165_);
v___x_3168_ = l_Lean_Meta_Context_configKey(v___y_3128_);
v___x_3169_ = 2ULL;
v___x_3170_ = lean_uint64_shift_right(v___x_3168_, v___x_3169_);
v___x_3171_ = lean_uint64_shift_left(v___x_3170_, v___x_3169_);
v___x_3172_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_3173_ = lean_uint64_lor(v___x_3171_, v___x_3172_);
v___x_3174_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3174_, 0, v_config_3167_);
lean_ctor_set_uint64(v___x_3174_, sizeof(void*)*1, v_key_3173_);
lean_inc(v_canUnfold_x3f_3161_);
lean_inc(v_synthPendingDepth_3160_);
lean_inc(v_defEqCtx_x3f_3159_);
lean_inc_ref(v_localInstances_3158_);
lean_inc_ref(v_lctx_3157_);
lean_inc(v_zetaDeltaSet_3156_);
v___x_3175_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
lean_ctor_set(v___x_3175_, 1, v_zetaDeltaSet_3156_);
lean_ctor_set(v___x_3175_, 2, v_lctx_3157_);
lean_ctor_set(v___x_3175_, 3, v_localInstances_3158_);
lean_ctor_set(v___x_3175_, 4, v_defEqCtx_x3f_3159_);
lean_ctor_set(v___x_3175_, 5, v_synthPendingDepth_3160_);
lean_ctor_set(v___x_3175_, 6, v_canUnfold_x3f_3161_);
lean_ctor_set_uint8(v___x_3175_, sizeof(void*)*7, v_trackZetaDelta_3155_);
lean_ctor_set_uint8(v___x_3175_, sizeof(void*)*7 + 1, v_univApprox_3162_);
lean_ctor_set_uint8(v___x_3175_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3163_);
lean_ctor_set_uint8(v___x_3175_, sizeof(void*)*7 + 3, v_cacheInferType_3164_);
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3130_);
lean_inc(v___y_3125_);
lean_inc(v_a_3132_);
v___x_3176_ = lean_whnf(v_a_3132_, v___x_3175_, v___y_3125_, v___y_3130_, v___y_3127_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref(v___x_3176_);
v___x_3178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_3179_ = l_Lean_Expr_isConstOf(v_a_3177_, v___x_3178_);
lean_dec(v_a_3177_);
if (v___x_3179_ == 0)
{
lean_dec(v_a_3132_);
v___y_3096_ = v___y_3126_;
v___y_3097_ = v___y_3129_;
v___y_3098_ = v___y_3128_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___y_3130_;
v___y_3101_ = v___y_3127_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3180_; 
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3130_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3128_);
lean_inc(v_a_3132_);
v___x_3180_ = l_Lean_Meta_mkEqRefl(v_a_3132_, v___y_3128_, v___y_3125_, v___y_3130_, v___y_3127_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3182_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
lean_dec_ref(v___x_3180_);
lean_inc(v_mvarId_2946_);
v___x_3182_ = l_Lean_MVarId_getType(v_mvarId_2946_, v___y_3128_, v___y_3125_, v___y_3130_, v___y_3127_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v_nargs_3184_; lean_object* v___x_3185_; lean_object* v_dummy_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref(v___x_3182_);
v_nargs_3184_ = l_Lean_Expr_getAppNumArgs(v_a_3132_);
v___x_3185_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_3186_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_3184_);
v___x_3187_ = lean_mk_array(v_nargs_3184_, v_dummy_3186_);
v___x_3188_ = lean_unsigned_to_nat(1u);
v___x_3189_ = lean_nat_sub(v_nargs_3184_, v___x_3188_);
lean_dec(v_nargs_3184_);
v___x_3190_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3132_, v___x_3187_, v___x_3189_);
v___x_3191_ = lean_array_push(v___x_3190_, v_a_3181_);
v___x_3192_ = l_Lean_mkAppN(v___x_3185_, v___x_3191_);
lean_dec_ref(v___x_3191_);
lean_inc(v_val_2977_);
v___x_3193_ = l_Lean_LocalDecl_toExpr(v_val_2977_);
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3130_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3128_);
v___x_3194_ = l_Lean_Meta_mkAbsurd(v_a_3183_, v___x_3193_, v___x_3192_, v___y_3128_, v___y_3125_, v___y_3130_, v___y_3127_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref(v___x_3194_);
lean_inc(v_mvarId_2946_);
v___x_3196_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2946_, v_a_3195_, v___y_3125_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v___y_3130_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec(v___y_3125_);
lean_dec_ref(v___x_3094_);
lean_dec(v_val_2977_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; 
v_unused_3206_ = lean_ctor_get(v___x_3196_, 0);
lean_dec(v_unused_3206_);
v___x_3198_ = v___x_3196_;
v_isShared_3199_ = v_isSharedCheck_3205_;
goto v_resetjp_3197_;
}
else
{
lean_dec(v___x_3196_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3205_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3200_ = lean_box(v___x_2956_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set_tag(v___x_3198_, 1);
lean_ctor_set(v___x_3198_, 0, v___x_3200_);
v___x_3202_ = v___x_3198_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v___x_2981_);
v_a_2963_ = v___x_3203_;
goto v___jp_2962_;
}
}
}
else
{
lean_object* v_a_3207_; 
v_a_3207_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3207_);
lean_dec_ref(v___x_3196_);
v___y_3115_ = v___y_3125_;
v___y_3116_ = v___y_3126_;
v___y_3117_ = v___y_3127_;
v___y_3118_ = v___y_3128_;
v___y_3119_ = v___y_3129_;
v___y_3120_ = v___y_3130_;
v_a_3121_ = v_a_3207_;
goto v___jp_3114_;
}
}
else
{
lean_object* v_a_3208_; 
v_a_3208_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3208_);
lean_dec_ref(v___x_3194_);
v___y_3115_ = v___y_3125_;
v___y_3116_ = v___y_3126_;
v___y_3117_ = v___y_3127_;
v___y_3118_ = v___y_3128_;
v___y_3119_ = v___y_3129_;
v___y_3120_ = v___y_3130_;
v_a_3121_ = v_a_3208_;
goto v___jp_3114_;
}
}
else
{
lean_object* v_a_3209_; 
lean_dec(v_a_3181_);
lean_dec(v_a_3132_);
v_a_3209_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3209_);
lean_dec_ref(v___x_3182_);
v___y_3115_ = v___y_3125_;
v___y_3116_ = v___y_3126_;
v___y_3117_ = v___y_3127_;
v___y_3118_ = v___y_3128_;
v___y_3119_ = v___y_3129_;
v___y_3120_ = v___y_3130_;
v_a_3121_ = v_a_3209_;
goto v___jp_3114_;
}
}
else
{
lean_object* v_a_3210_; 
lean_dec(v_a_3132_);
v_a_3210_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3210_);
lean_dec_ref(v___x_3180_);
v___y_3115_ = v___y_3125_;
v___y_3116_ = v___y_3126_;
v___y_3117_ = v___y_3127_;
v___y_3118_ = v___y_3128_;
v___y_3119_ = v___y_3129_;
v___y_3120_ = v___y_3130_;
v_a_3121_ = v_a_3210_;
goto v___jp_3114_;
}
}
}
else
{
lean_object* v_a_3211_; 
lean_dec(v_a_3132_);
v_a_3211_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3211_);
lean_dec_ref(v___x_3176_);
v___y_3115_ = v___y_3125_;
v___y_3116_ = v___y_3126_;
v___y_3117_ = v___y_3127_;
v___y_3118_ = v___y_3128_;
v___y_3119_ = v___y_3129_;
v___y_3120_ = v___y_3130_;
v_a_3121_ = v_a_3211_;
goto v___jp_3114_;
}
}
}
}
else
{
lean_object* v_a_3214_; 
v_a_3214_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3214_);
lean_dec_ref(v___x_3131_);
v___y_3115_ = v___y_3125_;
v___y_3116_ = v___y_3126_;
v___y_3117_ = v___y_3127_;
v___y_3118_ = v___y_3128_;
v___y_3119_ = v___y_3129_;
v___y_3120_ = v___y_3130_;
v_a_3121_ = v_a_3214_;
goto v___jp_3114_;
}
}
v___jp_3215_:
{
if (v___y_3222_ == 0)
{
v___y_3096_ = v___y_3217_;
v___y_3097_ = v___y_3220_;
v___y_3098_ = v___y_3219_;
v___y_3099_ = v___y_3216_;
v___y_3100_ = v___y_3221_;
v___y_3101_ = v___y_3218_;
goto v___jp_3095_;
}
else
{
v___y_3125_ = v___y_3216_;
v___y_3126_ = v___y_3217_;
v___y_3127_ = v___y_3218_;
v___y_3128_ = v___y_3219_;
v___y_3129_ = v___y_3220_;
v___y_3130_ = v___y_3221_;
goto v___jp_3124_;
}
}
v___jp_3223_:
{
if (v___y_3231_ == 0)
{
lean_dec_ref(v___y_3226_);
v___y_3216_ = v___y_3224_;
v___y_3217_ = v___y_3225_;
v___y_3218_ = v___y_3227_;
v___y_3219_ = v___y_3228_;
v___y_3220_ = v___y_3229_;
v___y_3221_ = v___y_3230_;
v___y_3222_ = v___x_3050_;
goto v___jp_3215_;
}
else
{
uint8_t v___x_3232_; 
v___x_3232_ = l_Lean_Expr_hasFVar(v___y_3226_);
lean_dec_ref(v___y_3226_);
if (v___x_3232_ == 0)
{
v___y_3125_ = v___y_3224_;
v___y_3126_ = v___y_3225_;
v___y_3127_ = v___y_3227_;
v___y_3128_ = v___y_3228_;
v___y_3129_ = v___y_3229_;
v___y_3130_ = v___y_3230_;
goto v___jp_3124_;
}
else
{
v___y_3216_ = v___y_3224_;
v___y_3217_ = v___y_3225_;
v___y_3218_ = v___y_3227_;
v___y_3219_ = v___y_3228_;
v___y_3220_ = v___y_3229_;
v___y_3221_ = v___y_3230_;
v___y_3222_ = v___x_3050_;
goto v___jp_3215_;
}
}
}
v___jp_3233_:
{
lean_object* v___x_3241_; 
lean_inc_ref(v___x_3094_);
v___x_3241_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3094_, v___y_3234_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; uint8_t v___x_3243_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref(v___x_3241_);
v___x_3243_ = l_Lean_Expr_hasMVar(v_a_3242_);
if (v___x_3243_ == 0)
{
v___y_3224_ = v___y_3234_;
v___y_3225_ = v___y_3235_;
v___y_3226_ = v_a_3242_;
v___y_3227_ = v___y_3236_;
v___y_3228_ = v___y_3237_;
v___y_3229_ = v___y_3238_;
v___y_3230_ = v___y_3239_;
v___y_3231_ = v___y_3240_;
goto v___jp_3223_;
}
else
{
v___y_3224_ = v___y_3234_;
v___y_3225_ = v___y_3235_;
v___y_3226_ = v_a_3242_;
v___y_3227_ = v___y_3236_;
v___y_3228_ = v___y_3237_;
v___y_3229_ = v___y_3238_;
v___y_3230_ = v___y_3239_;
v___y_3231_ = v___x_3050_;
goto v___jp_3223_;
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec_ref(v___y_3239_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec(v___y_3234_);
lean_dec_ref(v___x_3094_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3244_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3241_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3241_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
v___jp_3252_:
{
if (v___y_3259_ == 0)
{
v___y_3096_ = v___y_3254_;
v___y_3097_ = v___y_3257_;
v___y_3098_ = v___y_3256_;
v___y_3099_ = v___y_3253_;
v___y_3100_ = v___y_3258_;
v___y_3101_ = v___y_3255_;
goto v___jp_3095_;
}
else
{
v___y_3234_ = v___y_3253_;
v___y_3235_ = v___y_3254_;
v___y_3236_ = v___y_3255_;
v___y_3237_ = v___y_3256_;
v___y_3238_ = v___y_3257_;
v___y_3239_ = v___y_3258_;
v___y_3240_ = v___y_3259_;
goto v___jp_3233_;
}
}
v___jp_3260_:
{
uint8_t v_useDecide_3267_; 
v_useDecide_3267_ = lean_ctor_get_uint8(v_config_2945_, sizeof(void*)*1);
if (v_useDecide_3267_ == 0)
{
v___y_3253_ = v___y_3264_;
v___y_3254_ = v___y_3261_;
v___y_3255_ = v___y_3266_;
v___y_3256_ = v___y_3263_;
v___y_3257_ = v_isHEq_3262_;
v___y_3258_ = v___y_3265_;
v___y_3259_ = v___x_3050_;
goto v___jp_3252_;
}
else
{
uint8_t v___x_3268_; 
v___x_3268_ = l_Lean_Expr_hasFVar(v___x_3094_);
if (v___x_3268_ == 0)
{
v___y_3234_ = v___y_3264_;
v___y_3235_ = v___y_3261_;
v___y_3236_ = v___y_3266_;
v___y_3237_ = v___y_3263_;
v___y_3238_ = v_isHEq_3262_;
v___y_3239_ = v___y_3265_;
v___y_3240_ = v_useDecide_3267_;
goto v___jp_3233_;
}
else
{
v___y_3253_ = v___y_3264_;
v___y_3254_ = v___y_3261_;
v___y_3255_ = v___y_3266_;
v___y_3256_ = v___y_3263_;
v___y_3257_ = v_isHEq_3262_;
v___y_3258_ = v___y_3265_;
v___y_3259_ = v___x_3050_;
goto v___jp_3252_;
}
}
}
v___jp_3269_:
{
lean_object* v___x_3277_; 
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3271_);
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3276_);
v___x_3277_ = l_Lean_Meta_isExprDefEq(v___y_3275_, v___y_3274_, v___y_3276_, v___y_3272_, v___y_3271_, v___y_3273_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; uint8_t v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref(v___x_3277_);
v___x_3279_ = lean_unbox(v_a_3278_);
lean_dec(v_a_3278_);
if (v___x_3279_ == 0)
{
v___y_3261_ = v___y_3270_;
v_isHEq_3262_ = v___x_2956_;
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3272_;
v___y_3265_ = v___y_3271_;
v___y_3266_ = v___y_3273_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3280_; 
lean_dec_ref(v___x_3094_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_config_2945_);
lean_inc(v_mvarId_2946_);
v___x_3280_ = l_Lean_MVarId_getType(v_mvarId_2946_, v___y_3276_, v___y_3272_, v___y_3271_, v___y_3273_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref(v___x_3280_);
v___x_3282_ = l_Lean_LocalDecl_toExpr(v_val_2977_);
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3271_);
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3276_);
v___x_3283_ = l_Lean_Meta_mkEqOfHEq(v___x_3282_, v___x_2956_, v___y_3276_, v___y_3272_, v___y_3271_, v___y_3273_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3285_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref(v___x_3283_);
lean_inc(v___y_3272_);
v___x_3285_ = l_Lean_Meta_mkNoConfusion(v_a_3281_, v_a_3284_, v___y_3276_, v___y_3272_, v___y_3271_, v___y_3273_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3285_);
v___x_3287_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2946_, v_a_3286_, v___y_3272_);
lean_dec(v___y_3272_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec_ref(v___x_3287_);
v___x_3288_ = lean_box(v___x_2956_);
v___x_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
lean_ctor_set(v___x_3290_, 1, v___x_2981_);
v_a_2963_ = v___x_3290_;
goto v___jp_2962_;
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
v_a_3291_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3287_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3287_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v___y_3272_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3299_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3285_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3285_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v_a_3281_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3307_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3283_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3283_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3315_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3280_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3280_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3315_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___x_3094_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3323_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3277_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3277_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
v___jp_3331_:
{
lean_object* v___x_3337_; 
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc(v___y_3334_);
lean_inc_ref(v___y_3333_);
lean_inc_ref(v___x_3094_);
v___x_3337_ = l_Lean_Meta_matchHEq_x3f(v___x_3094_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref(v___x_3337_);
if (lean_obj_tag(v_a_3338_) == 1)
{
lean_object* v_val_3339_; lean_object* v_snd_3340_; lean_object* v_snd_3341_; lean_object* v_fst_3342_; lean_object* v_fst_3343_; lean_object* v_fst_3344_; lean_object* v_snd_3345_; lean_object* v___x_3346_; 
v_val_3339_ = lean_ctor_get(v_a_3338_, 0);
lean_inc(v_val_3339_);
lean_dec_ref(v_a_3338_);
v_snd_3340_ = lean_ctor_get(v_val_3339_, 1);
lean_inc(v_snd_3340_);
v_snd_3341_ = lean_ctor_get(v_snd_3340_, 1);
lean_inc(v_snd_3341_);
v_fst_3342_ = lean_ctor_get(v_val_3339_, 0);
lean_inc(v_fst_3342_);
lean_dec(v_val_3339_);
v_fst_3343_ = lean_ctor_get(v_snd_3340_, 0);
lean_inc(v_fst_3343_);
lean_dec(v_snd_3340_);
v_fst_3344_ = lean_ctor_get(v_snd_3341_, 0);
lean_inc(v_fst_3344_);
v_snd_3345_ = lean_ctor_get(v_snd_3341_, 1);
lean_inc(v_snd_3345_);
lean_dec(v_snd_3341_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc(v___y_3334_);
lean_inc_ref(v___y_3333_);
v___x_3346_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3343_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref(v___x_3346_);
if (lean_obj_tag(v_a_3347_) == 1)
{
lean_object* v_val_3348_; lean_object* v___x_3349_; 
v_val_3348_ = lean_ctor_get(v_a_3347_, 0);
lean_inc(v_val_3348_);
lean_dec_ref(v_a_3347_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc(v___y_3334_);
lean_inc_ref(v___y_3333_);
v___x_3349_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3345_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref(v___x_3349_);
if (lean_obj_tag(v_a_3350_) == 1)
{
lean_object* v_toConstantVal_3351_; lean_object* v_val_3352_; lean_object* v_toConstantVal_3353_; lean_object* v_name_3354_; lean_object* v_name_3355_; uint8_t v___x_3356_; 
v_toConstantVal_3351_ = lean_ctor_get(v_val_3348_, 0);
lean_inc_ref(v_toConstantVal_3351_);
lean_dec(v_val_3348_);
v_val_3352_ = lean_ctor_get(v_a_3350_, 0);
lean_inc(v_val_3352_);
lean_dec_ref(v_a_3350_);
v_toConstantVal_3353_ = lean_ctor_get(v_val_3352_, 0);
lean_inc_ref(v_toConstantVal_3353_);
lean_dec(v_val_3352_);
v_name_3354_ = lean_ctor_get(v_toConstantVal_3351_, 0);
lean_inc(v_name_3354_);
lean_dec_ref(v_toConstantVal_3351_);
v_name_3355_ = lean_ctor_get(v_toConstantVal_3353_, 0);
lean_inc(v_name_3355_);
lean_dec_ref(v_toConstantVal_3353_);
v___x_3356_ = lean_name_eq(v_name_3354_, v_name_3355_);
lean_dec(v_name_3355_);
lean_dec(v_name_3354_);
if (v___x_3356_ == 0)
{
v___y_3270_ = v_isEq_3332_;
v___y_3271_ = v___y_3335_;
v___y_3272_ = v___y_3334_;
v___y_3273_ = v___y_3336_;
v___y_3274_ = v_fst_3344_;
v___y_3275_ = v_fst_3342_;
v___y_3276_ = v___y_3333_;
goto v___jp_3269_;
}
else
{
if (v___x_3050_ == 0)
{
lean_dec(v_fst_3344_);
lean_dec(v_fst_3342_);
v___y_3261_ = v_isEq_3332_;
v_isHEq_3262_ = v___x_2956_;
v___y_3263_ = v___y_3333_;
v___y_3264_ = v___y_3334_;
v___y_3265_ = v___y_3335_;
v___y_3266_ = v___y_3336_;
goto v___jp_3260_;
}
else
{
v___y_3270_ = v_isEq_3332_;
v___y_3271_ = v___y_3335_;
v___y_3272_ = v___y_3334_;
v___y_3273_ = v___y_3336_;
v___y_3274_ = v_fst_3344_;
v___y_3275_ = v_fst_3342_;
v___y_3276_ = v___y_3333_;
goto v___jp_3269_;
}
}
}
else
{
lean_dec(v_a_3350_);
lean_dec(v_val_3348_);
lean_dec(v_fst_3344_);
lean_dec(v_fst_3342_);
v___y_3261_ = v_isEq_3332_;
v_isHEq_3262_ = v___x_2956_;
v___y_3263_ = v___y_3333_;
v___y_3264_ = v___y_3334_;
v___y_3265_ = v___y_3335_;
v___y_3266_ = v___y_3336_;
goto v___jp_3260_;
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec(v_val_3348_);
lean_dec(v_fst_3344_);
lean_dec(v_fst_3342_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec_ref(v___x_3094_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3357_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3349_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3349_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
else
{
lean_dec(v_a_3347_);
lean_dec(v_snd_3345_);
lean_dec(v_fst_3344_);
lean_dec(v_fst_3342_);
v___y_3261_ = v_isEq_3332_;
v_isHEq_3262_ = v___x_2956_;
v___y_3263_ = v___y_3333_;
v___y_3264_ = v___y_3334_;
v___y_3265_ = v___y_3335_;
v___y_3266_ = v___y_3336_;
goto v___jp_3260_;
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_snd_3345_);
lean_dec(v_fst_3344_);
lean_dec(v_fst_3342_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec_ref(v___x_3094_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3365_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3346_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3346_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_dec(v_a_3338_);
v___y_3261_ = v_isEq_3332_;
v_isHEq_3262_ = v___x_3050_;
v___y_3263_ = v___y_3333_;
v___y_3264_ = v___y_3334_;
v___y_3265_ = v___y_3335_;
v___y_3266_ = v___y_3336_;
goto v___jp_3260_;
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec_ref(v___x_3094_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3373_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3337_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3337_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
v___jp_3381_:
{
lean_object* v___x_3386_; 
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v___y_3383_);
lean_inc_ref(v___y_3382_);
lean_inc_ref(v___x_3094_);
v___x_3386_ = l_Lean_Meta_matchEq_x3f(v___x_3094_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref(v___x_3386_);
if (lean_obj_tag(v_a_3387_) == 1)
{
lean_object* v_val_3388_; lean_object* v_snd_3389_; lean_object* v_fst_3390_; lean_object* v_snd_3391_; lean_object* v___x_3392_; 
v_val_3388_ = lean_ctor_get(v_a_3387_, 0);
lean_inc(v_val_3388_);
lean_dec_ref(v_a_3387_);
v_snd_3389_ = lean_ctor_get(v_val_3388_, 1);
lean_inc(v_snd_3389_);
lean_dec(v_val_3388_);
v_fst_3390_ = lean_ctor_get(v_snd_3389_, 0);
lean_inc(v_fst_3390_);
v_snd_3391_ = lean_ctor_get(v_snd_3389_, 1);
lean_inc(v_snd_3391_);
lean_dec(v_snd_3389_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v___y_3383_);
lean_inc_ref(v___y_3382_);
v___x_3392_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3390_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref(v___x_3392_);
if (lean_obj_tag(v_a_3393_) == 1)
{
lean_object* v_val_3394_; lean_object* v___x_3395_; 
v_val_3394_ = lean_ctor_get(v_a_3393_, 0);
lean_inc(v_val_3394_);
lean_dec_ref(v_a_3393_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v___y_3383_);
lean_inc_ref(v___y_3382_);
v___x_3395_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3391_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref(v___x_3395_);
if (lean_obj_tag(v_a_3396_) == 1)
{
lean_object* v_toConstantVal_3397_; lean_object* v_val_3398_; lean_object* v_toConstantVal_3399_; lean_object* v_name_3400_; lean_object* v_name_3401_; uint8_t v___x_3402_; 
v_toConstantVal_3397_ = lean_ctor_get(v_val_3394_, 0);
lean_inc_ref(v_toConstantVal_3397_);
lean_dec(v_val_3394_);
v_val_3398_ = lean_ctor_get(v_a_3396_, 0);
lean_inc(v_val_3398_);
lean_dec_ref(v_a_3396_);
v_toConstantVal_3399_ = lean_ctor_get(v_val_3398_, 0);
lean_inc_ref(v_toConstantVal_3399_);
lean_dec(v_val_3398_);
v_name_3400_ = lean_ctor_get(v_toConstantVal_3397_, 0);
lean_inc(v_name_3400_);
lean_dec_ref(v_toConstantVal_3397_);
v_name_3401_ = lean_ctor_get(v_toConstantVal_3399_, 0);
lean_inc(v_name_3401_);
lean_dec_ref(v_toConstantVal_3399_);
v___x_3402_ = lean_name_eq(v_name_3400_, v_name_3401_);
lean_dec(v_name_3401_);
lean_dec(v_name_3400_);
if (v___x_3402_ == 0)
{
lean_dec_ref(v___x_3094_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_config_2945_);
v___y_2983_ = v___y_3382_;
v___y_2984_ = v___y_3383_;
v___y_2985_ = v___y_3385_;
v___y_2986_ = v___y_3384_;
goto v___jp_2982_;
}
else
{
if (v___x_3050_ == 0)
{
lean_del_object(v___x_2979_);
v_isEq_3332_ = v___x_2956_;
v___y_3333_ = v___y_3382_;
v___y_3334_ = v___y_3383_;
v___y_3335_ = v___y_3384_;
v___y_3336_ = v___y_3385_;
goto v___jp_3331_;
}
else
{
lean_dec_ref(v___x_3094_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_config_2945_);
v___y_2983_ = v___y_3382_;
v___y_2984_ = v___y_3383_;
v___y_2985_ = v___y_3385_;
v___y_2986_ = v___y_3384_;
goto v___jp_2982_;
}
}
}
else
{
lean_dec(v_a_3396_);
lean_dec(v_val_3394_);
lean_del_object(v___x_2979_);
v_isEq_3332_ = v___x_2956_;
v___y_3333_ = v___y_3382_;
v___y_3334_ = v___y_3383_;
v___y_3335_ = v___y_3384_;
v___y_3336_ = v___y_3385_;
goto v___jp_3331_;
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_val_3394_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3403_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3395_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3395_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_dec(v_a_3393_);
lean_dec(v_snd_3391_);
lean_del_object(v___x_2979_);
v_isEq_3332_ = v___x_2956_;
v___y_3333_ = v___y_3382_;
v___y_3334_ = v___y_3383_;
v___y_3335_ = v___y_3384_;
v___y_3336_ = v___y_3385_;
goto v___jp_3331_;
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_snd_3391_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3411_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3392_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3392_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
else
{
lean_dec(v_a_3387_);
lean_del_object(v___x_2979_);
v_isEq_3332_ = v___x_3050_;
v___y_3333_ = v___y_3382_;
v___y_3334_ = v___y_3383_;
v___y_3335_ = v___y_3384_;
v___y_3336_ = v___y_3385_;
goto v___jp_3331_;
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3419_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3386_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3386_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
v___jp_3427_:
{
lean_object* v___x_3432_; 
lean_inc(v___y_3431_);
lean_inc_ref(v___y_3430_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc_ref(v___x_3094_);
v___x_3432_ = l_refutableHasNotBit_x3f(v___x_3094_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref(v___x_3432_);
if (lean_obj_tag(v_a_3433_) == 1)
{
lean_object* v_val_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3473_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_config_2945_);
v_val_3434_ = lean_ctor_get(v_a_3433_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_a_3433_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3436_ = v_a_3433_;
v_isShared_3437_ = v_isSharedCheck_3473_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_val_3434_);
lean_dec(v_a_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3473_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; 
lean_inc(v_mvarId_2946_);
v___x_3438_ = l_Lean_MVarId_getType(v_mvarId_2946_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref(v___x_3438_);
v___x_3440_ = l_Lean_LocalDecl_toExpr(v_val_2977_);
lean_inc(v___y_3429_);
v___x_3441_ = l_Lean_Meta_mkAbsurd(v_a_3439_, v_val_3434_, v___x_3440_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v___x_3443_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2946_, v_a_3442_, v___y_3429_);
lean_dec(v___y_3429_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_dec_ref(v___x_3443_);
v___x_3444_ = lean_box(v___x_2956_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3444_);
v___x_3446_ = v___x_3436_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
lean_ctor_set(v___x_3447_, 1, v___x_2981_);
v_a_2963_ = v___x_3447_;
goto v___jp_2962_;
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_del_object(v___x_3436_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
v_a_3449_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3443_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3443_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_del_object(v___x_3436_);
lean_dec(v___y_3429_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3457_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3441_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3441_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_del_object(v___x_3436_);
lean_dec(v_val_3434_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3465_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3438_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3438_);
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
lean_object* v___x_3474_; 
lean_dec(v_a_3433_);
lean_inc(v___y_3431_);
lean_inc_ref(v___y_3430_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc_ref(v___x_3094_);
v___x_3474_ = l_Lean_Meta_matchNe_x3f(v___x_3094_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref(v___x_3474_);
if (lean_obj_tag(v_a_3475_) == 1)
{
lean_object* v_val_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3545_; 
v_val_3476_ = lean_ctor_get(v_a_3475_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_a_3475_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3478_ = v_a_3475_;
v_isShared_3479_ = v_isSharedCheck_3545_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_val_3476_);
lean_dec(v_a_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3545_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v_snd_3480_; lean_object* v_fst_3481_; lean_object* v_snd_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3544_; 
v_snd_3480_ = lean_ctor_get(v_val_3476_, 1);
lean_inc(v_snd_3480_);
lean_dec(v_val_3476_);
v_fst_3481_ = lean_ctor_get(v_snd_3480_, 0);
v_snd_3482_ = lean_ctor_get(v_snd_3480_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_snd_3480_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3484_ = v_snd_3480_;
v_isShared_3485_ = v_isSharedCheck_3544_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_snd_3482_);
lean_inc(v_fst_3481_);
lean_dec(v_snd_3480_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3544_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; 
lean_inc(v___y_3431_);
lean_inc_ref(v___y_3430_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc(v_fst_3481_);
v___x_3486_ = l_Lean_Meta_isExprDefEq(v_fst_3481_, v_snd_3482_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; uint8_t v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref(v___x_3486_);
v___x_3488_ = lean_unbox(v_a_3487_);
lean_dec(v_a_3487_);
if (v___x_3488_ == 0)
{
lean_del_object(v___x_3484_);
lean_dec(v_fst_3481_);
lean_del_object(v___x_3478_);
v___y_3382_ = v___y_3428_;
v___y_3383_ = v___y_3429_;
v___y_3384_ = v___y_3430_;
v___y_3385_ = v___y_3431_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3489_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_config_2945_);
lean_inc(v_mvarId_2946_);
v___x_3489_ = l_Lean_MVarId_getType(v_mvarId_2946_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref(v___x_3489_);
lean_inc(v___y_3431_);
lean_inc_ref(v___y_3430_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
v___x_3491_ = l_Lean_Meta_mkEqRefl(v_fst_3481_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref(v___x_3491_);
v___x_3493_ = l_Lean_LocalDecl_toExpr(v_val_2977_);
lean_inc(v___y_3429_);
v___x_3494_ = l_Lean_Meta_mkAbsurd(v_a_3490_, v_a_3492_, v___x_3493_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3496_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref(v___x_3494_);
v___x_3496_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2946_, v_a_3495_, v___y_3429_);
lean_dec(v___y_3429_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v___x_3497_; lean_object* v___x_3499_; 
lean_dec_ref(v___x_3496_);
v___x_3497_ = lean_box(v___x_2956_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3497_);
v___x_3499_ = v___x_3478_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3501_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 1, v___x_2981_);
lean_ctor_set(v___x_3484_, 0, v___x_3499_);
v___x_3501_ = v___x_3484_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_2981_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
v_a_2963_ = v___x_3501_;
goto v___jp_2962_;
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_del_object(v___x_3484_);
lean_del_object(v___x_3478_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
v_a_3504_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3496_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3496_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_del_object(v___x_3484_);
lean_del_object(v___x_3478_);
lean_dec(v___y_3429_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3512_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3494_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3494_);
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
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec(v_a_3490_);
lean_del_object(v___x_3484_);
lean_del_object(v___x_3478_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3520_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3491_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3491_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_del_object(v___x_3484_);
lean_dec(v_fst_3481_);
lean_del_object(v___x_3478_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3528_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3489_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3489_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_del_object(v___x_3484_);
lean_dec(v_fst_3481_);
lean_del_object(v___x_3478_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3536_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3486_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3486_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3475_);
v___y_3382_ = v___y_3428_;
v___y_3383_ = v___y_3429_;
v___y_3384_ = v___y_3430_;
v___y_3385_ = v___y_3431_;
goto v___jp_3381_;
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3546_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3474_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3474_);
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
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3554_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3432_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3432_);
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
}
else
{
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
v_a_2971_ = v___x_3022_;
goto v___jp_2970_;
}
v___jp_2982_:
{
lean_object* v___x_2987_; 
lean_inc(v_mvarId_2946_);
v___x_2987_ = l_Lean_MVarId_getType(v_mvarId_2946_, v___y_2983_, v___y_2984_, v___y_2986_, v___y_2985_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref(v___x_2987_);
v___x_2989_ = l_Lean_LocalDecl_toExpr(v_val_2977_);
lean_inc(v___y_2984_);
v___x_2990_ = l_Lean_Meta_mkNoConfusion(v_a_2988_, v___x_2989_, v___y_2983_, v___y_2984_, v___y_2986_, v___y_2985_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v___x_2990_);
v___x_2992_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2946_, v_a_2991_, v___y_2984_);
lean_dec(v___y_2984_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
lean_dec_ref(v___x_2992_);
v___x_2993_ = lean_box(v___x_2956_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v___x_2993_);
v___x_2995_ = v___x_2979_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
lean_ctor_set(v___x_2996_, 1, v___x_2981_);
v_a_2963_ = v___x_2996_;
goto v___jp_2962_;
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_del_object(v___x_2979_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
v_a_2998_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2992_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2992_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v___y_2984_);
lean_del_object(v___x_2979_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3006_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2990_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2990_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_del_object(v___x_2979_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v_mvarId_2946_);
v_a_3014_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2987_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2987_);
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
v___jp_3023_:
{
lean_object* v_searchFuel_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_searchFuel_3028_ = lean_ctor_get(v_config_2945_, 0);
v___x_3029_ = l_Lean_LocalDecl_fvarId(v_val_2977_);
lean_dec(v_val_2977_);
lean_inc(v_searchFuel_3028_);
lean_inc(v_mvarId_2946_);
v___x_3030_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2946_, v___x_3029_, v_searchFuel_3028_, v___y_3025_, v___y_3024_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; uint8_t v___x_3032_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref(v___x_3030_);
v___x_3032_ = lean_unbox(v_a_3031_);
lean_dec(v_a_3031_);
if (v___x_3032_ == 0)
{
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
v_a_2971_ = v___x_3022_;
goto v___jp_2970_;
}
else
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v___x_3033_ = lean_box(v___x_2956_);
v___x_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
v___x_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v___x_2981_);
v_a_2963_ = v___x_3035_;
goto v___jp_2962_;
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3036_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3030_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3030_);
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
v___jp_3044_:
{
if (v___y_3049_ == 0)
{
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
v_a_2971_ = v___x_3022_;
goto v___jp_2970_;
}
else
{
v___y_3024_ = v___y_3045_;
v___y_3025_ = v___y_3046_;
v___y_3026_ = v___y_3047_;
v___y_3027_ = v___y_3048_;
goto v___jp_3023_;
}
}
v___jp_3051_:
{
if (v___y_3053_ == 0)
{
v___y_3024_ = v___y_3052_;
v___y_3025_ = v___y_3054_;
v___y_3026_ = v___y_3055_;
v___y_3027_ = v___y_3056_;
goto v___jp_3023_;
}
else
{
v___y_3045_ = v___y_3052_;
v___y_3046_ = v___y_3054_;
v___y_3047_ = v___y_3055_;
v___y_3048_ = v___y_3056_;
v___y_3049_ = v___x_3050_;
goto v___jp_3044_;
}
}
v___jp_3057_:
{
if (v___y_3063_ == 0)
{
v___y_3045_ = v___y_3058_;
v___y_3046_ = v___y_3060_;
v___y_3047_ = v___y_3061_;
v___y_3048_ = v___y_3062_;
v___y_3049_ = v___x_3050_;
goto v___jp_3044_;
}
else
{
v___y_3052_ = v___y_3058_;
v___y_3053_ = v___y_3059_;
v___y_3054_ = v___y_3060_;
v___y_3055_ = v___y_3061_;
v___y_3056_ = v___y_3062_;
goto v___jp_3051_;
}
}
v___jp_3064_:
{
uint8_t v_emptyType_3071_; 
v_emptyType_3071_ = lean_ctor_get_uint8(v_config_2945_, sizeof(void*)*1 + 1);
if (v_emptyType_3071_ == 0)
{
v___y_3058_ = v___y_3068_;
v___y_3059_ = v___y_3066_;
v___y_3060_ = v___y_3067_;
v___y_3061_ = v___y_3069_;
v___y_3062_ = v___y_3070_;
v___y_3063_ = v___x_3050_;
goto v___jp_3057_;
}
else
{
if (v___y_3065_ == 0)
{
v___y_3052_ = v___y_3068_;
v___y_3053_ = v___y_3066_;
v___y_3054_ = v___y_3067_;
v___y_3055_ = v___y_3069_;
v___y_3056_ = v___y_3070_;
goto v___jp_3051_;
}
else
{
v___y_3058_ = v___y_3068_;
v___y_3059_ = v___y_3066_;
v___y_3060_ = v___y_3067_;
v___y_3061_ = v___y_3069_;
v___y_3062_ = v___y_3070_;
v___y_3063_ = v___x_3050_;
goto v___jp_3057_;
}
}
}
v___jp_3072_:
{
if (v___y_3079_ == 0)
{
v___y_3065_ = v___y_3074_;
v___y_3066_ = v___y_3075_;
v___y_3067_ = v___y_3078_;
v___y_3068_ = v___y_3073_;
v___y_3069_ = v___y_3076_;
v___y_3070_ = v___y_3077_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3080_; 
lean_inc(v___y_3077_);
lean_inc_ref(v___y_3076_);
lean_inc(v___y_3073_);
lean_inc_ref(v___y_3078_);
lean_inc(v_val_2977_);
lean_inc(v_mvarId_2946_);
v___x_3080_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2946_, v_val_2977_, v___y_3078_, v___y_3073_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; uint8_t v___x_3082_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref(v___x_3080_);
v___x_3082_ = lean_unbox(v_a_3081_);
lean_dec(v_a_3081_);
if (v___x_3082_ == 0)
{
v___y_3065_ = v___y_3074_;
v___y_3066_ = v___y_3075_;
v___y_3067_ = v___y_3078_;
v___y_3068_ = v___y_3073_;
v___y_3069_ = v___y_3076_;
v___y_3070_ = v___y_3077_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3073_);
lean_dec(v_val_2977_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v___x_3083_ = lean_box(v___x_2956_);
v___x_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v___x_2981_);
v_a_2963_ = v___x_3085_;
goto v___jp_2962_;
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3073_);
lean_dec(v_val_2977_);
lean_del_object(v___x_2960_);
lean_dec(v_snd_2958_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v_mvarId_2946_);
lean_dec_ref(v_config_2945_);
v_a_3086_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3080_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3080_);
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
}
}
v___jp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2964_, 0, v_a_2963_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2964_);
v___x_2966_ = v___x_2960_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_snd_2958_);
v___x_2966_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
return v___x_2967_;
}
}
v___jp_2970_:
{
lean_object* v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2969_);
lean_ctor_set(v___x_2972_, 1, v_a_2971_);
v___x_2973_ = ((size_t)1ULL);
v___x_2974_ = lean_usize_add(v_i_2949_, v___x_2973_);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2945_, v_mvarId_2946_, v_as_2947_, v_sz_2948_, v___x_2974_, v___x_2972_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
return v___x_2975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3628_, lean_object* v_mvarId_3629_, lean_object* v_as_3630_, lean_object* v_sz_3631_, lean_object* v_i_3632_, lean_object* v_b_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
size_t v_sz_boxed_3639_; size_t v_i_boxed_3640_; lean_object* v_res_3641_; 
v_sz_boxed_3639_ = lean_unbox_usize(v_sz_3631_);
lean_dec(v_sz_3631_);
v_i_boxed_3640_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3628_, v_mvarId_3629_, v_as_3630_, v_sz_boxed_3639_, v_i_boxed_3640_, v_b_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec_ref(v_as_3630_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3645_, lean_object* v_mvarId_3646_, lean_object* v_as_3647_, size_t v_sz_3648_, size_t v_i_3649_, lean_object* v_b_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
uint8_t v___x_3656_; 
v___x_3656_ = lean_usize_dec_lt(v_i_3649_, v_sz_3648_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; 
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v___x_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3657_, 0, v_b_3650_);
return v___x_3657_;
}
else
{
lean_object* v_snd_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_4346_; 
v_snd_3658_ = lean_ctor_get(v_b_3650_, 1);
v_isSharedCheck_4346_ = !lean_is_exclusive(v_b_3650_);
if (v_isSharedCheck_4346_ == 0)
{
lean_object* v_unused_4347_; 
v_unused_4347_ = lean_ctor_get(v_b_3650_, 0);
lean_dec(v_unused_4347_);
v___x_3660_ = v_b_3650_;
v_isShared_3661_ = v_isSharedCheck_4346_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_snd_3658_);
lean_dec(v_b_3650_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_4346_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v_a_3663_; lean_object* v___x_3669_; lean_object* v_a_3671_; lean_object* v_a_3676_; 
v___x_3669_ = lean_box(0);
v_a_3676_ = lean_array_uget(v_as_3647_, v_i_3649_);
if (lean_obj_tag(v_a_3676_) == 0)
{
lean_del_object(v___x_3660_);
v_a_3671_ = v_snd_3658_;
goto v___jp_3670_;
}
else
{
lean_object* v_val_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_4345_; 
v_val_3677_ = lean_ctor_get(v_a_3676_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v_a_3676_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_3679_ = v_a_3676_;
v_isShared_3680_ = v_isSharedCheck_4345_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_val_3677_);
lean_dec(v_a_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_4345_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___x_3723_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; uint8_t v___y_3751_; uint8_t v___x_3752_; uint8_t v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; uint8_t v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; uint8_t v___y_3765_; uint8_t v___y_3767_; uint8_t v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3775_; uint8_t v___y_3776_; lean_object* v___y_3777_; uint8_t v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; uint8_t v___y_3781_; 
v___x_3681_ = lean_box(0);
v___x_3723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3752_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3677_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3797_; uint8_t v___y_3799_; uint8_t v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; uint8_t v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; uint8_t v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; uint8_t v___y_3815_; uint8_t v___y_3818_; lean_object* v___y_3819_; uint8_t v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v_a_3824_; uint8_t v___y_3828_; lean_object* v___y_3829_; uint8_t v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; uint8_t v___y_3926_; lean_object* v___y_3927_; uint8_t v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; uint8_t v___y_3932_; uint8_t v___y_3934_; lean_object* v___y_3935_; uint8_t v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; uint8_t v___y_3941_; uint8_t v___y_3944_; lean_object* v___y_3945_; uint8_t v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; uint8_t v___y_3950_; uint8_t v___y_3963_; lean_object* v___y_3964_; uint8_t v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; uint8_t v___y_3969_; uint8_t v___y_3971_; uint8_t v_isHEq_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; uint8_t v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; uint8_t v_isEq_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___x_4275_; 
v___x_3797_ = l_Lean_LocalDecl_type(v_val_3677_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3651_);
lean_inc_ref(v___x_3797_);
v___x_4275_ = l_Lean_Meta_matchNot_x3f(v___x_3797_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref(v___x_4275_);
if (lean_obj_tag(v_a_4276_) == 1)
{
lean_object* v_val_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4336_; 
v_val_4277_ = lean_ctor_get(v_a_4276_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v_a_4276_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4279_ = v_a_4276_;
v_isShared_4280_ = v_isSharedCheck_4336_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_val_4277_);
lean_dec(v_a_4276_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4336_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4281_; 
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3651_);
v___x_4281_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4277_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_a_4282_);
lean_dec_ref(v___x_4281_);
if (lean_obj_tag(v_a_4282_) == 1)
{
lean_object* v_val_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec_ref(v_config_3645_);
v_val_4283_ = lean_ctor_get(v_a_4282_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_a_4282_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4285_ = v_a_4282_;
v_isShared_4286_ = v_isSharedCheck_4327_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_val_4283_);
lean_dec(v_a_4282_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4327_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4287_; 
lean_inc(v_mvarId_3646_);
v___x_4287_ = l_Lean_MVarId_getType(v_mvarId_3646_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref(v___x_4287_);
v___x_4289_ = l_Lean_LocalDecl_toExpr(v_val_3677_);
v___x_4290_ = l_Lean_mkFVar(v_val_4283_);
v___x_4291_ = l_Lean_Expr_app___override(v___x_4289_, v___x_4290_);
lean_inc(v___y_3652_);
v___x_4292_ = l_Lean_Meta_mkFalseElim(v_a_4288_, v___x_4291_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4294_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4293_);
lean_dec_ref(v___x_4292_);
v___x_4294_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3646_, v_a_4293_, v___y_3652_);
lean_dec(v___y_3652_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4297_; 
lean_dec_ref(v___x_4294_);
v___x_4295_ = lean_box(v___x_3656_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 0, v___x_4295_);
v___x_4297_ = v___x_4285_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4298_; lean_object* v___x_4300_; 
v___x_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
lean_ctor_set(v___x_4298_, 1, v___x_3681_);
if (v_isShared_4280_ == 0)
{
lean_ctor_set_tag(v___x_4279_, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4298_);
v___x_4300_ = v___x_4279_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v___x_4298_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
v_a_3663_ = v___x_4300_;
goto v___jp_3662_;
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
lean_del_object(v___x_4285_);
lean_del_object(v___x_4279_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
v_a_4303_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4294_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4294_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
lean_del_object(v___x_4285_);
lean_del_object(v___x_4279_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3652_);
lean_dec(v_mvarId_3646_);
v_a_4311_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4292_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4292_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_del_object(v___x_4285_);
lean_dec(v_val_4283_);
lean_del_object(v___x_4279_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
v_a_4319_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4287_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4287_);
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
}
else
{
lean_dec(v_a_4282_);
lean_del_object(v___x_4279_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3651_);
v___y_4139_ = v___y_3651_;
v___y_4140_ = v___y_3652_;
v___y_4141_ = v___y_3653_;
v___y_4142_ = v___y_3654_;
goto v___jp_4138_;
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_del_object(v___x_4279_);
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4328_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4281_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4281_);
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
}
else
{
lean_dec(v_a_4276_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3651_);
v___y_4139_ = v___y_3651_;
v___y_4140_ = v___y_3652_;
v___y_4141_ = v___y_3653_;
v___y_4142_ = v___y_3654_;
goto v___jp_4138_;
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4337_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4275_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4275_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
v___jp_3798_:
{
uint8_t v_genDiseq_3805_; 
v_genDiseq_3805_ = lean_ctor_get_uint8(v_config_3645_, sizeof(void*)*1 + 2);
if (v_genDiseq_3805_ == 0)
{
lean_dec_ref(v___x_3797_);
v___y_3775_ = v___y_3802_;
v___y_3776_ = v___y_3799_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3800_;
v___y_3779_ = v___y_3804_;
v___y_3780_ = v___y_3801_;
v___y_3781_ = v___x_3752_;
goto v___jp_3774_;
}
else
{
uint8_t v___x_3806_; 
v___x_3806_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3797_);
v___y_3775_ = v___y_3802_;
v___y_3776_ = v___y_3799_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3800_;
v___y_3779_ = v___y_3804_;
v___y_3780_ = v___y_3801_;
v___y_3781_ = v___x_3806_;
goto v___jp_3774_;
}
}
v___jp_3807_:
{
if (v___y_3815_ == 0)
{
lean_dec_ref(v___y_3809_);
v___y_3799_ = v___y_3808_;
v___y_3800_ = v___y_3811_;
v___y_3801_ = v___y_3810_;
v___y_3802_ = v___y_3812_;
v___y_3803_ = v___y_3813_;
v___y_3804_ = v___y_3814_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3816_; 
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3810_);
lean_dec_ref(v___x_3797_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___y_3809_);
return v___x_3816_;
}
}
v___jp_3817_:
{
uint8_t v___x_3825_; 
v___x_3825_ = l_Lean_Exception_isInterrupt(v_a_3824_);
if (v___x_3825_ == 0)
{
uint8_t v___x_3826_; 
lean_inc_ref(v_a_3824_);
v___x_3826_ = l_Lean_Exception_isRuntime(v_a_3824_);
v___y_3808_ = v___y_3818_;
v___y_3809_ = v_a_3824_;
v___y_3810_ = v___y_3819_;
v___y_3811_ = v___y_3820_;
v___y_3812_ = v___y_3821_;
v___y_3813_ = v___y_3822_;
v___y_3814_ = v___y_3823_;
v___y_3815_ = v___x_3826_;
goto v___jp_3807_;
}
else
{
v___y_3808_ = v___y_3818_;
v___y_3809_ = v_a_3824_;
v___y_3810_ = v___y_3819_;
v___y_3811_ = v___y_3820_;
v___y_3812_ = v___y_3821_;
v___y_3813_ = v___y_3822_;
v___y_3814_ = v___y_3823_;
v___y_3815_ = v___x_3825_;
goto v___jp_3807_;
}
}
v___jp_3827_:
{
lean_object* v___x_3834_; 
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
lean_inc(v___y_3831_);
lean_inc_ref(v___y_3829_);
lean_inc_ref(v___x_3797_);
v___x_3834_ = l_Lean_Meta_mkDecide(v___x_3797_, v___y_3829_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3836_; uint8_t v_foApprox_3837_; uint8_t v_ctxApprox_3838_; uint8_t v_quasiPatternApprox_3839_; uint8_t v_constApprox_3840_; uint8_t v_isDefEqStuckEx_3841_; uint8_t v_unificationHints_3842_; uint8_t v_proofIrrelevance_3843_; uint8_t v_assignSyntheticOpaque_3844_; uint8_t v_offsetCnstrs_3845_; uint8_t v_etaStruct_3846_; uint8_t v_univApprox_3847_; uint8_t v_iota_3848_; uint8_t v_beta_3849_; uint8_t v_proj_3850_; uint8_t v_zeta_3851_; uint8_t v_zetaDelta_3852_; uint8_t v_zetaUnused_3853_; uint8_t v_zetaHave_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3923_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref(v___x_3834_);
v___x_3836_ = l_Lean_Meta_Context_config(v___y_3829_);
v_foApprox_3837_ = lean_ctor_get_uint8(v___x_3836_, 0);
v_ctxApprox_3838_ = lean_ctor_get_uint8(v___x_3836_, 1);
v_quasiPatternApprox_3839_ = lean_ctor_get_uint8(v___x_3836_, 2);
v_constApprox_3840_ = lean_ctor_get_uint8(v___x_3836_, 3);
v_isDefEqStuckEx_3841_ = lean_ctor_get_uint8(v___x_3836_, 4);
v_unificationHints_3842_ = lean_ctor_get_uint8(v___x_3836_, 5);
v_proofIrrelevance_3843_ = lean_ctor_get_uint8(v___x_3836_, 6);
v_assignSyntheticOpaque_3844_ = lean_ctor_get_uint8(v___x_3836_, 7);
v_offsetCnstrs_3845_ = lean_ctor_get_uint8(v___x_3836_, 8);
v_etaStruct_3846_ = lean_ctor_get_uint8(v___x_3836_, 10);
v_univApprox_3847_ = lean_ctor_get_uint8(v___x_3836_, 11);
v_iota_3848_ = lean_ctor_get_uint8(v___x_3836_, 12);
v_beta_3849_ = lean_ctor_get_uint8(v___x_3836_, 13);
v_proj_3850_ = lean_ctor_get_uint8(v___x_3836_, 14);
v_zeta_3851_ = lean_ctor_get_uint8(v___x_3836_, 15);
v_zetaDelta_3852_ = lean_ctor_get_uint8(v___x_3836_, 16);
v_zetaUnused_3853_ = lean_ctor_get_uint8(v___x_3836_, 17);
v_zetaHave_3854_ = lean_ctor_get_uint8(v___x_3836_, 18);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3856_ = v___x_3836_;
v_isShared_3857_ = v_isSharedCheck_3923_;
goto v_resetjp_3855_;
}
else
{
lean_dec(v___x_3836_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3923_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
uint8_t v_trackZetaDelta_3858_; lean_object* v_zetaDeltaSet_3859_; lean_object* v_lctx_3860_; lean_object* v_localInstances_3861_; lean_object* v_defEqCtx_x3f_3862_; lean_object* v_synthPendingDepth_3863_; lean_object* v_canUnfold_x3f_3864_; uint8_t v_univApprox_3865_; uint8_t v_inTypeClassResolution_3866_; uint8_t v_cacheInferType_3867_; uint8_t v___x_3868_; lean_object* v_config_3870_; 
v_trackZetaDelta_3858_ = lean_ctor_get_uint8(v___y_3829_, sizeof(void*)*7);
v_zetaDeltaSet_3859_ = lean_ctor_get(v___y_3829_, 1);
v_lctx_3860_ = lean_ctor_get(v___y_3829_, 2);
v_localInstances_3861_ = lean_ctor_get(v___y_3829_, 3);
v_defEqCtx_x3f_3862_ = lean_ctor_get(v___y_3829_, 4);
v_synthPendingDepth_3863_ = lean_ctor_get(v___y_3829_, 5);
v_canUnfold_x3f_3864_ = lean_ctor_get(v___y_3829_, 6);
v_univApprox_3865_ = lean_ctor_get_uint8(v___y_3829_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3866_ = lean_ctor_get_uint8(v___y_3829_, sizeof(void*)*7 + 2);
v_cacheInferType_3867_ = lean_ctor_get_uint8(v___y_3829_, sizeof(void*)*7 + 3);
v___x_3868_ = 1;
if (v_isShared_3857_ == 0)
{
v_config_3870_ = v___x_3856_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 0, v_foApprox_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 1, v_ctxApprox_3838_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 2, v_quasiPatternApprox_3839_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 3, v_constApprox_3840_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 4, v_isDefEqStuckEx_3841_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 5, v_unificationHints_3842_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 6, v_proofIrrelevance_3843_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 7, v_assignSyntheticOpaque_3844_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 8, v_offsetCnstrs_3845_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 10, v_etaStruct_3846_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 11, v_univApprox_3847_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 12, v_iota_3848_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 13, v_beta_3849_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 14, v_proj_3850_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 15, v_zeta_3851_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 16, v_zetaDelta_3852_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 17, v_zetaUnused_3853_);
lean_ctor_set_uint8(v_reuseFailAlloc_3922_, 18, v_zetaHave_3854_);
v_config_3870_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
uint64_t v___x_3871_; uint64_t v___x_3872_; uint64_t v___x_3873_; uint64_t v___x_3874_; uint64_t v___x_3875_; uint64_t v_key_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_ctor_set_uint8(v_config_3870_, 9, v___x_3868_);
v___x_3871_ = l_Lean_Meta_Context_configKey(v___y_3829_);
v___x_3872_ = 2ULL;
v___x_3873_ = lean_uint64_shift_right(v___x_3871_, v___x_3872_);
v___x_3874_ = lean_uint64_shift_left(v___x_3873_, v___x_3872_);
v___x_3875_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_3876_ = lean_uint64_lor(v___x_3874_, v___x_3875_);
v___x_3877_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3877_, 0, v_config_3870_);
lean_ctor_set_uint64(v___x_3877_, sizeof(void*)*1, v_key_3876_);
lean_inc(v_canUnfold_x3f_3864_);
lean_inc(v_synthPendingDepth_3863_);
lean_inc(v_defEqCtx_x3f_3862_);
lean_inc_ref(v_localInstances_3861_);
lean_inc_ref(v_lctx_3860_);
lean_inc(v_zetaDeltaSet_3859_);
v___x_3878_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
lean_ctor_set(v___x_3878_, 1, v_zetaDeltaSet_3859_);
lean_ctor_set(v___x_3878_, 2, v_lctx_3860_);
lean_ctor_set(v___x_3878_, 3, v_localInstances_3861_);
lean_ctor_set(v___x_3878_, 4, v_defEqCtx_x3f_3862_);
lean_ctor_set(v___x_3878_, 5, v_synthPendingDepth_3863_);
lean_ctor_set(v___x_3878_, 6, v_canUnfold_x3f_3864_);
lean_ctor_set_uint8(v___x_3878_, sizeof(void*)*7, v_trackZetaDelta_3858_);
lean_ctor_set_uint8(v___x_3878_, sizeof(void*)*7 + 1, v_univApprox_3865_);
lean_ctor_set_uint8(v___x_3878_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3866_);
lean_ctor_set_uint8(v___x_3878_, sizeof(void*)*7 + 3, v_cacheInferType_3867_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
lean_inc(v___y_3831_);
lean_inc(v_a_3835_);
v___x_3879_ = lean_whnf(v_a_3835_, v___x_3878_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref(v___x_3879_);
v___x_3881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_3882_ = l_Lean_Expr_isConstOf(v_a_3880_, v___x_3881_);
lean_dec(v_a_3880_);
if (v___x_3882_ == 0)
{
lean_dec(v_a_3835_);
v___y_3799_ = v___y_3828_;
v___y_3800_ = v___y_3830_;
v___y_3801_ = v___y_3829_;
v___y_3802_ = v___y_3831_;
v___y_3803_ = v___y_3832_;
v___y_3804_ = v___y_3833_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3883_; 
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
lean_inc(v___y_3831_);
lean_inc_ref(v___y_3829_);
lean_inc(v_a_3835_);
v___x_3883_ = l_Lean_Meta_mkEqRefl(v_a_3835_, v___y_3829_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref(v___x_3883_);
lean_inc(v_mvarId_3646_);
v___x_3885_ = l_Lean_MVarId_getType(v_mvarId_3646_, v___y_3829_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v_nargs_3887_; lean_object* v___x_3888_; lean_object* v_dummy_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref(v___x_3885_);
v_nargs_3887_ = l_Lean_Expr_getAppNumArgs(v_a_3835_);
v___x_3888_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_3889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_3887_);
v___x_3890_ = lean_mk_array(v_nargs_3887_, v_dummy_3889_);
v___x_3891_ = lean_unsigned_to_nat(1u);
v___x_3892_ = lean_nat_sub(v_nargs_3887_, v___x_3891_);
lean_dec(v_nargs_3887_);
v___x_3893_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3835_, v___x_3890_, v___x_3892_);
v___x_3894_ = lean_array_push(v___x_3893_, v_a_3884_);
v___x_3895_ = l_Lean_mkAppN(v___x_3888_, v___x_3894_);
lean_dec_ref(v___x_3894_);
lean_inc(v_val_3677_);
v___x_3896_ = l_Lean_LocalDecl_toExpr(v_val_3677_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
lean_inc(v___y_3831_);
lean_inc_ref(v___y_3829_);
v___x_3897_ = l_Lean_Meta_mkAbsurd(v_a_3886_, v___x_3896_, v___x_3895_, v___y_3829_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3917_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3917_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3917_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; 
lean_inc(v_mvarId_3646_);
v___x_3902_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3646_, v_a_3898_, v___y_3831_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3829_);
lean_dec_ref(v___x_3797_);
lean_dec(v_val_3677_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; 
v_unused_3915_ = lean_ctor_get(v___x_3902_, 0);
lean_dec(v_unused_3915_);
v___x_3904_ = v___x_3902_;
v_isShared_3905_ = v_isSharedCheck_3914_;
goto v_resetjp_3903_;
}
else
{
lean_dec(v___x_3902_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3914_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3906_ = lean_box(v___x_3656_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set_tag(v___x_3904_, 1);
lean_ctor_set(v___x_3904_, 0, v___x_3906_);
v___x_3908_ = v___x_3904_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
lean_ctor_set(v___x_3909_, 1, v___x_3681_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3909_);
v___x_3911_ = v___x_3900_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
v_a_3663_ = v___x_3911_;
goto v___jp_3662_;
}
}
}
}
else
{
lean_object* v_a_3916_; 
lean_del_object(v___x_3900_);
v_a_3916_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v___x_3902_);
v___y_3818_ = v___y_3828_;
v___y_3819_ = v___y_3829_;
v___y_3820_ = v___y_3830_;
v___y_3821_ = v___y_3831_;
v___y_3822_ = v___y_3832_;
v___y_3823_ = v___y_3833_;
v_a_3824_ = v_a_3916_;
goto v___jp_3817_;
}
}
}
else
{
lean_object* v_a_3918_; 
v_a_3918_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3918_);
lean_dec_ref(v___x_3897_);
v___y_3818_ = v___y_3828_;
v___y_3819_ = v___y_3829_;
v___y_3820_ = v___y_3830_;
v___y_3821_ = v___y_3831_;
v___y_3822_ = v___y_3832_;
v___y_3823_ = v___y_3833_;
v_a_3824_ = v_a_3918_;
goto v___jp_3817_;
}
}
else
{
lean_object* v_a_3919_; 
lean_dec(v_a_3884_);
lean_dec(v_a_3835_);
v_a_3919_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3919_);
lean_dec_ref(v___x_3885_);
v___y_3818_ = v___y_3828_;
v___y_3819_ = v___y_3829_;
v___y_3820_ = v___y_3830_;
v___y_3821_ = v___y_3831_;
v___y_3822_ = v___y_3832_;
v___y_3823_ = v___y_3833_;
v_a_3824_ = v_a_3919_;
goto v___jp_3817_;
}
}
else
{
lean_object* v_a_3920_; 
lean_dec(v_a_3835_);
v_a_3920_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3920_);
lean_dec_ref(v___x_3883_);
v___y_3818_ = v___y_3828_;
v___y_3819_ = v___y_3829_;
v___y_3820_ = v___y_3830_;
v___y_3821_ = v___y_3831_;
v___y_3822_ = v___y_3832_;
v___y_3823_ = v___y_3833_;
v_a_3824_ = v_a_3920_;
goto v___jp_3817_;
}
}
}
else
{
lean_object* v_a_3921_; 
lean_dec(v_a_3835_);
v_a_3921_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3921_);
lean_dec_ref(v___x_3879_);
v___y_3818_ = v___y_3828_;
v___y_3819_ = v___y_3829_;
v___y_3820_ = v___y_3830_;
v___y_3821_ = v___y_3831_;
v___y_3822_ = v___y_3832_;
v___y_3823_ = v___y_3833_;
v_a_3824_ = v_a_3921_;
goto v___jp_3817_;
}
}
}
}
else
{
lean_object* v_a_3924_; 
v_a_3924_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3924_);
lean_dec_ref(v___x_3834_);
v___y_3818_ = v___y_3828_;
v___y_3819_ = v___y_3829_;
v___y_3820_ = v___y_3830_;
v___y_3821_ = v___y_3831_;
v___y_3822_ = v___y_3832_;
v___y_3823_ = v___y_3833_;
v_a_3824_ = v_a_3924_;
goto v___jp_3817_;
}
}
v___jp_3925_:
{
if (v___y_3932_ == 0)
{
v___y_3799_ = v___y_3926_;
v___y_3800_ = v___y_3928_;
v___y_3801_ = v___y_3927_;
v___y_3802_ = v___y_3929_;
v___y_3803_ = v___y_3930_;
v___y_3804_ = v___y_3931_;
goto v___jp_3798_;
}
else
{
v___y_3828_ = v___y_3926_;
v___y_3829_ = v___y_3927_;
v___y_3830_ = v___y_3928_;
v___y_3831_ = v___y_3929_;
v___y_3832_ = v___y_3930_;
v___y_3833_ = v___y_3931_;
goto v___jp_3827_;
}
}
v___jp_3933_:
{
if (v___y_3941_ == 0)
{
lean_dec_ref(v___y_3939_);
v___y_3926_ = v___y_3934_;
v___y_3927_ = v___y_3935_;
v___y_3928_ = v___y_3936_;
v___y_3929_ = v___y_3937_;
v___y_3930_ = v___y_3938_;
v___y_3931_ = v___y_3940_;
v___y_3932_ = v___x_3752_;
goto v___jp_3925_;
}
else
{
uint8_t v___x_3942_; 
v___x_3942_ = l_Lean_Expr_hasFVar(v___y_3939_);
lean_dec_ref(v___y_3939_);
if (v___x_3942_ == 0)
{
v___y_3828_ = v___y_3934_;
v___y_3829_ = v___y_3935_;
v___y_3830_ = v___y_3936_;
v___y_3831_ = v___y_3937_;
v___y_3832_ = v___y_3938_;
v___y_3833_ = v___y_3940_;
goto v___jp_3827_;
}
else
{
v___y_3926_ = v___y_3934_;
v___y_3927_ = v___y_3935_;
v___y_3928_ = v___y_3936_;
v___y_3929_ = v___y_3937_;
v___y_3930_ = v___y_3938_;
v___y_3931_ = v___y_3940_;
v___y_3932_ = v___x_3752_;
goto v___jp_3925_;
}
}
}
v___jp_3943_:
{
lean_object* v___x_3951_; 
lean_inc_ref(v___x_3797_);
v___x_3951_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3797_, v___y_3947_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; uint8_t v___x_3953_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref(v___x_3951_);
v___x_3953_ = l_Lean_Expr_hasMVar(v_a_3952_);
if (v___x_3953_ == 0)
{
v___y_3934_ = v___y_3944_;
v___y_3935_ = v___y_3945_;
v___y_3936_ = v___y_3946_;
v___y_3937_ = v___y_3947_;
v___y_3938_ = v___y_3948_;
v___y_3939_ = v_a_3952_;
v___y_3940_ = v___y_3949_;
v___y_3941_ = v___y_3950_;
goto v___jp_3933_;
}
else
{
v___y_3934_ = v___y_3944_;
v___y_3935_ = v___y_3945_;
v___y_3936_ = v___y_3946_;
v___y_3937_ = v___y_3947_;
v___y_3938_ = v___y_3948_;
v___y_3939_ = v_a_3952_;
v___y_3940_ = v___y_3949_;
v___y_3941_ = v___x_3752_;
goto v___jp_3933_;
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3945_);
lean_dec_ref(v___x_3797_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_3954_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3951_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3951_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
v___jp_3962_:
{
if (v___y_3969_ == 0)
{
v___y_3799_ = v___y_3963_;
v___y_3800_ = v___y_3965_;
v___y_3801_ = v___y_3964_;
v___y_3802_ = v___y_3966_;
v___y_3803_ = v___y_3967_;
v___y_3804_ = v___y_3968_;
goto v___jp_3798_;
}
else
{
v___y_3944_ = v___y_3963_;
v___y_3945_ = v___y_3964_;
v___y_3946_ = v___y_3965_;
v___y_3947_ = v___y_3966_;
v___y_3948_ = v___y_3967_;
v___y_3949_ = v___y_3968_;
v___y_3950_ = v___y_3969_;
goto v___jp_3943_;
}
}
v___jp_3970_:
{
uint8_t v_useDecide_3977_; 
v_useDecide_3977_ = lean_ctor_get_uint8(v_config_3645_, sizeof(void*)*1);
if (v_useDecide_3977_ == 0)
{
v___y_3963_ = v_isHEq_3972_;
v___y_3964_ = v___y_3973_;
v___y_3965_ = v___y_3971_;
v___y_3966_ = v___y_3974_;
v___y_3967_ = v___y_3975_;
v___y_3968_ = v___y_3976_;
v___y_3969_ = v___x_3752_;
goto v___jp_3962_;
}
else
{
uint8_t v___x_3978_; 
v___x_3978_ = l_Lean_Expr_hasFVar(v___x_3797_);
if (v___x_3978_ == 0)
{
v___y_3944_ = v_isHEq_3972_;
v___y_3945_ = v___y_3973_;
v___y_3946_ = v___y_3971_;
v___y_3947_ = v___y_3974_;
v___y_3948_ = v___y_3975_;
v___y_3949_ = v___y_3976_;
v___y_3950_ = v_useDecide_3977_;
goto v___jp_3943_;
}
else
{
v___y_3963_ = v_isHEq_3972_;
v___y_3964_ = v___y_3973_;
v___y_3965_ = v___y_3971_;
v___y_3966_ = v___y_3974_;
v___y_3967_ = v___y_3975_;
v___y_3968_ = v___y_3976_;
v___y_3969_ = v___x_3752_;
goto v___jp_3962_;
}
}
}
v___jp_3979_:
{
lean_object* v___x_3987_; 
lean_inc(v___y_3982_);
lean_inc_ref(v___y_3984_);
lean_inc(v___y_3985_);
lean_inc_ref(v___y_3986_);
v___x_3987_ = l_Lean_Meta_isExprDefEq(v___y_3981_, v___y_3983_, v___y_3986_, v___y_3985_, v___y_3984_, v___y_3982_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; uint8_t v___x_3989_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref(v___x_3987_);
v___x_3989_ = lean_unbox(v_a_3988_);
lean_dec(v_a_3988_);
if (v___x_3989_ == 0)
{
v___y_3971_ = v___y_3980_;
v_isHEq_3972_ = v___x_3656_;
v___y_3973_ = v___y_3986_;
v___y_3974_ = v___y_3985_;
v___y_3975_ = v___y_3984_;
v___y_3976_ = v___y_3982_;
goto v___jp_3970_;
}
else
{
lean_object* v___x_3990_; 
lean_dec_ref(v___x_3797_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_config_3645_);
lean_inc(v_mvarId_3646_);
v___x_3990_ = l_Lean_MVarId_getType(v_mvarId_3646_, v___y_3986_, v___y_3985_, v___y_3984_, v___y_3982_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref(v___x_3990_);
v___x_3992_ = l_Lean_LocalDecl_toExpr(v_val_3677_);
lean_inc(v___y_3982_);
lean_inc_ref(v___y_3984_);
lean_inc(v___y_3985_);
lean_inc_ref(v___y_3986_);
v___x_3993_ = l_Lean_Meta_mkEqOfHEq(v___x_3992_, v___x_3656_, v___y_3986_, v___y_3985_, v___y_3984_, v___y_3982_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3995_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref(v___x_3993_);
lean_inc(v___y_3985_);
v___x_3995_ = l_Lean_Meta_mkNoConfusion(v_a_3991_, v_a_3994_, v___y_3986_, v___y_3985_, v___y_3984_, v___y_3982_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3997_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref(v___x_3995_);
v___x_3997_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3646_, v_a_3996_, v___y_3985_);
lean_dec(v___y_3985_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_dec_ref(v___x_3997_);
v___x_3998_ = lean_box(v___x_3656_);
v___x_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
lean_ctor_set(v___x_4000_, 1, v___x_3681_);
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
v_a_3663_ = v___x_4001_;
goto v___jp_3662_;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
v_a_4002_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3997_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3997_);
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
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v___y_3985_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_4010_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3995_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3995_);
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
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v_a_3991_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3982_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_4018_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_3993_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_3993_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3982_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_4026_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_3990_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_3990_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3982_);
lean_dec_ref(v___x_3797_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4034_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_3987_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_3987_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
v___jp_4042_:
{
lean_object* v___x_4048_; 
lean_inc(v___y_4047_);
lean_inc_ref(v___y_4046_);
lean_inc(v___y_4045_);
lean_inc_ref(v___y_4044_);
lean_inc_ref(v___x_3797_);
v___x_4048_ = l_Lean_Meta_matchHEq_x3f(v___x_3797_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref(v___x_4048_);
if (lean_obj_tag(v_a_4049_) == 1)
{
lean_object* v_val_4050_; lean_object* v_snd_4051_; lean_object* v_snd_4052_; lean_object* v_fst_4053_; lean_object* v_fst_4054_; lean_object* v_fst_4055_; lean_object* v_snd_4056_; lean_object* v___x_4057_; 
v_val_4050_ = lean_ctor_get(v_a_4049_, 0);
lean_inc(v_val_4050_);
lean_dec_ref(v_a_4049_);
v_snd_4051_ = lean_ctor_get(v_val_4050_, 1);
lean_inc(v_snd_4051_);
v_snd_4052_ = lean_ctor_get(v_snd_4051_, 1);
lean_inc(v_snd_4052_);
v_fst_4053_ = lean_ctor_get(v_val_4050_, 0);
lean_inc(v_fst_4053_);
lean_dec(v_val_4050_);
v_fst_4054_ = lean_ctor_get(v_snd_4051_, 0);
lean_inc(v_fst_4054_);
lean_dec(v_snd_4051_);
v_fst_4055_ = lean_ctor_get(v_snd_4052_, 0);
lean_inc(v_fst_4055_);
v_snd_4056_ = lean_ctor_get(v_snd_4052_, 1);
lean_inc(v_snd_4056_);
lean_dec(v_snd_4052_);
lean_inc(v___y_4047_);
lean_inc_ref(v___y_4046_);
lean_inc(v___y_4045_);
lean_inc_ref(v___y_4044_);
v___x_4057_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4054_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref(v___x_4057_);
if (lean_obj_tag(v_a_4058_) == 1)
{
lean_object* v_val_4059_; lean_object* v___x_4060_; 
v_val_4059_ = lean_ctor_get(v_a_4058_, 0);
lean_inc(v_val_4059_);
lean_dec_ref(v_a_4058_);
lean_inc(v___y_4047_);
lean_inc_ref(v___y_4046_);
lean_inc(v___y_4045_);
lean_inc_ref(v___y_4044_);
v___x_4060_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4056_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref(v___x_4060_);
if (lean_obj_tag(v_a_4061_) == 1)
{
lean_object* v_toConstantVal_4062_; lean_object* v_val_4063_; lean_object* v_toConstantVal_4064_; lean_object* v_name_4065_; lean_object* v_name_4066_; uint8_t v___x_4067_; 
v_toConstantVal_4062_ = lean_ctor_get(v_val_4059_, 0);
lean_inc_ref(v_toConstantVal_4062_);
lean_dec(v_val_4059_);
v_val_4063_ = lean_ctor_get(v_a_4061_, 0);
lean_inc(v_val_4063_);
lean_dec_ref(v_a_4061_);
v_toConstantVal_4064_ = lean_ctor_get(v_val_4063_, 0);
lean_inc_ref(v_toConstantVal_4064_);
lean_dec(v_val_4063_);
v_name_4065_ = lean_ctor_get(v_toConstantVal_4062_, 0);
lean_inc(v_name_4065_);
lean_dec_ref(v_toConstantVal_4062_);
v_name_4066_ = lean_ctor_get(v_toConstantVal_4064_, 0);
lean_inc(v_name_4066_);
lean_dec_ref(v_toConstantVal_4064_);
v___x_4067_ = lean_name_eq(v_name_4065_, v_name_4066_);
lean_dec(v_name_4066_);
lean_dec(v_name_4065_);
if (v___x_4067_ == 0)
{
v___y_3980_ = v_isEq_4043_;
v___y_3981_ = v_fst_4053_;
v___y_3982_ = v___y_4047_;
v___y_3983_ = v_fst_4055_;
v___y_3984_ = v___y_4046_;
v___y_3985_ = v___y_4045_;
v___y_3986_ = v___y_4044_;
goto v___jp_3979_;
}
else
{
if (v___x_3752_ == 0)
{
lean_dec(v_fst_4055_);
lean_dec(v_fst_4053_);
v___y_3971_ = v_isEq_4043_;
v_isHEq_3972_ = v___x_3656_;
v___y_3973_ = v___y_4044_;
v___y_3974_ = v___y_4045_;
v___y_3975_ = v___y_4046_;
v___y_3976_ = v___y_4047_;
goto v___jp_3970_;
}
else
{
v___y_3980_ = v_isEq_4043_;
v___y_3981_ = v_fst_4053_;
v___y_3982_ = v___y_4047_;
v___y_3983_ = v_fst_4055_;
v___y_3984_ = v___y_4046_;
v___y_3985_ = v___y_4045_;
v___y_3986_ = v___y_4044_;
goto v___jp_3979_;
}
}
}
else
{
lean_dec(v_a_4061_);
lean_dec(v_val_4059_);
lean_dec(v_fst_4055_);
lean_dec(v_fst_4053_);
v___y_3971_ = v_isEq_4043_;
v_isHEq_3972_ = v___x_3656_;
v___y_3973_ = v___y_4044_;
v___y_3974_ = v___y_4045_;
v___y_3975_ = v___y_4046_;
v___y_3976_ = v___y_4047_;
goto v___jp_3970_;
}
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
lean_dec(v_val_4059_);
lean_dec(v_fst_4055_);
lean_dec(v_fst_4053_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec_ref(v___x_3797_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4068_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4060_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4060_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
else
{
lean_dec(v_a_4058_);
lean_dec(v_snd_4056_);
lean_dec(v_fst_4055_);
lean_dec(v_fst_4053_);
v___y_3971_ = v_isEq_4043_;
v_isHEq_3972_ = v___x_3656_;
v___y_3973_ = v___y_4044_;
v___y_3974_ = v___y_4045_;
v___y_3975_ = v___y_4046_;
v___y_3976_ = v___y_4047_;
goto v___jp_3970_;
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec(v_snd_4056_);
lean_dec(v_fst_4055_);
lean_dec(v_fst_4053_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec_ref(v___x_3797_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4076_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4057_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4057_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
else
{
lean_dec(v_a_4049_);
v___y_3971_ = v_isEq_4043_;
v_isHEq_3972_ = v___x_3752_;
v___y_3973_ = v___y_4044_;
v___y_3974_ = v___y_4045_;
v___y_3975_ = v___y_4046_;
v___y_3976_ = v___y_4047_;
goto v___jp_3970_;
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec_ref(v___x_3797_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4084_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4048_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4048_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
v___jp_4092_:
{
lean_object* v___x_4097_; 
lean_inc(v___y_4096_);
lean_inc_ref(v___y_4095_);
lean_inc(v___y_4094_);
lean_inc_ref(v___y_4093_);
lean_inc_ref(v___x_3797_);
v___x_4097_ = l_Lean_Meta_matchEq_x3f(v___x_3797_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc(v_a_4098_);
lean_dec_ref(v___x_4097_);
if (lean_obj_tag(v_a_4098_) == 1)
{
lean_object* v_val_4099_; lean_object* v_snd_4100_; lean_object* v_fst_4101_; lean_object* v_snd_4102_; lean_object* v___x_4103_; 
v_val_4099_ = lean_ctor_get(v_a_4098_, 0);
lean_inc(v_val_4099_);
lean_dec_ref(v_a_4098_);
v_snd_4100_ = lean_ctor_get(v_val_4099_, 1);
lean_inc(v_snd_4100_);
lean_dec(v_val_4099_);
v_fst_4101_ = lean_ctor_get(v_snd_4100_, 0);
lean_inc(v_fst_4101_);
v_snd_4102_ = lean_ctor_get(v_snd_4100_, 1);
lean_inc(v_snd_4102_);
lean_dec(v_snd_4100_);
lean_inc(v___y_4096_);
lean_inc_ref(v___y_4095_);
lean_inc(v___y_4094_);
lean_inc_ref(v___y_4093_);
v___x_4103_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4101_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref(v___x_4103_);
if (lean_obj_tag(v_a_4104_) == 1)
{
lean_object* v_val_4105_; lean_object* v___x_4106_; 
v_val_4105_ = lean_ctor_get(v_a_4104_, 0);
lean_inc(v_val_4105_);
lean_dec_ref(v_a_4104_);
lean_inc(v___y_4096_);
lean_inc_ref(v___y_4095_);
lean_inc(v___y_4094_);
lean_inc_ref(v___y_4093_);
v___x_4106_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4102_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref(v___x_4106_);
if (lean_obj_tag(v_a_4107_) == 1)
{
lean_object* v_toConstantVal_4108_; lean_object* v_val_4109_; lean_object* v_toConstantVal_4110_; lean_object* v_name_4111_; lean_object* v_name_4112_; uint8_t v___x_4113_; 
v_toConstantVal_4108_ = lean_ctor_get(v_val_4105_, 0);
lean_inc_ref(v_toConstantVal_4108_);
lean_dec(v_val_4105_);
v_val_4109_ = lean_ctor_get(v_a_4107_, 0);
lean_inc(v_val_4109_);
lean_dec_ref(v_a_4107_);
v_toConstantVal_4110_ = lean_ctor_get(v_val_4109_, 0);
lean_inc_ref(v_toConstantVal_4110_);
lean_dec(v_val_4109_);
v_name_4111_ = lean_ctor_get(v_toConstantVal_4108_, 0);
lean_inc(v_name_4111_);
lean_dec_ref(v_toConstantVal_4108_);
v_name_4112_ = lean_ctor_get(v_toConstantVal_4110_, 0);
lean_inc(v_name_4112_);
lean_dec_ref(v_toConstantVal_4110_);
v___x_4113_ = lean_name_eq(v_name_4111_, v_name_4112_);
lean_dec(v_name_4112_);
lean_dec(v_name_4111_);
if (v___x_4113_ == 0)
{
lean_dec_ref(v___x_3797_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_config_3645_);
v___y_3683_ = v___y_4095_;
v___y_3684_ = v___y_4094_;
v___y_3685_ = v___y_4093_;
v___y_3686_ = v___y_4096_;
goto v___jp_3682_;
}
else
{
if (v___x_3752_ == 0)
{
lean_del_object(v___x_3679_);
v_isEq_4043_ = v___x_3656_;
v___y_4044_ = v___y_4093_;
v___y_4045_ = v___y_4094_;
v___y_4046_ = v___y_4095_;
v___y_4047_ = v___y_4096_;
goto v___jp_4042_;
}
else
{
lean_dec_ref(v___x_3797_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_config_3645_);
v___y_3683_ = v___y_4095_;
v___y_3684_ = v___y_4094_;
v___y_3685_ = v___y_4093_;
v___y_3686_ = v___y_4096_;
goto v___jp_3682_;
}
}
}
else
{
lean_dec(v_a_4107_);
lean_dec(v_val_4105_);
lean_del_object(v___x_3679_);
v_isEq_4043_ = v___x_3656_;
v___y_4044_ = v___y_4093_;
v___y_4045_ = v___y_4094_;
v___y_4046_ = v___y_4095_;
v___y_4047_ = v___y_4096_;
goto v___jp_4042_;
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
lean_dec(v_val_4105_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4114_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4106_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4106_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
else
{
lean_dec(v_a_4104_);
lean_dec(v_snd_4102_);
lean_del_object(v___x_3679_);
v_isEq_4043_ = v___x_3656_;
v___y_4044_ = v___y_4093_;
v___y_4045_ = v___y_4094_;
v___y_4046_ = v___y_4095_;
v___y_4047_ = v___y_4096_;
goto v___jp_4042_;
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec(v_snd_4102_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4122_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4103_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4103_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
else
{
lean_dec(v_a_4098_);
lean_del_object(v___x_3679_);
v_isEq_4043_ = v___x_3752_;
v___y_4044_ = v___y_4093_;
v___y_4045_ = v___y_4094_;
v___y_4046_ = v___y_4095_;
v___y_4047_ = v___y_4096_;
goto v___jp_4042_;
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4130_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4097_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4097_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
v___jp_4138_:
{
lean_object* v___x_4143_; 
lean_inc(v___y_4142_);
lean_inc_ref(v___y_4141_);
lean_inc(v___y_4140_);
lean_inc_ref(v___y_4139_);
lean_inc_ref(v___x_3797_);
v___x_4143_ = l_refutableHasNotBit_x3f(v___x_3797_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref(v___x_4143_);
if (lean_obj_tag(v_a_4144_) == 1)
{
lean_object* v_val_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4185_; 
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_config_3645_);
v_val_4145_ = lean_ctor_get(v_a_4144_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v_a_4144_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4147_ = v_a_4144_;
v_isShared_4148_ = v_isSharedCheck_4185_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_val_4145_);
lean_dec(v_a_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4185_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; 
lean_inc(v_mvarId_3646_);
v___x_4149_ = l_Lean_MVarId_getType(v_mvarId_3646_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref(v___x_4149_);
v___x_4151_ = l_Lean_LocalDecl_toExpr(v_val_3677_);
lean_inc(v___y_4140_);
v___x_4152_ = l_Lean_Meta_mkAbsurd(v_a_4150_, v_val_4145_, v___x_4151_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref(v___x_4152_);
v___x_4154_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3646_, v_a_4153_, v___y_4140_);
lean_dec(v___y_4140_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v___x_4155_; lean_object* v___x_4157_; 
lean_dec_ref(v___x_4154_);
v___x_4155_ = lean_box(v___x_3656_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 0, v___x_4155_);
v___x_4157_ = v___x_4147_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
lean_ctor_set(v___x_4158_, 1, v___x_3681_);
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
v_a_3663_ = v___x_4159_;
goto v___jp_3662_;
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
lean_del_object(v___x_4147_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
v_a_4161_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4154_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4154_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_del_object(v___x_4147_);
lean_dec(v___y_4140_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_4169_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4152_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4152_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_del_object(v___x_4147_);
lean_dec(v_val_4145_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_4177_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4149_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4149_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
else
{
lean_object* v___x_4186_; 
lean_dec(v_a_4144_);
lean_inc(v___y_4142_);
lean_inc_ref(v___y_4141_);
lean_inc(v___y_4140_);
lean_inc_ref(v___y_4139_);
lean_inc_ref(v___x_3797_);
v___x_4186_ = l_Lean_Meta_matchNe_x3f(v___x_3797_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref(v___x_4186_);
if (lean_obj_tag(v_a_4187_) == 1)
{
lean_object* v_val_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4258_; 
v_val_4188_ = lean_ctor_get(v_a_4187_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v_a_4187_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4190_ = v_a_4187_;
v_isShared_4191_ = v_isSharedCheck_4258_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_val_4188_);
lean_dec(v_a_4187_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4258_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v_snd_4192_; lean_object* v_fst_4193_; lean_object* v_snd_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4257_; 
v_snd_4192_ = lean_ctor_get(v_val_4188_, 1);
lean_inc(v_snd_4192_);
lean_dec(v_val_4188_);
v_fst_4193_ = lean_ctor_get(v_snd_4192_, 0);
v_snd_4194_ = lean_ctor_get(v_snd_4192_, 1);
v_isSharedCheck_4257_ = !lean_is_exclusive(v_snd_4192_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4196_ = v_snd_4192_;
v_isShared_4197_ = v_isSharedCheck_4257_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_snd_4194_);
lean_inc(v_fst_4193_);
lean_dec(v_snd_4192_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4257_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4198_; 
lean_inc(v___y_4142_);
lean_inc_ref(v___y_4141_);
lean_inc(v___y_4140_);
lean_inc_ref(v___y_4139_);
lean_inc(v_fst_4193_);
v___x_4198_ = l_Lean_Meta_isExprDefEq(v_fst_4193_, v_snd_4194_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; uint8_t v___x_4200_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = lean_unbox(v_a_4199_);
lean_dec(v_a_4199_);
if (v___x_4200_ == 0)
{
lean_del_object(v___x_4196_);
lean_dec(v_fst_4193_);
lean_del_object(v___x_4190_);
v___y_4093_ = v___y_4139_;
v___y_4094_ = v___y_4140_;
v___y_4095_ = v___y_4141_;
v___y_4096_ = v___y_4142_;
goto v___jp_4092_;
}
else
{
lean_object* v___x_4201_; 
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_config_3645_);
lean_inc(v_mvarId_3646_);
v___x_4201_ = l_Lean_MVarId_getType(v_mvarId_3646_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4203_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
lean_dec_ref(v___x_4201_);
lean_inc(v___y_4142_);
lean_inc_ref(v___y_4141_);
lean_inc(v___y_4140_);
lean_inc_ref(v___y_4139_);
v___x_4203_ = l_Lean_Meta_mkEqRefl(v_fst_4193_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref(v___x_4203_);
v___x_4205_ = l_Lean_LocalDecl_toExpr(v_val_3677_);
lean_inc(v___y_4140_);
v___x_4206_ = l_Lean_Meta_mkAbsurd(v_a_4202_, v_a_4204_, v___x_4205_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4208_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref(v___x_4206_);
v___x_4208_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3646_, v_a_4207_, v___y_4140_);
lean_dec(v___y_4140_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4211_; 
lean_dec_ref(v___x_4208_);
v___x_4209_ = lean_box(v___x_3656_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4209_);
v___x_4211_ = v___x_4190_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4209_);
v___x_4211_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
lean_object* v___x_4213_; 
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 1, v___x_3681_);
lean_ctor_set(v___x_4196_, 0, v___x_4211_);
v___x_4213_ = v___x_4196_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4211_);
lean_ctor_set(v_reuseFailAlloc_4215_, 1, v___x_3681_);
v___x_4213_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; 
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
v_a_3663_ = v___x_4214_;
goto v___jp_3662_;
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_del_object(v___x_4196_);
lean_del_object(v___x_4190_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
v_a_4217_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4208_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4208_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
lean_del_object(v___x_4196_);
lean_del_object(v___x_4190_);
lean_dec(v___y_4140_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_4225_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4206_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4206_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec(v_a_4202_);
lean_del_object(v___x_4196_);
lean_del_object(v___x_4190_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_4233_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4203_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4203_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_del_object(v___x_4196_);
lean_dec(v_fst_4193_);
lean_del_object(v___x_4190_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_4241_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4201_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4201_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_del_object(v___x_4196_);
lean_dec(v_fst_4193_);
lean_del_object(v___x_4190_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4249_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4198_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4198_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4187_);
v___y_4093_ = v___y_4139_;
v___y_4094_ = v___y_4140_;
v___y_4095_ = v___y_4141_;
v___y_4096_ = v___y_4142_;
goto v___jp_4092_;
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4259_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_4186_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_4186_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec_ref(v___x_3797_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_4267_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4143_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4143_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
}
else
{
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
v_a_3671_ = v___x_3723_;
goto v___jp_3670_;
}
v___jp_3682_:
{
lean_object* v___x_3687_; 
lean_inc(v_mvarId_3646_);
v___x_3687_ = l_Lean_MVarId_getType(v_mvarId_3646_, v___y_3685_, v___y_3684_, v___y_3683_, v___y_3686_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref(v___x_3687_);
v___x_3689_ = l_Lean_LocalDecl_toExpr(v_val_3677_);
lean_inc(v___y_3684_);
v___x_3690_ = l_Lean_Meta_mkNoConfusion(v_a_3688_, v___x_3689_, v___y_3685_, v___y_3684_, v___y_3683_, v___y_3686_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3692_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3646_, v_a_3691_, v___y_3684_);
lean_dec(v___y_3684_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v___x_3693_; lean_object* v___x_3695_; 
lean_dec_ref(v___x_3692_);
v___x_3693_ = lean_box(v___x_3656_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v___x_3693_);
v___x_3695_ = v___x_3679_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
lean_ctor_set(v___x_3696_, 1, v___x_3681_);
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
v_a_3663_ = v___x_3697_;
goto v___jp_3662_;
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_del_object(v___x_3679_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
v_a_3699_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3692_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3692_);
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
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec(v___y_3684_);
lean_del_object(v___x_3679_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_3707_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3690_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3690_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_del_object(v___x_3679_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_3715_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3687_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3687_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
v___jp_3724_:
{
lean_object* v_searchFuel_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_searchFuel_3729_ = lean_ctor_get(v_config_3645_, 0);
v___x_3730_ = l_Lean_LocalDecl_fvarId(v_val_3677_);
lean_dec(v_val_3677_);
lean_inc(v_searchFuel_3729_);
lean_inc(v_mvarId_3646_);
v___x_3731_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3646_, v___x_3730_, v_searchFuel_3729_, v___y_3725_, v___y_3726_, v___y_3728_, v___y_3727_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; uint8_t v___x_3733_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref(v___x_3731_);
v___x_3733_ = lean_unbox(v_a_3732_);
lean_dec(v_a_3732_);
if (v___x_3733_ == 0)
{
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
v_a_3671_ = v___x_3723_;
goto v___jp_3670_;
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v___x_3734_ = lean_box(v___x_3656_);
v___x_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v___x_3681_);
v___x_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
v_a_3663_ = v___x_3737_;
goto v___jp_3662_;
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_3738_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3731_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3731_);
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
v___jp_3746_:
{
if (v___y_3751_ == 0)
{
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
v_a_3671_ = v___x_3723_;
goto v___jp_3670_;
}
else
{
v___y_3725_ = v___y_3747_;
v___y_3726_ = v___y_3748_;
v___y_3727_ = v___y_3749_;
v___y_3728_ = v___y_3750_;
goto v___jp_3724_;
}
}
v___jp_3753_:
{
if (v___y_3754_ == 0)
{
v___y_3725_ = v___y_3755_;
v___y_3726_ = v___y_3756_;
v___y_3727_ = v___y_3757_;
v___y_3728_ = v___y_3758_;
goto v___jp_3724_;
}
else
{
v___y_3747_ = v___y_3755_;
v___y_3748_ = v___y_3756_;
v___y_3749_ = v___y_3757_;
v___y_3750_ = v___y_3758_;
v___y_3751_ = v___x_3752_;
goto v___jp_3746_;
}
}
v___jp_3759_:
{
if (v___y_3765_ == 0)
{
v___y_3747_ = v___y_3761_;
v___y_3748_ = v___y_3762_;
v___y_3749_ = v___y_3763_;
v___y_3750_ = v___y_3764_;
v___y_3751_ = v___x_3752_;
goto v___jp_3746_;
}
else
{
v___y_3754_ = v___y_3760_;
v___y_3755_ = v___y_3761_;
v___y_3756_ = v___y_3762_;
v___y_3757_ = v___y_3763_;
v___y_3758_ = v___y_3764_;
goto v___jp_3753_;
}
}
v___jp_3766_:
{
uint8_t v_emptyType_3773_; 
v_emptyType_3773_ = lean_ctor_get_uint8(v_config_3645_, sizeof(void*)*1 + 1);
if (v_emptyType_3773_ == 0)
{
v___y_3760_ = v___y_3767_;
v___y_3761_ = v___y_3769_;
v___y_3762_ = v___y_3770_;
v___y_3763_ = v___y_3772_;
v___y_3764_ = v___y_3771_;
v___y_3765_ = v___x_3752_;
goto v___jp_3759_;
}
else
{
if (v___y_3768_ == 0)
{
v___y_3754_ = v___y_3767_;
v___y_3755_ = v___y_3769_;
v___y_3756_ = v___y_3770_;
v___y_3757_ = v___y_3772_;
v___y_3758_ = v___y_3771_;
goto v___jp_3753_;
}
else
{
v___y_3760_ = v___y_3767_;
v___y_3761_ = v___y_3769_;
v___y_3762_ = v___y_3770_;
v___y_3763_ = v___y_3772_;
v___y_3764_ = v___y_3771_;
v___y_3765_ = v___x_3752_;
goto v___jp_3759_;
}
}
}
v___jp_3774_:
{
if (v___y_3781_ == 0)
{
v___y_3767_ = v___y_3776_;
v___y_3768_ = v___y_3778_;
v___y_3769_ = v___y_3780_;
v___y_3770_ = v___y_3775_;
v___y_3771_ = v___y_3777_;
v___y_3772_ = v___y_3779_;
goto v___jp_3766_;
}
else
{
lean_object* v___x_3782_; 
lean_inc(v___y_3779_);
lean_inc_ref(v___y_3777_);
lean_inc(v___y_3775_);
lean_inc_ref(v___y_3780_);
lean_inc(v_val_3677_);
lean_inc(v_mvarId_3646_);
v___x_3782_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3646_, v_val_3677_, v___y_3780_, v___y_3775_, v___y_3777_, v___y_3779_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; uint8_t v___x_3784_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref(v___x_3782_);
v___x_3784_ = lean_unbox(v_a_3783_);
lean_dec(v_a_3783_);
if (v___x_3784_ == 0)
{
v___y_3767_ = v___y_3776_;
v___y_3768_ = v___y_3778_;
v___y_3769_ = v___y_3780_;
v___y_3770_ = v___y_3775_;
v___y_3771_ = v___y_3777_;
v___y_3772_ = v___y_3779_;
goto v___jp_3766_;
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3775_);
lean_dec(v_val_3677_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v___x_3785_ = lean_box(v___x_3656_);
v___x_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
v___x_3787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
lean_ctor_set(v___x_3787_, 1, v___x_3681_);
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
v_a_3663_ = v___x_3788_;
goto v___jp_3662_;
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3775_);
lean_dec(v_val_3677_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_mvarId_3646_);
lean_dec_ref(v_config_3645_);
v_a_3789_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3782_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3782_);
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
}
}
}
v___jp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3664_, 0, v_a_3663_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3664_);
v___x_3666_ = v___x_3660_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_snd_3658_);
v___x_3666_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; 
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
return v___x_3667_;
}
}
v___jp_3670_:
{
lean_object* v___x_3672_; size_t v___x_3673_; size_t v___x_3674_; 
v___x_3672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3669_);
lean_ctor_set(v___x_3672_, 1, v_a_3671_);
v___x_3673_ = ((size_t)1ULL);
v___x_3674_ = lean_usize_add(v_i_3649_, v___x_3673_);
v_i_3649_ = v___x_3674_;
v_b_3650_ = v___x_3672_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_4348_, lean_object* v_mvarId_4349_, lean_object* v_as_4350_, lean_object* v_sz_4351_, lean_object* v_i_4352_, lean_object* v_b_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
size_t v_sz_boxed_4359_; size_t v_i_boxed_4360_; lean_object* v_res_4361_; 
v_sz_boxed_4359_ = lean_unbox_usize(v_sz_4351_);
lean_dec(v_sz_4351_);
v_i_boxed_4360_ = lean_unbox_usize(v_i_4352_);
lean_dec(v_i_4352_);
v_res_4361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_4348_, v_mvarId_4349_, v_as_4350_, v_sz_boxed_4359_, v_i_boxed_4360_, v_b_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
lean_dec_ref(v_as_4350_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_4362_, lean_object* v_mvarId_4363_, lean_object* v_as_4364_, size_t v_sz_4365_, size_t v_i_4366_, lean_object* v_b_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
uint8_t v___x_4373_; 
v___x_4373_ = lean_usize_dec_lt(v_i_4366_, v_sz_4365_);
if (v___x_4373_ == 0)
{
lean_object* v___x_4374_; 
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v_b_4367_);
return v___x_4374_;
}
else
{
lean_object* v_snd_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_5063_; 
v_snd_4375_ = lean_ctor_get(v_b_4367_, 1);
v_isSharedCheck_5063_ = !lean_is_exclusive(v_b_4367_);
if (v_isSharedCheck_5063_ == 0)
{
lean_object* v_unused_5064_; 
v_unused_5064_ = lean_ctor_get(v_b_4367_, 0);
lean_dec(v_unused_5064_);
v___x_4377_ = v_b_4367_;
v_isShared_4378_ = v_isSharedCheck_5063_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_snd_4375_);
lean_dec(v_b_4367_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_5063_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v_a_4380_; lean_object* v___x_4386_; lean_object* v_a_4388_; lean_object* v_a_4393_; 
v___x_4386_ = lean_box(0);
v_a_4393_ = lean_array_uget(v_as_4364_, v_i_4366_);
if (lean_obj_tag(v_a_4393_) == 0)
{
lean_del_object(v___x_4377_);
v_a_4388_ = v_snd_4375_;
goto v___jp_4387_;
}
else
{
lean_object* v_val_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_5062_; 
v_val_4394_ = lean_ctor_get(v_a_4393_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v_a_4393_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_4396_ = v_a_4393_;
v_isShared_4397_ = v_isSharedCheck_5062_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_val_4394_);
lean_dec(v_a_4393_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_5062_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___x_4440_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; uint8_t v___y_4468_; uint8_t v___x_4469_; lean_object* v___y_4471_; uint8_t v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4477_; uint8_t v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; uint8_t v___y_4482_; uint8_t v___y_4484_; uint8_t v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4492_; lean_object* v___y_4493_; uint8_t v___y_4494_; lean_object* v___y_4495_; uint8_t v___y_4496_; lean_object* v___y_4497_; uint8_t v___y_4498_; 
v___x_4398_ = lean_box(0);
v___x_4440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_4469_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4394_);
if (v___x_4469_ == 0)
{
lean_object* v___x_4514_; uint8_t v___y_4516_; uint8_t v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4525_; uint8_t v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; uint8_t v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; uint8_t v___y_4532_; lean_object* v___y_4535_; uint8_t v___y_4536_; lean_object* v___y_4537_; uint8_t v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v_a_4541_; lean_object* v___y_4545_; uint8_t v___y_4546_; lean_object* v___y_4547_; uint8_t v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4643_; uint8_t v___y_4644_; lean_object* v___y_4645_; uint8_t v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; uint8_t v___y_4649_; lean_object* v___y_4651_; lean_object* v___y_4652_; uint8_t v___y_4653_; lean_object* v___y_4654_; uint8_t v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; uint8_t v___y_4658_; lean_object* v___y_4661_; uint8_t v___y_4662_; lean_object* v___y_4663_; uint8_t v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; uint8_t v___y_4667_; lean_object* v___y_4680_; uint8_t v___y_4681_; lean_object* v___y_4682_; uint8_t v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; uint8_t v___y_4686_; uint8_t v___y_4688_; uint8_t v_isHEq_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___y_4700_; uint8_t v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4703_; uint8_t v_isEq_4760_; lean_object* v___y_4761_; lean_object* v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___y_4810_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___y_4813_; lean_object* v___y_4856_; lean_object* v___y_4857_; lean_object* v___y_4858_; lean_object* v___y_4859_; lean_object* v___x_4992_; 
v___x_4514_ = l_Lean_LocalDecl_type(v_val_4394_);
lean_inc(v___y_4371_);
lean_inc_ref(v___y_4370_);
lean_inc(v___y_4369_);
lean_inc_ref(v___y_4368_);
lean_inc_ref(v___x_4514_);
v___x_4992_ = l_Lean_Meta_matchNot_x3f(v___x_4514_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v_a_4993_; 
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
lean_inc(v_a_4993_);
lean_dec_ref(v___x_4992_);
if (lean_obj_tag(v_a_4993_) == 1)
{
lean_object* v_val_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5053_; 
v_val_4994_ = lean_ctor_get(v_a_4993_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v_a_4993_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_4996_ = v_a_4993_;
v_isShared_4997_ = v_isSharedCheck_5053_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_val_4994_);
lean_dec(v_a_4993_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5053_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4998_; 
lean_inc(v___y_4371_);
lean_inc_ref(v___y_4370_);
lean_inc(v___y_4369_);
lean_inc_ref(v___y_4368_);
v___x_4998_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4994_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v_a_4999_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
lean_inc(v_a_4999_);
lean_dec_ref(v___x_4998_);
if (lean_obj_tag(v_a_4999_) == 1)
{
lean_object* v_val_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5044_; 
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec_ref(v_config_4362_);
v_val_5000_ = lean_ctor_get(v_a_4999_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v_a_4999_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5002_ = v_a_4999_;
v_isShared_5003_ = v_isSharedCheck_5044_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_val_5000_);
lean_dec(v_a_4999_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5044_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5004_; 
lean_inc(v_mvarId_4363_);
v___x_5004_ = l_Lean_MVarId_getType(v_mvarId_4363_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_5004_) == 0)
{
lean_object* v_a_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v_a_5005_ = lean_ctor_get(v___x_5004_, 0);
lean_inc(v_a_5005_);
lean_dec_ref(v___x_5004_);
v___x_5006_ = l_Lean_LocalDecl_toExpr(v_val_4394_);
v___x_5007_ = l_Lean_mkFVar(v_val_5000_);
v___x_5008_ = l_Lean_Expr_app___override(v___x_5006_, v___x_5007_);
lean_inc(v___y_4369_);
v___x_5009_ = l_Lean_Meta_mkFalseElim(v_a_5005_, v___x_5008_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5011_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
lean_inc(v_a_5010_);
lean_dec_ref(v___x_5009_);
v___x_5011_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4363_, v_a_5010_, v___y_4369_);
lean_dec(v___y_4369_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v___x_5012_; lean_object* v___x_5014_; 
lean_dec_ref(v___x_5011_);
v___x_5012_ = lean_box(v___x_4373_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 0, v___x_5012_);
v___x_5014_ = v___x_5002_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_5012_);
v___x_5014_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
lean_object* v___x_5015_; lean_object* v___x_5017_; 
v___x_5015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5014_);
lean_ctor_set(v___x_5015_, 1, v___x_4398_);
if (v_isShared_4997_ == 0)
{
lean_ctor_set_tag(v___x_4996_, 0);
lean_ctor_set(v___x_4996_, 0, v___x_5015_);
v___x_5017_ = v___x_4996_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5015_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
v_a_4380_ = v___x_5017_;
goto v___jp_4379_;
}
}
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_del_object(v___x_5002_);
lean_del_object(v___x_4996_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
v_a_5020_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___x_5011_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5011_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
lean_del_object(v___x_5002_);
lean_del_object(v___x_4996_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4369_);
lean_dec(v_mvarId_4363_);
v_a_5028_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_5009_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_5009_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5033_; 
if (v_isShared_5031_ == 0)
{
v___x_5033_ = v___x_5030_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_5028_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
else
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
lean_del_object(v___x_5002_);
lean_dec(v_val_5000_);
lean_del_object(v___x_4996_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
v_a_5036_ = lean_ctor_get(v___x_5004_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5004_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5038_ = v___x_5004_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_5004_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5041_; 
if (v_isShared_5039_ == 0)
{
v___x_5041_ = v___x_5038_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5036_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
}
}
else
{
lean_dec(v_a_4999_);
lean_del_object(v___x_4996_);
lean_inc(v___y_4371_);
lean_inc_ref(v___y_4370_);
lean_inc(v___y_4369_);
lean_inc_ref(v___y_4368_);
v___y_4856_ = v___y_4368_;
v___y_4857_ = v___y_4369_;
v___y_4858_ = v___y_4370_;
v___y_4859_ = v___y_4371_;
goto v___jp_4855_;
}
}
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
lean_del_object(v___x_4996_);
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_5045_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_4998_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_4998_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
}
else
{
lean_dec(v_a_4993_);
lean_inc(v___y_4371_);
lean_inc_ref(v___y_4370_);
lean_inc(v___y_4369_);
lean_inc_ref(v___y_4368_);
v___y_4856_ = v___y_4368_;
v___y_4857_ = v___y_4369_;
v___y_4858_ = v___y_4370_;
v___y_4859_ = v___y_4371_;
goto v___jp_4855_;
}
}
else
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5061_; 
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_5054_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5056_ = v___x_4992_;
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_4992_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5057_ == 0)
{
v___x_5059_ = v___x_5056_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5054_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
}
v___jp_4515_:
{
uint8_t v_genDiseq_4522_; 
v_genDiseq_4522_ = lean_ctor_get_uint8(v_config_4362_, sizeof(void*)*1 + 2);
if (v_genDiseq_4522_ == 0)
{
lean_dec_ref(v___x_4514_);
v___y_4492_ = v___y_4521_;
v___y_4493_ = v___y_4518_;
v___y_4494_ = v___y_4516_;
v___y_4495_ = v___y_4520_;
v___y_4496_ = v___y_4517_;
v___y_4497_ = v___y_4519_;
v___y_4498_ = v___x_4469_;
goto v___jp_4491_;
}
else
{
uint8_t v___x_4523_; 
v___x_4523_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4514_);
v___y_4492_ = v___y_4521_;
v___y_4493_ = v___y_4518_;
v___y_4494_ = v___y_4516_;
v___y_4495_ = v___y_4520_;
v___y_4496_ = v___y_4517_;
v___y_4497_ = v___y_4519_;
v___y_4498_ = v___x_4523_;
goto v___jp_4491_;
}
}
v___jp_4524_:
{
if (v___y_4532_ == 0)
{
lean_dec_ref(v___y_4528_);
v___y_4516_ = v___y_4526_;
v___y_4517_ = v___y_4529_;
v___y_4518_ = v___y_4530_;
v___y_4519_ = v___y_4531_;
v___y_4520_ = v___y_4525_;
v___y_4521_ = v___y_4527_;
goto v___jp_4515_;
}
else
{
lean_object* v___x_4533_; 
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4525_);
lean_dec_ref(v___x_4514_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v___x_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4533_, 0, v___y_4528_);
return v___x_4533_;
}
}
v___jp_4534_:
{
uint8_t v___x_4542_; 
v___x_4542_ = l_Lean_Exception_isInterrupt(v_a_4541_);
if (v___x_4542_ == 0)
{
uint8_t v___x_4543_; 
lean_inc_ref(v_a_4541_);
v___x_4543_ = l_Lean_Exception_isRuntime(v_a_4541_);
v___y_4525_ = v___y_4535_;
v___y_4526_ = v___y_4536_;
v___y_4527_ = v___y_4537_;
v___y_4528_ = v_a_4541_;
v___y_4529_ = v___y_4538_;
v___y_4530_ = v___y_4539_;
v___y_4531_ = v___y_4540_;
v___y_4532_ = v___x_4543_;
goto v___jp_4524_;
}
else
{
v___y_4525_ = v___y_4535_;
v___y_4526_ = v___y_4536_;
v___y_4527_ = v___y_4537_;
v___y_4528_ = v_a_4541_;
v___y_4529_ = v___y_4538_;
v___y_4530_ = v___y_4539_;
v___y_4531_ = v___y_4540_;
v___y_4532_ = v___x_4542_;
goto v___jp_4524_;
}
}
v___jp_4544_:
{
lean_object* v___x_4551_; 
lean_inc(v___y_4547_);
lean_inc_ref(v___y_4545_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
lean_inc_ref(v___x_4514_);
v___x_4551_ = l_Lean_Meta_mkDecide(v___x_4514_, v___y_4549_, v___y_4550_, v___y_4545_, v___y_4547_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v___x_4553_; uint8_t v_foApprox_4554_; uint8_t v_ctxApprox_4555_; uint8_t v_quasiPatternApprox_4556_; uint8_t v_constApprox_4557_; uint8_t v_isDefEqStuckEx_4558_; uint8_t v_unificationHints_4559_; uint8_t v_proofIrrelevance_4560_; uint8_t v_assignSyntheticOpaque_4561_; uint8_t v_offsetCnstrs_4562_; uint8_t v_etaStruct_4563_; uint8_t v_univApprox_4564_; uint8_t v_iota_4565_; uint8_t v_beta_4566_; uint8_t v_proj_4567_; uint8_t v_zeta_4568_; uint8_t v_zetaDelta_4569_; uint8_t v_zetaUnused_4570_; uint8_t v_zetaHave_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4640_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref(v___x_4551_);
v___x_4553_ = l_Lean_Meta_Context_config(v___y_4549_);
v_foApprox_4554_ = lean_ctor_get_uint8(v___x_4553_, 0);
v_ctxApprox_4555_ = lean_ctor_get_uint8(v___x_4553_, 1);
v_quasiPatternApprox_4556_ = lean_ctor_get_uint8(v___x_4553_, 2);
v_constApprox_4557_ = lean_ctor_get_uint8(v___x_4553_, 3);
v_isDefEqStuckEx_4558_ = lean_ctor_get_uint8(v___x_4553_, 4);
v_unificationHints_4559_ = lean_ctor_get_uint8(v___x_4553_, 5);
v_proofIrrelevance_4560_ = lean_ctor_get_uint8(v___x_4553_, 6);
v_assignSyntheticOpaque_4561_ = lean_ctor_get_uint8(v___x_4553_, 7);
v_offsetCnstrs_4562_ = lean_ctor_get_uint8(v___x_4553_, 8);
v_etaStruct_4563_ = lean_ctor_get_uint8(v___x_4553_, 10);
v_univApprox_4564_ = lean_ctor_get_uint8(v___x_4553_, 11);
v_iota_4565_ = lean_ctor_get_uint8(v___x_4553_, 12);
v_beta_4566_ = lean_ctor_get_uint8(v___x_4553_, 13);
v_proj_4567_ = lean_ctor_get_uint8(v___x_4553_, 14);
v_zeta_4568_ = lean_ctor_get_uint8(v___x_4553_, 15);
v_zetaDelta_4569_ = lean_ctor_get_uint8(v___x_4553_, 16);
v_zetaUnused_4570_ = lean_ctor_get_uint8(v___x_4553_, 17);
v_zetaHave_4571_ = lean_ctor_get_uint8(v___x_4553_, 18);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4573_ = v___x_4553_;
v_isShared_4574_ = v_isSharedCheck_4640_;
goto v_resetjp_4572_;
}
else
{
lean_dec(v___x_4553_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4640_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
uint8_t v_trackZetaDelta_4575_; lean_object* v_zetaDeltaSet_4576_; lean_object* v_lctx_4577_; lean_object* v_localInstances_4578_; lean_object* v_defEqCtx_x3f_4579_; lean_object* v_synthPendingDepth_4580_; lean_object* v_canUnfold_x3f_4581_; uint8_t v_univApprox_4582_; uint8_t v_inTypeClassResolution_4583_; uint8_t v_cacheInferType_4584_; uint8_t v___x_4585_; lean_object* v_config_4587_; 
v_trackZetaDelta_4575_ = lean_ctor_get_uint8(v___y_4549_, sizeof(void*)*7);
v_zetaDeltaSet_4576_ = lean_ctor_get(v___y_4549_, 1);
v_lctx_4577_ = lean_ctor_get(v___y_4549_, 2);
v_localInstances_4578_ = lean_ctor_get(v___y_4549_, 3);
v_defEqCtx_x3f_4579_ = lean_ctor_get(v___y_4549_, 4);
v_synthPendingDepth_4580_ = lean_ctor_get(v___y_4549_, 5);
v_canUnfold_x3f_4581_ = lean_ctor_get(v___y_4549_, 6);
v_univApprox_4582_ = lean_ctor_get_uint8(v___y_4549_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4583_ = lean_ctor_get_uint8(v___y_4549_, sizeof(void*)*7 + 2);
v_cacheInferType_4584_ = lean_ctor_get_uint8(v___y_4549_, sizeof(void*)*7 + 3);
v___x_4585_ = 1;
if (v_isShared_4574_ == 0)
{
v_config_4587_ = v___x_4573_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 0, v_foApprox_4554_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 1, v_ctxApprox_4555_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 2, v_quasiPatternApprox_4556_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 3, v_constApprox_4557_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 4, v_isDefEqStuckEx_4558_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 5, v_unificationHints_4559_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 6, v_proofIrrelevance_4560_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 7, v_assignSyntheticOpaque_4561_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 8, v_offsetCnstrs_4562_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 10, v_etaStruct_4563_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 11, v_univApprox_4564_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 12, v_iota_4565_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 13, v_beta_4566_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 14, v_proj_4567_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 15, v_zeta_4568_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 16, v_zetaDelta_4569_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 17, v_zetaUnused_4570_);
lean_ctor_set_uint8(v_reuseFailAlloc_4639_, 18, v_zetaHave_4571_);
v_config_4587_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
uint64_t v___x_4588_; uint64_t v___x_4589_; uint64_t v___x_4590_; uint64_t v___x_4591_; uint64_t v___x_4592_; uint64_t v_key_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
lean_ctor_set_uint8(v_config_4587_, 9, v___x_4585_);
v___x_4588_ = l_Lean_Meta_Context_configKey(v___y_4549_);
v___x_4589_ = 2ULL;
v___x_4590_ = lean_uint64_shift_right(v___x_4588_, v___x_4589_);
v___x_4591_ = lean_uint64_shift_left(v___x_4590_, v___x_4589_);
v___x_4592_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_4593_ = lean_uint64_lor(v___x_4591_, v___x_4592_);
v___x_4594_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4594_, 0, v_config_4587_);
lean_ctor_set_uint64(v___x_4594_, sizeof(void*)*1, v_key_4593_);
lean_inc(v_canUnfold_x3f_4581_);
lean_inc(v_synthPendingDepth_4580_);
lean_inc(v_defEqCtx_x3f_4579_);
lean_inc_ref(v_localInstances_4578_);
lean_inc_ref(v_lctx_4577_);
lean_inc(v_zetaDeltaSet_4576_);
v___x_4595_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
lean_ctor_set(v___x_4595_, 1, v_zetaDeltaSet_4576_);
lean_ctor_set(v___x_4595_, 2, v_lctx_4577_);
lean_ctor_set(v___x_4595_, 3, v_localInstances_4578_);
lean_ctor_set(v___x_4595_, 4, v_defEqCtx_x3f_4579_);
lean_ctor_set(v___x_4595_, 5, v_synthPendingDepth_4580_);
lean_ctor_set(v___x_4595_, 6, v_canUnfold_x3f_4581_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*7, v_trackZetaDelta_4575_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*7 + 1, v_univApprox_4582_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4583_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*7 + 3, v_cacheInferType_4584_);
lean_inc(v___y_4547_);
lean_inc_ref(v___y_4545_);
lean_inc(v___y_4550_);
lean_inc(v_a_4552_);
v___x_4596_ = lean_whnf(v_a_4552_, v___x_4595_, v___y_4550_, v___y_4545_, v___y_4547_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4598_; uint8_t v___x_4599_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref(v___x_4596_);
v___x_4598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_4599_ = l_Lean_Expr_isConstOf(v_a_4597_, v___x_4598_);
lean_dec(v_a_4597_);
if (v___x_4599_ == 0)
{
lean_dec(v_a_4552_);
v___y_4516_ = v___y_4546_;
v___y_4517_ = v___y_4548_;
v___y_4518_ = v___y_4549_;
v___y_4519_ = v___y_4550_;
v___y_4520_ = v___y_4545_;
v___y_4521_ = v___y_4547_;
goto v___jp_4515_;
}
else
{
lean_object* v___x_4600_; 
lean_inc(v___y_4547_);
lean_inc_ref(v___y_4545_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
lean_inc(v_a_4552_);
v___x_4600_ = l_Lean_Meta_mkEqRefl(v_a_4552_, v___y_4549_, v___y_4550_, v___y_4545_, v___y_4547_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v_a_4601_; lean_object* v___x_4602_; 
v_a_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc(v_a_4601_);
lean_dec_ref(v___x_4600_);
lean_inc(v_mvarId_4363_);
v___x_4602_ = l_Lean_MVarId_getType(v_mvarId_4363_, v___y_4549_, v___y_4550_, v___y_4545_, v___y_4547_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v_nargs_4604_; lean_object* v___x_4605_; lean_object* v_dummy_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_a_4603_);
lean_dec_ref(v___x_4602_);
v_nargs_4604_ = l_Lean_Expr_getAppNumArgs(v_a_4552_);
v___x_4605_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_4606_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_4604_);
v___x_4607_ = lean_mk_array(v_nargs_4604_, v_dummy_4606_);
v___x_4608_ = lean_unsigned_to_nat(1u);
v___x_4609_ = lean_nat_sub(v_nargs_4604_, v___x_4608_);
lean_dec(v_nargs_4604_);
v___x_4610_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4552_, v___x_4607_, v___x_4609_);
v___x_4611_ = lean_array_push(v___x_4610_, v_a_4601_);
v___x_4612_ = l_Lean_mkAppN(v___x_4605_, v___x_4611_);
lean_dec_ref(v___x_4611_);
lean_inc(v_val_4394_);
v___x_4613_ = l_Lean_LocalDecl_toExpr(v_val_4394_);
lean_inc(v___y_4547_);
lean_inc_ref(v___y_4545_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
v___x_4614_ = l_Lean_Meta_mkAbsurd(v_a_4603_, v___x_4613_, v___x_4612_, v___y_4549_, v___y_4550_, v___y_4545_, v___y_4547_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4634_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4617_ = v___x_4614_;
v_isShared_4618_ = v_isSharedCheck_4634_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4614_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4634_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; 
lean_inc(v_mvarId_4363_);
v___x_4619_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4363_, v_a_4615_, v___y_4550_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4631_; 
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4545_);
lean_dec_ref(v___x_4514_);
lean_dec(v_val_4394_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4631_ == 0)
{
lean_object* v_unused_4632_; 
v_unused_4632_ = lean_ctor_get(v___x_4619_, 0);
lean_dec(v_unused_4632_);
v___x_4621_ = v___x_4619_;
v_isShared_4622_ = v_isSharedCheck_4631_;
goto v_resetjp_4620_;
}
else
{
lean_dec(v___x_4619_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4631_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4623_; lean_object* v___x_4625_; 
v___x_4623_ = lean_box(v___x_4373_);
if (v_isShared_4622_ == 0)
{
lean_ctor_set_tag(v___x_4621_, 1);
lean_ctor_set(v___x_4621_, 0, v___x_4623_);
v___x_4625_ = v___x_4621_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_object* v___x_4626_; lean_object* v___x_4628_; 
v___x_4626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
lean_ctor_set(v___x_4626_, 1, v___x_4398_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4626_);
v___x_4628_ = v___x_4617_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4626_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
v_a_4380_ = v___x_4628_;
goto v___jp_4379_;
}
}
}
}
else
{
lean_object* v_a_4633_; 
lean_del_object(v___x_4617_);
v_a_4633_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4633_);
lean_dec_ref(v___x_4619_);
v___y_4535_ = v___y_4545_;
v___y_4536_ = v___y_4546_;
v___y_4537_ = v___y_4547_;
v___y_4538_ = v___y_4548_;
v___y_4539_ = v___y_4549_;
v___y_4540_ = v___y_4550_;
v_a_4541_ = v_a_4633_;
goto v___jp_4534_;
}
}
}
else
{
lean_object* v_a_4635_; 
v_a_4635_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_a_4635_);
lean_dec_ref(v___x_4614_);
v___y_4535_ = v___y_4545_;
v___y_4536_ = v___y_4546_;
v___y_4537_ = v___y_4547_;
v___y_4538_ = v___y_4548_;
v___y_4539_ = v___y_4549_;
v___y_4540_ = v___y_4550_;
v_a_4541_ = v_a_4635_;
goto v___jp_4534_;
}
}
else
{
lean_object* v_a_4636_; 
lean_dec(v_a_4601_);
lean_dec(v_a_4552_);
v_a_4636_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_a_4636_);
lean_dec_ref(v___x_4602_);
v___y_4535_ = v___y_4545_;
v___y_4536_ = v___y_4546_;
v___y_4537_ = v___y_4547_;
v___y_4538_ = v___y_4548_;
v___y_4539_ = v___y_4549_;
v___y_4540_ = v___y_4550_;
v_a_4541_ = v_a_4636_;
goto v___jp_4534_;
}
}
else
{
lean_object* v_a_4637_; 
lean_dec(v_a_4552_);
v_a_4637_ = lean_ctor_get(v___x_4600_, 0);
lean_inc(v_a_4637_);
lean_dec_ref(v___x_4600_);
v___y_4535_ = v___y_4545_;
v___y_4536_ = v___y_4546_;
v___y_4537_ = v___y_4547_;
v___y_4538_ = v___y_4548_;
v___y_4539_ = v___y_4549_;
v___y_4540_ = v___y_4550_;
v_a_4541_ = v_a_4637_;
goto v___jp_4534_;
}
}
}
else
{
lean_object* v_a_4638_; 
lean_dec(v_a_4552_);
v_a_4638_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4638_);
lean_dec_ref(v___x_4596_);
v___y_4535_ = v___y_4545_;
v___y_4536_ = v___y_4546_;
v___y_4537_ = v___y_4547_;
v___y_4538_ = v___y_4548_;
v___y_4539_ = v___y_4549_;
v___y_4540_ = v___y_4550_;
v_a_4541_ = v_a_4638_;
goto v___jp_4534_;
}
}
}
}
else
{
lean_object* v_a_4641_; 
v_a_4641_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4641_);
lean_dec_ref(v___x_4551_);
v___y_4535_ = v___y_4545_;
v___y_4536_ = v___y_4546_;
v___y_4537_ = v___y_4547_;
v___y_4538_ = v___y_4548_;
v___y_4539_ = v___y_4549_;
v___y_4540_ = v___y_4550_;
v_a_4541_ = v_a_4641_;
goto v___jp_4534_;
}
}
v___jp_4642_:
{
if (v___y_4649_ == 0)
{
v___y_4516_ = v___y_4644_;
v___y_4517_ = v___y_4646_;
v___y_4518_ = v___y_4647_;
v___y_4519_ = v___y_4648_;
v___y_4520_ = v___y_4643_;
v___y_4521_ = v___y_4645_;
goto v___jp_4515_;
}
else
{
v___y_4545_ = v___y_4643_;
v___y_4546_ = v___y_4644_;
v___y_4547_ = v___y_4645_;
v___y_4548_ = v___y_4646_;
v___y_4549_ = v___y_4647_;
v___y_4550_ = v___y_4648_;
goto v___jp_4544_;
}
}
v___jp_4650_:
{
if (v___y_4658_ == 0)
{
lean_dec_ref(v___y_4652_);
v___y_4643_ = v___y_4651_;
v___y_4644_ = v___y_4653_;
v___y_4645_ = v___y_4654_;
v___y_4646_ = v___y_4655_;
v___y_4647_ = v___y_4656_;
v___y_4648_ = v___y_4657_;
v___y_4649_ = v___x_4469_;
goto v___jp_4642_;
}
else
{
uint8_t v___x_4659_; 
v___x_4659_ = l_Lean_Expr_hasFVar(v___y_4652_);
lean_dec_ref(v___y_4652_);
if (v___x_4659_ == 0)
{
v___y_4545_ = v___y_4651_;
v___y_4546_ = v___y_4653_;
v___y_4547_ = v___y_4654_;
v___y_4548_ = v___y_4655_;
v___y_4549_ = v___y_4656_;
v___y_4550_ = v___y_4657_;
goto v___jp_4544_;
}
else
{
v___y_4643_ = v___y_4651_;
v___y_4644_ = v___y_4653_;
v___y_4645_ = v___y_4654_;
v___y_4646_ = v___y_4655_;
v___y_4647_ = v___y_4656_;
v___y_4648_ = v___y_4657_;
v___y_4649_ = v___x_4469_;
goto v___jp_4642_;
}
}
}
v___jp_4660_:
{
lean_object* v___x_4668_; 
lean_inc_ref(v___x_4514_);
v___x_4668_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4514_, v___y_4666_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; uint8_t v___x_4670_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref(v___x_4668_);
v___x_4670_ = l_Lean_Expr_hasMVar(v_a_4669_);
if (v___x_4670_ == 0)
{
v___y_4651_ = v___y_4661_;
v___y_4652_ = v_a_4669_;
v___y_4653_ = v___y_4662_;
v___y_4654_ = v___y_4663_;
v___y_4655_ = v___y_4664_;
v___y_4656_ = v___y_4665_;
v___y_4657_ = v___y_4666_;
v___y_4658_ = v___y_4667_;
goto v___jp_4650_;
}
else
{
v___y_4651_ = v___y_4661_;
v___y_4652_ = v_a_4669_;
v___y_4653_ = v___y_4662_;
v___y_4654_ = v___y_4663_;
v___y_4655_ = v___y_4664_;
v___y_4656_ = v___y_4665_;
v___y_4657_ = v___y_4666_;
v___y_4658_ = v___x_4469_;
goto v___jp_4650_;
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4661_);
lean_dec_ref(v___x_4514_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4671_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4668_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4668_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
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
v___jp_4679_:
{
if (v___y_4686_ == 0)
{
v___y_4516_ = v___y_4681_;
v___y_4517_ = v___y_4683_;
v___y_4518_ = v___y_4684_;
v___y_4519_ = v___y_4685_;
v___y_4520_ = v___y_4680_;
v___y_4521_ = v___y_4682_;
goto v___jp_4515_;
}
else
{
v___y_4661_ = v___y_4680_;
v___y_4662_ = v___y_4681_;
v___y_4663_ = v___y_4682_;
v___y_4664_ = v___y_4683_;
v___y_4665_ = v___y_4684_;
v___y_4666_ = v___y_4685_;
v___y_4667_ = v___y_4686_;
goto v___jp_4660_;
}
}
v___jp_4687_:
{
uint8_t v_useDecide_4694_; 
v_useDecide_4694_ = lean_ctor_get_uint8(v_config_4362_, sizeof(void*)*1);
if (v_useDecide_4694_ == 0)
{
v___y_4680_ = v___y_4692_;
v___y_4681_ = v_isHEq_4689_;
v___y_4682_ = v___y_4693_;
v___y_4683_ = v___y_4688_;
v___y_4684_ = v___y_4690_;
v___y_4685_ = v___y_4691_;
v___y_4686_ = v___x_4469_;
goto v___jp_4679_;
}
else
{
uint8_t v___x_4695_; 
v___x_4695_ = l_Lean_Expr_hasFVar(v___x_4514_);
if (v___x_4695_ == 0)
{
v___y_4661_ = v___y_4692_;
v___y_4662_ = v_isHEq_4689_;
v___y_4663_ = v___y_4693_;
v___y_4664_ = v___y_4688_;
v___y_4665_ = v___y_4690_;
v___y_4666_ = v___y_4691_;
v___y_4667_ = v_useDecide_4694_;
goto v___jp_4660_;
}
else
{
v___y_4680_ = v___y_4692_;
v___y_4681_ = v_isHEq_4689_;
v___y_4682_ = v___y_4693_;
v___y_4683_ = v___y_4688_;
v___y_4684_ = v___y_4690_;
v___y_4685_ = v___y_4691_;
v___y_4686_ = v___x_4469_;
goto v___jp_4679_;
}
}
}
v___jp_4696_:
{
lean_object* v___x_4704_; 
lean_inc(v___y_4702_);
lean_inc_ref(v___y_4697_);
lean_inc(v___y_4703_);
lean_inc_ref(v___y_4700_);
v___x_4704_ = l_Lean_Meta_isExprDefEq(v___y_4699_, v___y_4698_, v___y_4700_, v___y_4703_, v___y_4697_, v___y_4702_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v_a_4705_; uint8_t v___x_4706_; 
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc(v_a_4705_);
lean_dec_ref(v___x_4704_);
v___x_4706_ = lean_unbox(v_a_4705_);
lean_dec(v_a_4705_);
if (v___x_4706_ == 0)
{
v___y_4688_ = v___y_4701_;
v_isHEq_4689_ = v___x_4373_;
v___y_4690_ = v___y_4700_;
v___y_4691_ = v___y_4703_;
v___y_4692_ = v___y_4697_;
v___y_4693_ = v___y_4702_;
goto v___jp_4687_;
}
else
{
lean_object* v___x_4707_; 
lean_dec_ref(v___x_4514_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v_config_4362_);
lean_inc(v_mvarId_4363_);
v___x_4707_ = l_Lean_MVarId_getType(v_mvarId_4363_, v___y_4700_, v___y_4703_, v___y_4697_, v___y_4702_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4708_);
lean_dec_ref(v___x_4707_);
v___x_4709_ = l_Lean_LocalDecl_toExpr(v_val_4394_);
lean_inc(v___y_4702_);
lean_inc_ref(v___y_4697_);
lean_inc(v___y_4703_);
lean_inc_ref(v___y_4700_);
v___x_4710_ = l_Lean_Meta_mkEqOfHEq(v___x_4709_, v___x_4373_, v___y_4700_, v___y_4703_, v___y_4697_, v___y_4702_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v___x_4712_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4711_);
lean_dec_ref(v___x_4710_);
lean_inc(v___y_4703_);
v___x_4712_ = l_Lean_Meta_mkNoConfusion(v_a_4708_, v_a_4711_, v___y_4700_, v___y_4703_, v___y_4697_, v___y_4702_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; lean_object* v___x_4714_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
lean_inc(v_a_4713_);
lean_dec_ref(v___x_4712_);
v___x_4714_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4363_, v_a_4713_, v___y_4703_);
lean_dec(v___y_4703_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
lean_dec_ref(v___x_4714_);
v___x_4715_ = lean_box(v___x_4373_);
v___x_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
v___x_4717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4716_);
lean_ctor_set(v___x_4717_, 1, v___x_4398_);
v___x_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4717_);
v_a_4380_ = v___x_4718_;
goto v___jp_4379_;
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
v_a_4719_ = lean_ctor_get(v___x_4714_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4714_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4714_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
lean_dec(v___y_4703_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4727_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4729_ = v___x_4712_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4712_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
lean_dec(v_a_4708_);
lean_dec(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4700_);
lean_dec_ref(v___y_4697_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4735_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4710_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4710_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
lean_dec(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4700_);
lean_dec_ref(v___y_4697_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4743_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___x_4707_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4707_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
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
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
lean_dec(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4700_);
lean_dec_ref(v___y_4697_);
lean_dec_ref(v___x_4514_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4751_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4704_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4704_);
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
v___jp_4759_:
{
lean_object* v___x_4765_; 
lean_inc(v___y_4764_);
lean_inc_ref(v___y_4763_);
lean_inc(v___y_4762_);
lean_inc_ref(v___y_4761_);
lean_inc_ref(v___x_4514_);
v___x_4765_ = l_Lean_Meta_matchHEq_x3f(v___x_4514_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4766_);
lean_dec_ref(v___x_4765_);
if (lean_obj_tag(v_a_4766_) == 1)
{
lean_object* v_val_4767_; lean_object* v_snd_4768_; lean_object* v_snd_4769_; lean_object* v_fst_4770_; lean_object* v_fst_4771_; lean_object* v_fst_4772_; lean_object* v_snd_4773_; lean_object* v___x_4774_; 
v_val_4767_ = lean_ctor_get(v_a_4766_, 0);
lean_inc(v_val_4767_);
lean_dec_ref(v_a_4766_);
v_snd_4768_ = lean_ctor_get(v_val_4767_, 1);
lean_inc(v_snd_4768_);
v_snd_4769_ = lean_ctor_get(v_snd_4768_, 1);
lean_inc(v_snd_4769_);
v_fst_4770_ = lean_ctor_get(v_val_4767_, 0);
lean_inc(v_fst_4770_);
lean_dec(v_val_4767_);
v_fst_4771_ = lean_ctor_get(v_snd_4768_, 0);
lean_inc(v_fst_4771_);
lean_dec(v_snd_4768_);
v_fst_4772_ = lean_ctor_get(v_snd_4769_, 0);
lean_inc(v_fst_4772_);
v_snd_4773_ = lean_ctor_get(v_snd_4769_, 1);
lean_inc(v_snd_4773_);
lean_dec(v_snd_4769_);
lean_inc(v___y_4764_);
lean_inc_ref(v___y_4763_);
lean_inc(v___y_4762_);
lean_inc_ref(v___y_4761_);
v___x_4774_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4771_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_object* v_a_4775_; 
v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
lean_inc(v_a_4775_);
lean_dec_ref(v___x_4774_);
if (lean_obj_tag(v_a_4775_) == 1)
{
lean_object* v_val_4776_; lean_object* v___x_4777_; 
v_val_4776_ = lean_ctor_get(v_a_4775_, 0);
lean_inc(v_val_4776_);
lean_dec_ref(v_a_4775_);
lean_inc(v___y_4764_);
lean_inc_ref(v___y_4763_);
lean_inc(v___y_4762_);
lean_inc_ref(v___y_4761_);
v___x_4777_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4773_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref(v___x_4777_);
if (lean_obj_tag(v_a_4778_) == 1)
{
lean_object* v_toConstantVal_4779_; lean_object* v_val_4780_; lean_object* v_toConstantVal_4781_; lean_object* v_name_4782_; lean_object* v_name_4783_; uint8_t v___x_4784_; 
v_toConstantVal_4779_ = lean_ctor_get(v_val_4776_, 0);
lean_inc_ref(v_toConstantVal_4779_);
lean_dec(v_val_4776_);
v_val_4780_ = lean_ctor_get(v_a_4778_, 0);
lean_inc(v_val_4780_);
lean_dec_ref(v_a_4778_);
v_toConstantVal_4781_ = lean_ctor_get(v_val_4780_, 0);
lean_inc_ref(v_toConstantVal_4781_);
lean_dec(v_val_4780_);
v_name_4782_ = lean_ctor_get(v_toConstantVal_4779_, 0);
lean_inc(v_name_4782_);
lean_dec_ref(v_toConstantVal_4779_);
v_name_4783_ = lean_ctor_get(v_toConstantVal_4781_, 0);
lean_inc(v_name_4783_);
lean_dec_ref(v_toConstantVal_4781_);
v___x_4784_ = lean_name_eq(v_name_4782_, v_name_4783_);
lean_dec(v_name_4783_);
lean_dec(v_name_4782_);
if (v___x_4784_ == 0)
{
v___y_4697_ = v___y_4763_;
v___y_4698_ = v_fst_4772_;
v___y_4699_ = v_fst_4770_;
v___y_4700_ = v___y_4761_;
v___y_4701_ = v_isEq_4760_;
v___y_4702_ = v___y_4764_;
v___y_4703_ = v___y_4762_;
goto v___jp_4696_;
}
else
{
if (v___x_4469_ == 0)
{
lean_dec(v_fst_4772_);
lean_dec(v_fst_4770_);
v___y_4688_ = v_isEq_4760_;
v_isHEq_4689_ = v___x_4373_;
v___y_4690_ = v___y_4761_;
v___y_4691_ = v___y_4762_;
v___y_4692_ = v___y_4763_;
v___y_4693_ = v___y_4764_;
goto v___jp_4687_;
}
else
{
v___y_4697_ = v___y_4763_;
v___y_4698_ = v_fst_4772_;
v___y_4699_ = v_fst_4770_;
v___y_4700_ = v___y_4761_;
v___y_4701_ = v_isEq_4760_;
v___y_4702_ = v___y_4764_;
v___y_4703_ = v___y_4762_;
goto v___jp_4696_;
}
}
}
else
{
lean_dec(v_a_4778_);
lean_dec(v_val_4776_);
lean_dec(v_fst_4772_);
lean_dec(v_fst_4770_);
v___y_4688_ = v_isEq_4760_;
v_isHEq_4689_ = v___x_4373_;
v___y_4690_ = v___y_4761_;
v___y_4691_ = v___y_4762_;
v___y_4692_ = v___y_4763_;
v___y_4693_ = v___y_4764_;
goto v___jp_4687_;
}
}
else
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4792_; 
lean_dec(v_val_4776_);
lean_dec(v_fst_4772_);
lean_dec(v_fst_4770_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec_ref(v___x_4514_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4785_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4787_ = v___x_4777_;
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4777_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4790_; 
if (v_isShared_4788_ == 0)
{
v___x_4790_ = v___x_4787_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4785_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
else
{
lean_dec(v_a_4775_);
lean_dec(v_snd_4773_);
lean_dec(v_fst_4772_);
lean_dec(v_fst_4770_);
v___y_4688_ = v_isEq_4760_;
v_isHEq_4689_ = v___x_4373_;
v___y_4690_ = v___y_4761_;
v___y_4691_ = v___y_4762_;
v___y_4692_ = v___y_4763_;
v___y_4693_ = v___y_4764_;
goto v___jp_4687_;
}
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_dec(v_snd_4773_);
lean_dec(v_fst_4772_);
lean_dec(v_fst_4770_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec_ref(v___x_4514_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4793_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4774_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4774_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
else
{
lean_dec(v_a_4766_);
v___y_4688_ = v_isEq_4760_;
v_isHEq_4689_ = v___x_4469_;
v___y_4690_ = v___y_4761_;
v___y_4691_ = v___y_4762_;
v___y_4692_ = v___y_4763_;
v___y_4693_ = v___y_4764_;
goto v___jp_4687_;
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec_ref(v___x_4514_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4801_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4765_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4765_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
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
v___jp_4809_:
{
lean_object* v___x_4814_; 
lean_inc(v___y_4813_);
lean_inc_ref(v___y_4812_);
lean_inc(v___y_4811_);
lean_inc_ref(v___y_4810_);
lean_inc_ref(v___x_4514_);
v___x_4814_ = l_Lean_Meta_matchEq_x3f(v___x_4514_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_a_4815_; 
v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_a_4815_);
lean_dec_ref(v___x_4814_);
if (lean_obj_tag(v_a_4815_) == 1)
{
lean_object* v_val_4816_; lean_object* v_snd_4817_; lean_object* v_fst_4818_; lean_object* v_snd_4819_; lean_object* v___x_4820_; 
v_val_4816_ = lean_ctor_get(v_a_4815_, 0);
lean_inc(v_val_4816_);
lean_dec_ref(v_a_4815_);
v_snd_4817_ = lean_ctor_get(v_val_4816_, 1);
lean_inc(v_snd_4817_);
lean_dec(v_val_4816_);
v_fst_4818_ = lean_ctor_get(v_snd_4817_, 0);
lean_inc(v_fst_4818_);
v_snd_4819_ = lean_ctor_get(v_snd_4817_, 1);
lean_inc(v_snd_4819_);
lean_dec(v_snd_4817_);
lean_inc(v___y_4813_);
lean_inc_ref(v___y_4812_);
lean_inc(v___y_4811_);
lean_inc_ref(v___y_4810_);
v___x_4820_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4818_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_a_4821_);
lean_dec_ref(v___x_4820_);
if (lean_obj_tag(v_a_4821_) == 1)
{
lean_object* v_val_4822_; lean_object* v___x_4823_; 
v_val_4822_ = lean_ctor_get(v_a_4821_, 0);
lean_inc(v_val_4822_);
lean_dec_ref(v_a_4821_);
lean_inc(v___y_4813_);
lean_inc_ref(v___y_4812_);
lean_inc(v___y_4811_);
lean_inc_ref(v___y_4810_);
v___x_4823_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4819_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc(v_a_4824_);
lean_dec_ref(v___x_4823_);
if (lean_obj_tag(v_a_4824_) == 1)
{
lean_object* v_toConstantVal_4825_; lean_object* v_val_4826_; lean_object* v_toConstantVal_4827_; lean_object* v_name_4828_; lean_object* v_name_4829_; uint8_t v___x_4830_; 
v_toConstantVal_4825_ = lean_ctor_get(v_val_4822_, 0);
lean_inc_ref(v_toConstantVal_4825_);
lean_dec(v_val_4822_);
v_val_4826_ = lean_ctor_get(v_a_4824_, 0);
lean_inc(v_val_4826_);
lean_dec_ref(v_a_4824_);
v_toConstantVal_4827_ = lean_ctor_get(v_val_4826_, 0);
lean_inc_ref(v_toConstantVal_4827_);
lean_dec(v_val_4826_);
v_name_4828_ = lean_ctor_get(v_toConstantVal_4825_, 0);
lean_inc(v_name_4828_);
lean_dec_ref(v_toConstantVal_4825_);
v_name_4829_ = lean_ctor_get(v_toConstantVal_4827_, 0);
lean_inc(v_name_4829_);
lean_dec_ref(v_toConstantVal_4827_);
v___x_4830_ = lean_name_eq(v_name_4828_, v_name_4829_);
lean_dec(v_name_4829_);
lean_dec(v_name_4828_);
if (v___x_4830_ == 0)
{
lean_dec_ref(v___x_4514_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v_config_4362_);
v___y_4400_ = v___y_4810_;
v___y_4401_ = v___y_4811_;
v___y_4402_ = v___y_4813_;
v___y_4403_ = v___y_4812_;
goto v___jp_4399_;
}
else
{
if (v___x_4469_ == 0)
{
lean_del_object(v___x_4396_);
v_isEq_4760_ = v___x_4373_;
v___y_4761_ = v___y_4810_;
v___y_4762_ = v___y_4811_;
v___y_4763_ = v___y_4812_;
v___y_4764_ = v___y_4813_;
goto v___jp_4759_;
}
else
{
lean_dec_ref(v___x_4514_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v_config_4362_);
v___y_4400_ = v___y_4810_;
v___y_4401_ = v___y_4811_;
v___y_4402_ = v___y_4813_;
v___y_4403_ = v___y_4812_;
goto v___jp_4399_;
}
}
}
else
{
lean_dec(v_a_4824_);
lean_dec(v_val_4822_);
lean_del_object(v___x_4396_);
v_isEq_4760_ = v___x_4373_;
v___y_4761_ = v___y_4810_;
v___y_4762_ = v___y_4811_;
v___y_4763_ = v___y_4812_;
v___y_4764_ = v___y_4813_;
goto v___jp_4759_;
}
}
else
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
lean_dec(v_val_4822_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4831_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4823_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4823_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
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
lean_dec(v_a_4821_);
lean_dec(v_snd_4819_);
lean_del_object(v___x_4396_);
v_isEq_4760_ = v___x_4373_;
v___y_4761_ = v___y_4810_;
v___y_4762_ = v___y_4811_;
v___y_4763_ = v___y_4812_;
v___y_4764_ = v___y_4813_;
goto v___jp_4759_;
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
lean_dec(v_snd_4819_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4839_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4820_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4820_);
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
else
{
lean_dec(v_a_4815_);
lean_del_object(v___x_4396_);
v_isEq_4760_ = v___x_4469_;
v___y_4761_ = v___y_4810_;
v___y_4762_ = v___y_4811_;
v___y_4763_ = v___y_4812_;
v___y_4764_ = v___y_4813_;
goto v___jp_4759_;
}
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4847_ = lean_ctor_get(v___x_4814_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4814_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4814_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
v___jp_4855_:
{
lean_object* v___x_4860_; 
lean_inc(v___y_4859_);
lean_inc_ref(v___y_4858_);
lean_inc(v___y_4857_);
lean_inc_ref(v___y_4856_);
lean_inc_ref(v___x_4514_);
v___x_4860_ = l_refutableHasNotBit_x3f(v___x_4514_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref(v___x_4860_);
if (lean_obj_tag(v_a_4861_) == 1)
{
lean_object* v_val_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4902_; 
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v_config_4362_);
v_val_4862_ = lean_ctor_get(v_a_4861_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v_a_4861_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4864_ = v_a_4861_;
v_isShared_4865_ = v_isSharedCheck_4902_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_val_4862_);
lean_dec(v_a_4861_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4902_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4866_; 
lean_inc(v_mvarId_4363_);
v___x_4866_ = l_Lean_MVarId_getType(v_mvarId_4363_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref(v___x_4866_);
v___x_4868_ = l_Lean_LocalDecl_toExpr(v_val_4394_);
lean_inc(v___y_4857_);
v___x_4869_ = l_Lean_Meta_mkAbsurd(v_a_4867_, v_val_4862_, v___x_4868_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4871_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc(v_a_4870_);
lean_dec_ref(v___x_4869_);
v___x_4871_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4363_, v_a_4870_, v___y_4857_);
lean_dec(v___y_4857_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v___x_4872_; lean_object* v___x_4874_; 
lean_dec_ref(v___x_4871_);
v___x_4872_ = lean_box(v___x_4373_);
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 0, v___x_4872_);
v___x_4874_ = v___x_4864_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4872_);
v___x_4874_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4875_, 0, v___x_4874_);
lean_ctor_set(v___x_4875_, 1, v___x_4398_);
v___x_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
v_a_4380_ = v___x_4876_;
goto v___jp_4379_;
}
}
else
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4885_; 
lean_del_object(v___x_4864_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
v_a_4878_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4880_ = v___x_4871_;
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4871_);
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
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
lean_del_object(v___x_4864_);
lean_dec(v___y_4857_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4886_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4869_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4869_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
else
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4901_; 
lean_del_object(v___x_4864_);
lean_dec(v_val_4862_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4894_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4896_ = v___x_4866_;
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4866_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4899_; 
if (v_isShared_4897_ == 0)
{
v___x_4899_ = v___x_4896_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v_a_4894_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
}
else
{
lean_object* v___x_4903_; 
lean_dec(v_a_4861_);
lean_inc(v___y_4859_);
lean_inc_ref(v___y_4858_);
lean_inc(v___y_4857_);
lean_inc_ref(v___y_4856_);
lean_inc_ref(v___x_4514_);
v___x_4903_ = l_Lean_Meta_matchNe_x3f(v___x_4514_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4903_) == 0)
{
lean_object* v_a_4904_; 
v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
lean_inc(v_a_4904_);
lean_dec_ref(v___x_4903_);
if (lean_obj_tag(v_a_4904_) == 1)
{
lean_object* v_val_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4975_; 
v_val_4905_ = lean_ctor_get(v_a_4904_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v_a_4904_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4907_ = v_a_4904_;
v_isShared_4908_ = v_isSharedCheck_4975_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_val_4905_);
lean_dec(v_a_4904_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4975_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v_snd_4909_; lean_object* v_fst_4910_; lean_object* v_snd_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4974_; 
v_snd_4909_ = lean_ctor_get(v_val_4905_, 1);
lean_inc(v_snd_4909_);
lean_dec(v_val_4905_);
v_fst_4910_ = lean_ctor_get(v_snd_4909_, 0);
v_snd_4911_ = lean_ctor_get(v_snd_4909_, 1);
v_isSharedCheck_4974_ = !lean_is_exclusive(v_snd_4909_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4913_ = v_snd_4909_;
v_isShared_4914_ = v_isSharedCheck_4974_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_snd_4911_);
lean_inc(v_fst_4910_);
lean_dec(v_snd_4909_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4974_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4915_; 
lean_inc(v___y_4859_);
lean_inc_ref(v___y_4858_);
lean_inc(v___y_4857_);
lean_inc_ref(v___y_4856_);
lean_inc(v_fst_4910_);
v___x_4915_ = l_Lean_Meta_isExprDefEq(v_fst_4910_, v_snd_4911_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; uint8_t v___x_4917_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref(v___x_4915_);
v___x_4917_ = lean_unbox(v_a_4916_);
lean_dec(v_a_4916_);
if (v___x_4917_ == 0)
{
lean_del_object(v___x_4913_);
lean_dec(v_fst_4910_);
lean_del_object(v___x_4907_);
v___y_4810_ = v___y_4856_;
v___y_4811_ = v___y_4857_;
v___y_4812_ = v___y_4858_;
v___y_4813_ = v___y_4859_;
goto v___jp_4809_;
}
else
{
lean_object* v___x_4918_; 
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v_config_4362_);
lean_inc(v_mvarId_4363_);
v___x_4918_ = l_Lean_MVarId_getType(v_mvarId_4363_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v_a_4919_; lean_object* v___x_4920_; 
v_a_4919_ = lean_ctor_get(v___x_4918_, 0);
lean_inc(v_a_4919_);
lean_dec_ref(v___x_4918_);
lean_inc(v___y_4859_);
lean_inc_ref(v___y_4858_);
lean_inc(v___y_4857_);
lean_inc_ref(v___y_4856_);
v___x_4920_ = l_Lean_Meta_mkEqRefl(v_fst_4910_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref(v___x_4920_);
v___x_4922_ = l_Lean_LocalDecl_toExpr(v_val_4394_);
lean_inc(v___y_4857_);
v___x_4923_ = l_Lean_Meta_mkAbsurd(v_a_4919_, v_a_4921_, v___x_4922_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; lean_object* v___x_4925_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4924_);
lean_dec_ref(v___x_4923_);
v___x_4925_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4363_, v_a_4924_, v___y_4857_);
lean_dec(v___y_4857_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4928_; 
lean_dec_ref(v___x_4925_);
v___x_4926_ = lean_box(v___x_4373_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4926_);
v___x_4928_ = v___x_4907_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4926_);
v___x_4928_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
lean_object* v___x_4930_; 
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 1, v___x_4398_);
lean_ctor_set(v___x_4913_, 0, v___x_4928_);
v___x_4930_ = v___x_4913_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v___x_4928_);
lean_ctor_set(v_reuseFailAlloc_4932_, 1, v___x_4398_);
v___x_4930_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v___x_4931_; 
v___x_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
v_a_4380_ = v___x_4931_;
goto v___jp_4379_;
}
}
}
else
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4941_; 
lean_del_object(v___x_4913_);
lean_del_object(v___x_4907_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
v_a_4934_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4941_ == 0)
{
v___x_4936_ = v___x_4925_;
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4925_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4939_; 
if (v_isShared_4937_ == 0)
{
v___x_4939_ = v___x_4936_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4934_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
}
else
{
lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4949_; 
lean_del_object(v___x_4913_);
lean_del_object(v___x_4907_);
lean_dec(v___y_4857_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4942_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4944_ = v___x_4923_;
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4923_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4947_; 
if (v_isShared_4945_ == 0)
{
v___x_4947_ = v___x_4944_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4942_);
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
lean_dec(v_a_4919_);
lean_del_object(v___x_4913_);
lean_del_object(v___x_4907_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4950_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4920_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4920_);
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
else
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4965_; 
lean_del_object(v___x_4913_);
lean_dec(v_fst_4910_);
lean_del_object(v___x_4907_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4958_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4960_ = v___x_4918_;
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4918_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4961_ == 0)
{
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4958_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
}
else
{
lean_object* v_a_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4973_; 
lean_del_object(v___x_4913_);
lean_dec(v_fst_4910_);
lean_del_object(v___x_4907_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4966_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4968_ = v___x_4915_;
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_a_4966_);
lean_dec(v___x_4915_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4971_; 
if (v_isShared_4969_ == 0)
{
v___x_4971_ = v___x_4968_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4966_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4904_);
v___y_4810_ = v___y_4856_;
v___y_4811_ = v___y_4857_;
v___y_4812_ = v___y_4858_;
v___y_4813_ = v___y_4859_;
goto v___jp_4809_;
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4976_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4903_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4903_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4991_; 
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec_ref(v___x_4514_);
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4984_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4986_ = v___x_4860_;
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4860_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
if (v_isShared_4987_ == 0)
{
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
}
else
{
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
v_a_4388_ = v___x_4440_;
goto v___jp_4387_;
}
v___jp_4399_:
{
lean_object* v___x_4404_; 
lean_inc(v_mvarId_4363_);
v___x_4404_ = l_Lean_MVarId_getType(v_mvarId_4363_, v___y_4400_, v___y_4401_, v___y_4403_, v___y_4402_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
lean_dec_ref(v___x_4404_);
v___x_4406_ = l_Lean_LocalDecl_toExpr(v_val_4394_);
lean_inc(v___y_4401_);
v___x_4407_ = l_Lean_Meta_mkNoConfusion(v_a_4405_, v___x_4406_, v___y_4400_, v___y_4401_, v___y_4403_, v___y_4402_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4409_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref(v___x_4407_);
v___x_4409_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4363_, v_a_4408_, v___y_4401_);
lean_dec(v___y_4401_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v___x_4410_; lean_object* v___x_4412_; 
lean_dec_ref(v___x_4409_);
v___x_4410_ = lean_box(v___x_4373_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4410_);
v___x_4412_ = v___x_4396_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4410_);
v___x_4412_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
lean_ctor_set(v___x_4413_, 1, v___x_4398_);
v___x_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4413_);
v_a_4380_ = v___x_4414_;
goto v___jp_4379_;
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_del_object(v___x_4396_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
v_a_4416_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4409_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4409_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v___y_4401_);
lean_del_object(v___x_4396_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4424_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4407_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4407_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_del_object(v___x_4396_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v_mvarId_4363_);
v_a_4432_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4404_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4404_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
v___jp_4441_:
{
lean_object* v_searchFuel_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v_searchFuel_4446_ = lean_ctor_get(v_config_4362_, 0);
v___x_4447_ = l_Lean_LocalDecl_fvarId(v_val_4394_);
lean_dec(v_val_4394_);
lean_inc(v_searchFuel_4446_);
lean_inc(v_mvarId_4363_);
v___x_4448_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_4363_, v___x_4447_, v_searchFuel_4446_, v___y_4442_, v___y_4445_, v___y_4444_, v___y_4443_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v_a_4449_; uint8_t v___x_4450_; 
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_a_4449_);
lean_dec_ref(v___x_4448_);
v___x_4450_ = lean_unbox(v_a_4449_);
lean_dec(v_a_4449_);
if (v___x_4450_ == 0)
{
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
v_a_4388_ = v___x_4440_;
goto v___jp_4387_;
}
else
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v___x_4451_ = lean_box(v___x_4373_);
v___x_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
v___x_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
lean_ctor_set(v___x_4453_, 1, v___x_4398_);
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
v_a_4380_ = v___x_4454_;
goto v___jp_4379_;
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4455_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4448_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4448_);
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
v___jp_4463_:
{
if (v___y_4468_ == 0)
{
lean_dec(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
v_a_4388_ = v___x_4440_;
goto v___jp_4387_;
}
else
{
v___y_4442_ = v___y_4464_;
v___y_4443_ = v___y_4466_;
v___y_4444_ = v___y_4465_;
v___y_4445_ = v___y_4467_;
goto v___jp_4441_;
}
}
v___jp_4470_:
{
if (v___y_4472_ == 0)
{
v___y_4442_ = v___y_4471_;
v___y_4443_ = v___y_4474_;
v___y_4444_ = v___y_4473_;
v___y_4445_ = v___y_4475_;
goto v___jp_4441_;
}
else
{
v___y_4464_ = v___y_4471_;
v___y_4465_ = v___y_4473_;
v___y_4466_ = v___y_4474_;
v___y_4467_ = v___y_4475_;
v___y_4468_ = v___x_4469_;
goto v___jp_4463_;
}
}
v___jp_4476_:
{
if (v___y_4482_ == 0)
{
v___y_4464_ = v___y_4477_;
v___y_4465_ = v___y_4480_;
v___y_4466_ = v___y_4479_;
v___y_4467_ = v___y_4481_;
v___y_4468_ = v___x_4469_;
goto v___jp_4463_;
}
else
{
v___y_4471_ = v___y_4477_;
v___y_4472_ = v___y_4478_;
v___y_4473_ = v___y_4480_;
v___y_4474_ = v___y_4479_;
v___y_4475_ = v___y_4481_;
goto v___jp_4470_;
}
}
v___jp_4483_:
{
uint8_t v_emptyType_4490_; 
v_emptyType_4490_ = lean_ctor_get_uint8(v_config_4362_, sizeof(void*)*1 + 1);
if (v_emptyType_4490_ == 0)
{
v___y_4477_ = v___y_4486_;
v___y_4478_ = v___y_4484_;
v___y_4479_ = v___y_4489_;
v___y_4480_ = v___y_4488_;
v___y_4481_ = v___y_4487_;
v___y_4482_ = v___x_4469_;
goto v___jp_4476_;
}
else
{
if (v___y_4485_ == 0)
{
v___y_4471_ = v___y_4486_;
v___y_4472_ = v___y_4484_;
v___y_4473_ = v___y_4488_;
v___y_4474_ = v___y_4489_;
v___y_4475_ = v___y_4487_;
goto v___jp_4470_;
}
else
{
v___y_4477_ = v___y_4486_;
v___y_4478_ = v___y_4484_;
v___y_4479_ = v___y_4489_;
v___y_4480_ = v___y_4488_;
v___y_4481_ = v___y_4487_;
v___y_4482_ = v___x_4469_;
goto v___jp_4476_;
}
}
}
v___jp_4491_:
{
if (v___y_4498_ == 0)
{
v___y_4484_ = v___y_4494_;
v___y_4485_ = v___y_4496_;
v___y_4486_ = v___y_4493_;
v___y_4487_ = v___y_4497_;
v___y_4488_ = v___y_4495_;
v___y_4489_ = v___y_4492_;
goto v___jp_4483_;
}
else
{
lean_object* v___x_4499_; 
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4495_);
lean_inc(v___y_4497_);
lean_inc_ref(v___y_4493_);
lean_inc(v_val_4394_);
lean_inc(v_mvarId_4363_);
v___x_4499_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_4363_, v_val_4394_, v___y_4493_, v___y_4497_, v___y_4495_, v___y_4492_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; uint8_t v___x_4501_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
lean_inc(v_a_4500_);
lean_dec_ref(v___x_4499_);
v___x_4501_ = lean_unbox(v_a_4500_);
lean_dec(v_a_4500_);
if (v___x_4501_ == 0)
{
v___y_4484_ = v___y_4494_;
v___y_4485_ = v___y_4496_;
v___y_4486_ = v___y_4493_;
v___y_4487_ = v___y_4497_;
v___y_4488_ = v___y_4495_;
v___y_4489_ = v___y_4492_;
goto v___jp_4483_;
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4495_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec(v_val_4394_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v___x_4502_ = lean_box(v___x_4373_);
v___x_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
v___x_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
lean_ctor_set(v___x_4504_, 1, v___x_4398_);
v___x_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
v_a_4380_ = v___x_4505_;
goto v___jp_4379_;
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4495_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec(v_val_4394_);
lean_del_object(v___x_4377_);
lean_dec(v_snd_4375_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v_mvarId_4363_);
lean_dec_ref(v_config_4362_);
v_a_4506_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4499_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4499_);
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
}
}
}
v___jp_4379_:
{
lean_object* v___x_4381_; lean_object* v___x_4383_; 
v___x_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4381_, 0, v_a_4380_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 0, v___x_4381_);
v___x_4383_ = v___x_4377_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4381_);
lean_ctor_set(v_reuseFailAlloc_4385_, 1, v_snd_4375_);
v___x_4383_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
lean_object* v___x_4384_; 
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
return v___x_4384_;
}
}
v___jp_4387_:
{
lean_object* v___x_4389_; size_t v___x_4390_; size_t v___x_4391_; lean_object* v___x_4392_; 
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4386_);
lean_ctor_set(v___x_4389_, 1, v_a_4388_);
v___x_4390_ = ((size_t)1ULL);
v___x_4391_ = lean_usize_add(v_i_4366_, v___x_4390_);
v___x_4392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_4362_, v_mvarId_4363_, v_as_4364_, v_sz_4365_, v___x_4391_, v___x_4389_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
return v___x_4392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_5065_, lean_object* v_mvarId_5066_, lean_object* v_as_5067_, lean_object* v_sz_5068_, lean_object* v_i_5069_, lean_object* v_b_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
size_t v_sz_boxed_5076_; size_t v_i_boxed_5077_; lean_object* v_res_5078_; 
v_sz_boxed_5076_ = lean_unbox_usize(v_sz_5068_);
lean_dec(v_sz_5068_);
v_i_boxed_5077_ = lean_unbox_usize(v_i_5069_);
lean_dec(v_i_5069_);
v_res_5078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_5065_, v_mvarId_5066_, v_as_5067_, v_sz_boxed_5076_, v_i_boxed_5077_, v_b_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_);
lean_dec_ref(v_as_5067_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_config_5079_, lean_object* v_mvarId_5080_, lean_object* v_inh_5081_, lean_object* v_n_5082_, lean_object* v_b_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
if (lean_obj_tag(v_n_5082_) == 0)
{
lean_object* v_cs_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5123_; 
v_cs_5089_ = lean_ctor_get(v_n_5082_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v_n_5082_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5091_ = v_n_5082_;
v_isShared_5092_ = v_isSharedCheck_5123_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_cs_5089_);
lean_dec(v_n_5082_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5123_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; size_t v_sz_5095_; size_t v___x_5096_; lean_object* v___x_5097_; 
v___x_5093_ = lean_box(0);
v___x_5094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
lean_ctor_set(v___x_5094_, 1, v_b_5083_);
v_sz_5095_ = lean_array_size(v_cs_5089_);
v___x_5096_ = ((size_t)0ULL);
v___x_5097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_config_5079_, v_mvarId_5080_, v_inh_5081_, v_cs_5089_, v_sz_5095_, v___x_5096_, v___x_5094_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
lean_dec_ref(v_cs_5089_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5114_; 
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5100_ = v___x_5097_;
v_isShared_5101_ = v_isSharedCheck_5114_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5097_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5114_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v_fst_5102_; 
v_fst_5102_ = lean_ctor_get(v_a_5098_, 0);
if (lean_obj_tag(v_fst_5102_) == 0)
{
lean_object* v_snd_5103_; lean_object* v___x_5105_; 
v_snd_5103_ = lean_ctor_get(v_a_5098_, 1);
lean_inc(v_snd_5103_);
lean_dec(v_a_5098_);
if (v_isShared_5092_ == 0)
{
lean_ctor_set_tag(v___x_5091_, 1);
lean_ctor_set(v___x_5091_, 0, v_snd_5103_);
v___x_5105_ = v___x_5091_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_snd_5103_);
v___x_5105_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
lean_object* v___x_5107_; 
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 0, v___x_5105_);
v___x_5107_ = v___x_5100_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5105_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
}
else
{
lean_object* v_val_5110_; lean_object* v___x_5112_; 
lean_inc_ref(v_fst_5102_);
lean_dec(v_a_5098_);
lean_del_object(v___x_5091_);
v_val_5110_ = lean_ctor_get(v_fst_5102_, 0);
lean_inc(v_val_5110_);
lean_dec_ref(v_fst_5102_);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 0, v_val_5110_);
v___x_5112_ = v___x_5100_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_val_5110_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
lean_del_object(v___x_5091_);
v_a_5115_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5097_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5097_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
}
}
else
{
lean_object* v_vs_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5158_; 
v_vs_5124_ = lean_ctor_get(v_n_5082_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_n_5082_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5126_ = v_n_5082_;
v_isShared_5127_ = v_isSharedCheck_5158_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_vs_5124_);
lean_dec(v_n_5082_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5158_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; size_t v_sz_5130_; size_t v___x_5131_; lean_object* v___x_5132_; 
v___x_5128_ = lean_box(0);
v___x_5129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
lean_ctor_set(v___x_5129_, 1, v_b_5083_);
v_sz_5130_ = lean_array_size(v_vs_5124_);
v___x_5131_ = ((size_t)0ULL);
v___x_5132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_5079_, v_mvarId_5080_, v_vs_5124_, v_sz_5130_, v___x_5131_, v___x_5129_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
lean_dec_ref(v_vs_5124_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5149_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5135_ = v___x_5132_;
v_isShared_5136_ = v_isSharedCheck_5149_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5132_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5149_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v_fst_5137_; 
v_fst_5137_ = lean_ctor_get(v_a_5133_, 0);
if (lean_obj_tag(v_fst_5137_) == 0)
{
lean_object* v_snd_5138_; lean_object* v___x_5140_; 
v_snd_5138_ = lean_ctor_get(v_a_5133_, 1);
lean_inc(v_snd_5138_);
lean_dec(v_a_5133_);
if (v_isShared_5127_ == 0)
{
lean_ctor_set(v___x_5126_, 0, v_snd_5138_);
v___x_5140_ = v___x_5126_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_snd_5138_);
v___x_5140_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
lean_object* v___x_5142_; 
if (v_isShared_5136_ == 0)
{
lean_ctor_set(v___x_5135_, 0, v___x_5140_);
v___x_5142_ = v___x_5135_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v___x_5140_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
else
{
lean_object* v_val_5145_; lean_object* v___x_5147_; 
lean_inc_ref(v_fst_5137_);
lean_dec(v_a_5133_);
lean_del_object(v___x_5126_);
v_val_5145_ = lean_ctor_get(v_fst_5137_, 0);
lean_inc(v_val_5145_);
lean_dec_ref(v_fst_5137_);
if (v_isShared_5136_ == 0)
{
lean_ctor_set(v___x_5135_, 0, v_val_5145_);
v___x_5147_ = v___x_5135_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_val_5145_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
}
else
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
lean_del_object(v___x_5126_);
v_a_5150_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v___x_5132_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5132_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_config_5159_, lean_object* v_mvarId_5160_, lean_object* v_inh_5161_, lean_object* v_as_5162_, size_t v_sz_5163_, size_t v_i_5164_, lean_object* v_b_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_){
_start:
{
uint8_t v___x_5171_; 
v___x_5171_ = lean_usize_dec_lt(v_i_5164_, v_sz_5163_);
if (v___x_5171_ == 0)
{
lean_object* v___x_5172_; 
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
lean_dec(v_mvarId_5160_);
lean_dec_ref(v_config_5159_);
v___x_5172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5172_, 0, v_b_5165_);
return v___x_5172_;
}
else
{
lean_object* v_snd_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5207_; 
v_snd_5173_ = lean_ctor_get(v_b_5165_, 1);
v_isSharedCheck_5207_ = !lean_is_exclusive(v_b_5165_);
if (v_isSharedCheck_5207_ == 0)
{
lean_object* v_unused_5208_; 
v_unused_5208_ = lean_ctor_get(v_b_5165_, 0);
lean_dec(v_unused_5208_);
v___x_5175_ = v_b_5165_;
v_isShared_5176_ = v_isSharedCheck_5207_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_snd_5173_);
lean_dec(v_b_5165_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5207_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v_a_5177_; lean_object* v___x_5178_; 
v_a_5177_ = lean_array_uget_borrowed(v_as_5162_, v_i_5164_);
lean_inc(v___y_5169_);
lean_inc_ref(v___y_5168_);
lean_inc(v___y_5167_);
lean_inc_ref(v___y_5166_);
lean_inc(v_snd_5173_);
lean_inc(v_a_5177_);
lean_inc(v_mvarId_5160_);
lean_inc_ref(v_config_5159_);
v___x_5178_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_config_5159_, v_mvarId_5160_, v_inh_5161_, v_a_5177_, v_snd_5173_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5198_; 
v_a_5179_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5181_ = v___x_5178_;
v_isShared_5182_ = v_isSharedCheck_5198_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5178_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5198_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
if (lean_obj_tag(v_a_5179_) == 0)
{
lean_object* v___x_5183_; lean_object* v___x_5185_; 
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
lean_dec(v_mvarId_5160_);
lean_dec_ref(v_config_5159_);
v___x_5183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5183_, 0, v_a_5179_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 0, v___x_5183_);
v___x_5185_ = v___x_5175_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v___x_5183_);
lean_ctor_set(v_reuseFailAlloc_5189_, 1, v_snd_5173_);
v___x_5185_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
lean_object* v___x_5187_; 
if (v_isShared_5182_ == 0)
{
lean_ctor_set(v___x_5181_, 0, v___x_5185_);
v___x_5187_ = v___x_5181_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5185_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5191_; lean_object* v___x_5193_; 
lean_del_object(v___x_5181_);
lean_dec(v_snd_5173_);
v_a_5190_ = lean_ctor_get(v_a_5179_, 0);
lean_inc(v_a_5190_);
lean_dec_ref(v_a_5179_);
v___x_5191_ = lean_box(0);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 1, v_a_5190_);
lean_ctor_set(v___x_5175_, 0, v___x_5191_);
v___x_5193_ = v___x_5175_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v___x_5191_);
lean_ctor_set(v_reuseFailAlloc_5197_, 1, v_a_5190_);
v___x_5193_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
size_t v___x_5194_; size_t v___x_5195_; 
v___x_5194_ = ((size_t)1ULL);
v___x_5195_ = lean_usize_add(v_i_5164_, v___x_5194_);
v_i_5164_ = v___x_5195_;
v_b_5165_ = v___x_5193_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5206_; 
lean_del_object(v___x_5175_);
lean_dec(v_snd_5173_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
lean_dec(v_mvarId_5160_);
lean_dec_ref(v_config_5159_);
v_a_5199_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5201_ = v___x_5178_;
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v___x_5178_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5204_; 
if (v_isShared_5202_ == 0)
{
v___x_5204_ = v___x_5201_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5199_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_config_5209_, lean_object* v_mvarId_5210_, lean_object* v_inh_5211_, lean_object* v_as_5212_, lean_object* v_sz_5213_, lean_object* v_i_5214_, lean_object* v_b_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
size_t v_sz_boxed_5221_; size_t v_i_boxed_5222_; lean_object* v_res_5223_; 
v_sz_boxed_5221_ = lean_unbox_usize(v_sz_5213_);
lean_dec(v_sz_5213_);
v_i_boxed_5222_ = lean_unbox_usize(v_i_5214_);
lean_dec(v_i_5214_);
v_res_5223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_config_5209_, v_mvarId_5210_, v_inh_5211_, v_as_5212_, v_sz_boxed_5221_, v_i_boxed_5222_, v_b_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_);
lean_dec_ref(v_as_5212_);
lean_dec_ref(v_inh_5211_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_config_5224_, lean_object* v_mvarId_5225_, lean_object* v_inh_5226_, lean_object* v_n_5227_, lean_object* v_b_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_config_5224_, v_mvarId_5225_, v_inh_5226_, v_n_5227_, v_b_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
lean_dec_ref(v_inh_5226_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_5235_, lean_object* v_mvarId_5236_, lean_object* v_t_5237_, lean_object* v_init_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
lean_object* v_root_5244_; lean_object* v_tail_5245_; lean_object* v___x_5246_; 
v_root_5244_ = lean_ctor_get(v_t_5237_, 0);
lean_inc_ref(v_root_5244_);
v_tail_5245_ = lean_ctor_get(v_t_5237_, 1);
lean_inc_ref(v_tail_5245_);
lean_dec_ref(v_t_5237_);
lean_inc(v___y_5242_);
lean_inc_ref(v___y_5241_);
lean_inc(v___y_5240_);
lean_inc_ref(v___y_5239_);
lean_inc_ref(v_init_5238_);
lean_inc(v_mvarId_5236_);
lean_inc_ref(v_config_5235_);
v___x_5246_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_config_5235_, v_mvarId_5236_, v_init_5238_, v_root_5244_, v_init_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
lean_dec_ref(v_init_5238_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5283_; 
v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5283_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5283_ == 0)
{
v___x_5249_ = v___x_5246_;
v_isShared_5250_ = v_isSharedCheck_5283_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5246_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5283_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
if (lean_obj_tag(v_a_5247_) == 0)
{
lean_object* v_a_5251_; lean_object* v___x_5253_; 
lean_dec_ref(v_tail_5245_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v_mvarId_5236_);
lean_dec_ref(v_config_5235_);
v_a_5251_ = lean_ctor_get(v_a_5247_, 0);
lean_inc(v_a_5251_);
lean_dec_ref(v_a_5247_);
if (v_isShared_5250_ == 0)
{
lean_ctor_set(v___x_5249_, 0, v_a_5251_);
v___x_5253_ = v___x_5249_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5251_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; size_t v_sz_5258_; size_t v___x_5259_; lean_object* v___x_5260_; 
lean_del_object(v___x_5249_);
v_a_5255_ = lean_ctor_get(v_a_5247_, 0);
lean_inc(v_a_5255_);
lean_dec_ref(v_a_5247_);
v___x_5256_ = lean_box(0);
v___x_5257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5257_, 0, v___x_5256_);
lean_ctor_set(v___x_5257_, 1, v_a_5255_);
v_sz_5258_ = lean_array_size(v_tail_5245_);
v___x_5259_ = ((size_t)0ULL);
v___x_5260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_5235_, v_mvarId_5236_, v_tail_5245_, v_sz_5258_, v___x_5259_, v___x_5257_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
lean_dec_ref(v_tail_5245_);
if (lean_obj_tag(v___x_5260_) == 0)
{
lean_object* v_a_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5274_; 
v_a_5261_ = lean_ctor_get(v___x_5260_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5263_ = v___x_5260_;
v_isShared_5264_ = v_isSharedCheck_5274_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_a_5261_);
lean_dec(v___x_5260_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5274_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v_fst_5265_; 
v_fst_5265_ = lean_ctor_get(v_a_5261_, 0);
if (lean_obj_tag(v_fst_5265_) == 0)
{
lean_object* v_snd_5266_; lean_object* v___x_5268_; 
v_snd_5266_ = lean_ctor_get(v_a_5261_, 1);
lean_inc(v_snd_5266_);
lean_dec(v_a_5261_);
if (v_isShared_5264_ == 0)
{
lean_ctor_set(v___x_5263_, 0, v_snd_5266_);
v___x_5268_ = v___x_5263_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_snd_5266_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
else
{
lean_object* v_val_5270_; lean_object* v___x_5272_; 
lean_inc_ref(v_fst_5265_);
lean_dec(v_a_5261_);
v_val_5270_ = lean_ctor_get(v_fst_5265_, 0);
lean_inc(v_val_5270_);
lean_dec_ref(v_fst_5265_);
if (v_isShared_5264_ == 0)
{
lean_ctor_set(v___x_5263_, 0, v_val_5270_);
v___x_5272_ = v___x_5263_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_val_5270_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
v_a_5275_ = lean_ctor_get(v___x_5260_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5277_ = v___x_5260_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5260_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5280_; 
if (v_isShared_5278_ == 0)
{
v___x_5280_ = v___x_5277_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5275_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
}
}
}
else
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5291_; 
lean_dec_ref(v_tail_5245_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v_mvarId_5236_);
lean_dec_ref(v_config_5235_);
v_a_5284_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5286_ = v___x_5246_;
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5246_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5289_; 
if (v_isShared_5287_ == 0)
{
v___x_5289_ = v___x_5286_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_5292_, lean_object* v_mvarId_5293_, lean_object* v_t_5294_, lean_object* v_init_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_5292_, v_mvarId_5293_, v_t_5294_, v_init_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_5302_, lean_object* v___x_5303_, lean_object* v_config_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v___x_5310_; 
lean_inc(v_mvarId_5302_);
v___x_5310_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_5302_, v___x_5303_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v___x_5311_; 
lean_dec_ref(v___x_5310_);
lean_inc(v___y_5308_);
lean_inc_ref(v___y_5307_);
lean_inc(v___y_5306_);
lean_inc_ref(v___y_5305_);
lean_inc(v_mvarId_5302_);
v___x_5311_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_5302_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5345_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5314_ = v___x_5311_;
v_isShared_5315_ = v_isSharedCheck_5345_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5311_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5345_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
uint8_t v___x_5316_; 
v___x_5316_ = lean_unbox(v_a_5312_);
if (v___x_5316_ == 0)
{
lean_object* v_lctx_5317_; lean_object* v_decls_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
lean_del_object(v___x_5314_);
v_lctx_5317_ = lean_ctor_get(v___y_5305_, 2);
v_decls_5318_ = lean_ctor_get(v_lctx_5317_, 1);
lean_inc_ref(v_decls_5318_);
v___x_5319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_5320_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_5304_, v_mvarId_5302_, v_decls_5318_, v___x_5319_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5333_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5323_ = v___x_5320_;
v_isShared_5324_ = v_isSharedCheck_5333_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5320_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5333_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v_fst_5325_; 
v_fst_5325_ = lean_ctor_get(v_a_5321_, 0);
lean_inc(v_fst_5325_);
lean_dec(v_a_5321_);
if (lean_obj_tag(v_fst_5325_) == 0)
{
lean_object* v___x_5327_; 
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 0, v_a_5312_);
v___x_5327_ = v___x_5323_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5312_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
else
{
lean_object* v_val_5329_; lean_object* v___x_5331_; 
lean_dec(v_a_5312_);
v_val_5329_ = lean_ctor_get(v_fst_5325_, 0);
lean_inc(v_val_5329_);
lean_dec_ref(v_fst_5325_);
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 0, v_val_5329_);
v___x_5331_ = v___x_5323_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_val_5329_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
}
}
else
{
lean_object* v_a_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5341_; 
lean_dec(v_a_5312_);
v_a_5334_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5341_ == 0)
{
v___x_5336_ = v___x_5320_;
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_a_5334_);
lean_dec(v___x_5320_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v___x_5339_; 
if (v_isShared_5337_ == 0)
{
v___x_5339_ = v___x_5336_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_a_5334_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
}
else
{
lean_object* v___x_5343_; 
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec_ref(v_config_5304_);
lean_dec(v_mvarId_5302_);
if (v_isShared_5315_ == 0)
{
v___x_5343_ = v___x_5314_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_a_5312_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
}
}
else
{
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec_ref(v_config_5304_);
lean_dec(v_mvarId_5302_);
return v___x_5311_;
}
}
else
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec_ref(v_config_5304_);
lean_dec(v_mvarId_5302_);
v_a_5346_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5348_ = v___x_5310_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5310_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5346_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_5354_, lean_object* v___x_5355_, lean_object* v_config_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_){
_start:
{
lean_object* v_res_5362_; 
v_res_5362_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_5354_, v___x_5355_, v_config_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
return v_res_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_5365_, lean_object* v_config_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v___x_5372_; lean_object* v___f_5373_; lean_object* v___x_5374_; 
v___x_5372_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_5365_);
v___f_5373_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5373_, 0, v_mvarId_5365_);
lean_closure_set(v___f_5373_, 1, v___x_5372_);
lean_closure_set(v___f_5373_, 2, v_config_5366_);
v___x_5374_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_5365_, v___f_5373_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_);
return v___x_5374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_5375_, lean_object* v_config_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_){
_start:
{
lean_object* v_res_5382_; 
v_res_5382_ = l_Lean_MVarId_contradictionCore(v_mvarId_5375_, v_config_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_);
return v_res_5382_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_5383_, lean_object* v_config_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_){
_start:
{
lean_object* v___x_5390_; 
lean_inc(v_a_5388_);
lean_inc_ref(v_a_5387_);
lean_inc(v_a_5386_);
lean_inc_ref(v_a_5385_);
lean_inc(v_mvarId_5383_);
v___x_5390_ = l_Lean_MVarId_contradictionCore(v_mvarId_5383_, v_config_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
if (lean_obj_tag(v___x_5390_) == 0)
{
lean_object* v_a_5391_; lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5403_; 
v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5393_ = v___x_5390_;
v_isShared_5394_ = v_isSharedCheck_5403_;
goto v_resetjp_5392_;
}
else
{
lean_inc(v_a_5391_);
lean_dec(v___x_5390_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5403_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
uint8_t v___x_5395_; 
v___x_5395_ = lean_unbox(v_a_5391_);
lean_dec(v_a_5391_);
if (v___x_5395_ == 0)
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; 
lean_del_object(v___x_5393_);
v___x_5396_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_5397_ = lean_box(0);
v___x_5398_ = l_Lean_Meta_throwTacticEx___redArg(v___x_5396_, v_mvarId_5383_, v___x_5397_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
lean_dec(v_a_5388_);
lean_dec_ref(v_a_5387_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
return v___x_5398_;
}
else
{
lean_object* v___x_5399_; lean_object* v___x_5401_; 
lean_dec(v_a_5388_);
lean_dec_ref(v_a_5387_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
lean_dec(v_mvarId_5383_);
v___x_5399_ = lean_box(0);
if (v_isShared_5394_ == 0)
{
lean_ctor_set(v___x_5393_, 0, v___x_5399_);
v___x_5401_ = v___x_5393_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5399_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec(v_a_5388_);
lean_dec_ref(v_a_5387_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
lean_dec(v_mvarId_5383_);
v_a_5404_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5390_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5390_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_5412_, lean_object* v_config_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_){
_start:
{
lean_object* v_res_5419_; 
v_res_5419_ = l_Lean_MVarId_contradiction(v_mvarId_5412_, v_config_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_);
return v_res_5419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5482_; uint8_t v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5482_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_5483_ = 0;
v___x_5484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_5485_ = l_Lean_registerTraceClass(v___x_5482_, v___x_5483_, v___x_5484_);
return v___x_5485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_5487_;
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
