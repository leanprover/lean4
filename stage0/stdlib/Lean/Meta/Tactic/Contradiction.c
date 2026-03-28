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
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
size_t v_x_1118__boxed_163_; size_t v_x_1119__boxed_164_; lean_object* v_res_165_; 
v_x_1118__boxed_163_ = lean_unbox_usize(v_x_159_);
lean_dec(v_x_159_);
v_x_1119__boxed_164_ = lean_unbox_usize(v_x_160_);
lean_dec(v_x_160_);
v_res_165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_158_, v_x_1118__boxed_163_, v_x_1119__boxed_164_, v_x_161_, v_x_162_);
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
v___x_233_ = l_Lean_Meta_mkFalseElim(v_a_231_, v___x_232_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_244_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref(v___x_233_);
v___x_235_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_216_, v_a_234_, v_a_218_);
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
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
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
size_t v_x_1479__boxed_317_; size_t v_x_1480__boxed_318_; lean_object* v_res_319_; 
v_x_1479__boxed_317_ = lean_unbox_usize(v_x_313_);
lean_dec(v_x_313_);
v_x_1480__boxed_318_ = lean_unbox_usize(v_x_314_);
lean_dec(v_x_314_);
v_res_319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_311_, v_x_312_, v_x_1479__boxed_317_, v_x_1480__boxed_318_, v_x_315_, v_x_316_);
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
v___x_358_ = l_Lean_FVarId_getType___redArg(v_fvarId_348_, v_a_349_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref(v___x_358_);
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
goto v___jp_354_;
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
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
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
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
lean_inc(v___y_436_);
v___x_442_ = lean_apply_6(v_x_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, lean_box(0));
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_444_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* v_mvarId_451_, lean_object* v_x_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___f_459_; lean_object* v___x_460_; 
lean_inc(v___y_453_);
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
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
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
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Meta_saveState___redArg(v___y_501_, v___y_503_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___y_508_; lean_object* v___y_509_; uint8_t v___y_510_; lean_object* v___y_529_; lean_object* v_a_530_; lean_object* v___x_533_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
v___x_533_ = lean_apply_6(v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, lean_box(0));
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; uint8_t v___x_535_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
v___x_535_ = lean_unbox(v_a_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
lean_dec_ref(v___x_533_);
v___x_536_ = l_Lean_Meta_SavedState_restore___redArg(v_a_506_, v___y_501_, v___y_503_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_a_506_);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v___x_536_, 0);
lean_dec(v_unused_544_);
v___x_538_ = v___x_536_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_dec(v___x_536_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v_a_534_);
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_534_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v_a_534_);
v_a_545_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_536_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_536_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
lean_inc(v_a_545_);
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v___y_529_ = v___x_550_;
v_a_530_ = v_a_545_;
goto v___jp_528_;
}
}
}
}
else
{
lean_dec(v_a_534_);
lean_dec(v_a_506_);
return v___x_533_;
}
}
else
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_553_);
v___y_529_ = v___x_533_;
v_a_530_ = v_a_553_;
goto v___jp_528_;
}
v___jp_507_:
{
if (v___y_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v___y_508_);
v___x_511_ = l_Lean_Meta_SavedState_restore___redArg(v_a_506_, v___y_501_, v___y_503_);
lean_dec(v_a_506_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v___x_511_, 0);
lean_dec(v_unused_519_);
v___x_513_ = v___x_511_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_dec(v___x_511_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 1);
lean_ctor_set(v___x_513_, 0, v___y_509_);
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___y_509_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v___y_509_);
v_a_520_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_511_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_511_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_dec_ref(v___y_509_);
lean_dec(v_a_506_);
return v___y_508_;
}
}
v___jp_528_:
{
uint8_t v___x_531_; 
v___x_531_ = l_Lean_Exception_isInterrupt(v_a_530_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; 
lean_inc_ref(v_a_530_);
v___x_532_ = l_Lean_Exception_isRuntime(v_a_530_);
v___y_508_ = v___y_529_;
v___y_509_ = v_a_530_;
v___y_510_ = v___x_532_;
goto v___jp_507_;
}
else
{
v___y_508_ = v___y_529_;
v___y_509_ = v_a_530_;
v___y_510_ = v___x_531_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v_x_498_);
v_a_554_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_505_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_505_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_x_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object* v_msgData_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; lean_object* v_env_577_; lean_object* v___x_578_; lean_object* v_mctx_579_; lean_object* v_lctx_580_; lean_object* v_options_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_576_ = lean_st_ref_get(v___y_574_);
v_env_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc_ref(v_env_577_);
lean_dec(v___x_576_);
v___x_578_ = lean_st_ref_get(v___y_572_);
v_mctx_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc_ref(v_mctx_579_);
lean_dec(v___x_578_);
v_lctx_580_ = lean_ctor_get(v___y_571_, 2);
v_options_581_ = lean_ctor_get(v___y_573_, 2);
lean_inc_ref(v_options_581_);
lean_inc_ref(v_lctx_580_);
v___x_582_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_582_, 0, v_env_577_);
lean_ctor_set(v___x_582_, 1, v_mctx_579_);
lean_ctor_set(v___x_582_, 2, v_lctx_580_);
lean_ctor_set(v___x_582_, 3, v_options_581_);
v___x_583_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_msgData_570_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
return v_res_591_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_592_; double v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_float_of_nat(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_597_, lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_ref_604_; lean_object* v___x_605_; lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_650_; 
v_ref_604_ = lean_ctor_get(v___y_601_, 5);
v___x_605_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_650_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_650_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_650_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v_traceState_611_; lean_object* v_env_612_; lean_object* v_nextMacroScope_613_; lean_object* v_ngen_614_; lean_object* v_auxDeclNGen_615_; lean_object* v_cache_616_; lean_object* v_messages_617_; lean_object* v_infoState_618_; lean_object* v_snapshotTasks_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_649_; 
v___x_610_ = lean_st_ref_take(v___y_602_);
v_traceState_611_ = lean_ctor_get(v___x_610_, 4);
v_env_612_ = lean_ctor_get(v___x_610_, 0);
v_nextMacroScope_613_ = lean_ctor_get(v___x_610_, 1);
v_ngen_614_ = lean_ctor_get(v___x_610_, 2);
v_auxDeclNGen_615_ = lean_ctor_get(v___x_610_, 3);
v_cache_616_ = lean_ctor_get(v___x_610_, 5);
v_messages_617_ = lean_ctor_get(v___x_610_, 6);
v_infoState_618_ = lean_ctor_get(v___x_610_, 7);
v_snapshotTasks_619_ = lean_ctor_get(v___x_610_, 8);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_649_ == 0)
{
v___x_621_ = v___x_610_;
v_isShared_622_ = v_isSharedCheck_649_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snapshotTasks_619_);
lean_inc(v_infoState_618_);
lean_inc(v_messages_617_);
lean_inc(v_cache_616_);
lean_inc(v_traceState_611_);
lean_inc(v_auxDeclNGen_615_);
lean_inc(v_ngen_614_);
lean_inc(v_nextMacroScope_613_);
lean_inc(v_env_612_);
lean_dec(v___x_610_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_649_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
uint64_t v_tid_623_; lean_object* v_traces_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_648_; 
v_tid_623_ = lean_ctor_get_uint64(v_traceState_611_, sizeof(void*)*1);
v_traces_624_ = lean_ctor_get(v_traceState_611_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_traceState_611_);
if (v_isSharedCheck_648_ == 0)
{
v___x_626_ = v_traceState_611_;
v_isShared_627_ = v_isSharedCheck_648_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_traces_624_);
lean_dec(v_traceState_611_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_648_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; double v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_628_ = lean_box(0);
v___x_629_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_630_ = 0;
v___x_631_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_632_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_632_, 0, v_cls_597_);
lean_ctor_set(v___x_632_, 1, v___x_628_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
lean_ctor_set_float(v___x_632_, sizeof(void*)*3, v___x_629_);
lean_ctor_set_float(v___x_632_, sizeof(void*)*3 + 8, v___x_629_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3 + 16, v___x_630_);
v___x_633_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_634_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v_a_606_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_inc(v_ref_604_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_ref_604_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_PersistentArray_push___redArg(v_traces_624_, v___x_635_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_636_);
v___x_638_ = v___x_626_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_636_);
lean_ctor_set_uint64(v_reuseFailAlloc_647_, sizeof(void*)*1, v_tid_623_);
v___x_638_ = v_reuseFailAlloc_647_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v___x_638_);
v___x_640_ = v___x_621_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_env_612_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_nextMacroScope_613_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_ngen_614_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v_auxDeclNGen_615_);
lean_ctor_set(v_reuseFailAlloc_646_, 4, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_646_, 5, v_cache_616_);
lean_ctor_set(v_reuseFailAlloc_646_, 6, v_messages_617_);
lean_ctor_set(v_reuseFailAlloc_646_, 7, v_infoState_618_);
lean_ctor_set(v_reuseFailAlloc_646_, 8, v_snapshotTasks_619_);
v___x_640_ = v_reuseFailAlloc_646_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_641_ = lean_st_ref_set(v___y_602_, v___x_640_);
v___x_642_ = lean_box(0);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_642_);
v___x_644_ = v___x_608_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_651_, v_msg_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_666_, lean_object* v_mvarId_667_, lean_object* v_fields_668_, lean_object* v_sz_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v___x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
size_t v_sz_boxed_679_; size_t v___x_18101__boxed_680_; uint8_t v___x_18103__boxed_681_; lean_object* v_res_682_; 
v_sz_boxed_679_ = lean_unbox_usize(v_sz_669_);
lean_dec(v_sz_669_);
v___x_18101__boxed_680_ = lean_unbox_usize(v___x_670_);
lean_dec(v___x_670_);
v___x_18103__boxed_681_ = lean_unbox(v___x_672_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_666_, v_mvarId_667_, v_fields_668_, v_sz_boxed_679_, v___x_18101__boxed_680_, v___x_671_, v___x_18103__boxed_681_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v_fields_668_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_683_, lean_object* v_as_684_, size_t v_sz_685_, size_t v_i_686_, lean_object* v_b_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
uint8_t v___x_694_; 
v___x_694_ = lean_usize_dec_lt(v_i_686_, v_sz_685_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v_b_687_);
return v___x_695_;
}
else
{
lean_object* v_a_696_; lean_object* v_toInductionSubgoal_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_b_687_);
v_a_696_ = lean_array_uget(v_as_684_, v_i_686_);
v_toInductionSubgoal_697_ = lean_ctor_get(v_a_696_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v_a_696_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v_a_696_, 1);
lean_dec(v_unused_739_);
v___x_699_ = v_a_696_;
v_isShared_700_ = v_isSharedCheck_738_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_toInductionSubgoal_697_);
lean_dec(v_a_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_738_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_mvarId_701_; lean_object* v_fields_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; size_t v_sz_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v___x_712_; 
v_mvarId_701_ = lean_ctor_get(v_toInductionSubgoal_697_, 0);
lean_inc_n(v_mvarId_701_, 2);
v_fields_702_ = lean_ctor_get(v_toInductionSubgoal_697_, 1);
lean_inc_ref(v_fields_702_);
v___x_703_ = lean_box(0);
v___x_704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_nat_dec_eq(v_val_683_, v___x_705_);
v_sz_707_ = lean_array_size(v_fields_702_);
v___x_708_ = lean_box_usize(v_sz_707_);
v___x_709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_710_ = lean_box(v___x_706_);
v___f_711_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_711_, 0, v_toInductionSubgoal_697_);
lean_closure_set(v___f_711_, 1, v_mvarId_701_);
lean_closure_set(v___f_711_, 2, v_fields_702_);
lean_closure_set(v___f_711_, 3, v___x_708_);
lean_closure_set(v___f_711_, 4, v___x_709_);
lean_closure_set(v___f_711_, 5, v___x_704_);
lean_closure_set(v___f_711_, 6, v___x_710_);
v___x_712_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_701_, v___f_711_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_729_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_729_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_729_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_729_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
uint8_t v___x_717_; 
v___x_717_ = lean_unbox(v_a_713_);
lean_dec(v_a_713_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_718_ = lean_box(v___x_706_);
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v___x_703_);
lean_ctor_set(v___x_699_, 0, v___x_719_);
v___x_721_ = v___x_699_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_703_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_721_);
v___x_723_ = v___x_715_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
size_t v___x_726_; size_t v___x_727_; 
lean_del_object(v___x_715_);
lean_del_object(v___x_699_);
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_add(v_i_686_, v___x_726_);
v_i_686_ = v___x_727_;
v_b_687_ = v___x_704_;
goto _start;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_del_object(v___x_699_);
v_a_730_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_712_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_712_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
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
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_751_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_752_ = l_Lean_Name_append(v___x_751_, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_756_, lean_object* v_fvarId_757_, lean_object* v___x_758_, uint8_t v___x_759_, lean_object* v___x_760_, lean_object* v_val_761_, uint8_t v___x_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_MVarId_cases(v_mvarId_756_, v_fvarId_757_, v___x_758_, v___x_759_, v___x_760_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v_options_803_; uint8_t v_hasTrace_804_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
v_options_803_ = lean_ctor_get(v___y_766_, 2);
v_hasTrace_804_ = lean_ctor_get_uint8(v_options_803_, sizeof(void*)*1);
if (v_hasTrace_804_ == 0)
{
v___y_772_ = v___y_763_;
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
v___y_776_ = v___y_767_;
goto v___jp_771_;
}
else
{
lean_object* v_inheritedTraceOptions_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_inheritedTraceOptions_805_ = lean_ctor_get(v___y_766_, 13);
v___x_806_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_807_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_808_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_805_, v_options_803_, v___x_807_);
if (v___x_808_ == 0)
{
v___y_772_ = v___y_763_;
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
v___y_776_ = v___y_767_;
goto v___jp_771_;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_809_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_810_ = lean_array_get_size(v_a_770_);
v___x_811_ = l_Nat_reprFast(v___x_810_);
v___x_812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = l_Lean_MessageData_ofFormat(v___x_812_);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_809_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_806_, v___x_814_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_dec_ref(v___x_815_);
v___y_772_ = v___y_763_;
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
v___y_776_ = v___y_767_;
goto v___jp_771_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_a_770_);
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
v___jp_771_:
{
lean_object* v___x_777_; size_t v_sz_778_; size_t v___x_779_; lean_object* v___x_780_; 
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_778_ = lean_array_size(v_a_770_);
v___x_779_ = ((size_t)0ULL);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_761_, v_a_770_, v_sz_778_, v___x_779_, v___x_777_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v_a_770_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_794_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_794_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_794_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_794_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_fst_785_; 
v_fst_785_ = lean_ctor_get(v_a_781_, 0);
lean_inc(v_fst_785_);
lean_dec(v_a_781_);
if (lean_obj_tag(v_fst_785_) == 0)
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = lean_box(v___x_762_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
else
{
lean_object* v_val_790_; lean_object* v___x_792_; 
v_val_790_ = lean_ctor_get(v_fst_785_, 0);
lean_inc(v_val_790_);
lean_dec_ref(v_fst_785_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_val_790_);
v___x_792_ = v___x_783_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_val_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v_a_795_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_780_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_780_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_868_; 
v_a_824_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_868_ == 0)
{
v___x_826_ = v___x_769_;
v_isShared_827_ = v_isSharedCheck_868_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_769_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_868_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
uint8_t v___y_829_; uint8_t v___x_866_; 
v___x_866_ = l_Lean_Exception_isInterrupt(v_a_824_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; 
lean_inc(v_a_824_);
v___x_867_ = l_Lean_Exception_isRuntime(v_a_824_);
v___y_829_ = v___x_867_;
goto v___jp_828_;
}
else
{
v___y_829_ = v___x_866_;
goto v___jp_828_;
}
v___jp_828_:
{
if (v___y_829_ == 0)
{
lean_object* v_options_830_; uint8_t v_hasTrace_831_; 
v_options_830_ = lean_ctor_get(v___y_766_, 2);
v_hasTrace_831_ = lean_ctor_get_uint8(v_options_830_, sizeof(void*)*1);
if (v_hasTrace_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_834_; 
lean_dec(v_a_824_);
v___x_832_ = lean_box(v___x_759_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_832_);
v___x_834_ = v___x_826_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
lean_object* v_inheritedTraceOptions_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_inheritedTraceOptions_836_ = lean_ctor_get(v___y_766_, 13);
v___x_837_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_838_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_836_, v_options_830_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_842_; 
lean_dec(v_a_824_);
v___x_840_ = lean_box(v___x_759_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_840_);
v___x_842_ = v___x_826_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_del_object(v___x_826_);
v___x_844_ = l_Lean_Exception_toMessageData(v_a_824_);
v___x_845_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_837_, v___x_844_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v___x_845_, 0);
lean_dec(v_unused_854_);
v___x_847_ = v___x_845_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_845_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_box(v___x_759_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_845_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_845_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
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
else
{
lean_object* v___x_864_; 
if (v_isShared_827_ == 0)
{
v___x_864_ = v___x_826_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_824_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_869_, lean_object* v_fvarId_870_, lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v_val_874_, lean_object* v___x_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v___x_18223__boxed_882_; uint8_t v___x_18226__boxed_883_; lean_object* v_res_884_; 
v___x_18223__boxed_882_ = lean_unbox(v___x_872_);
v___x_18226__boxed_883_ = lean_unbox(v___x_875_);
v_res_884_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_869_, v_fvarId_870_, v___x_871_, v___x_18223__boxed_882_, v___x_873_, v_val_874_, v___x_18226__boxed_883_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec(v_val_874_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_888_, lean_object* v_fvarId_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_st_ref_get(v_a_890_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_nat_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___f_912_; lean_object* v___x_913_; 
v___x_903_ = lean_st_ref_take(v_a_890_);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_sub(v___x_903_, v___x_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_st_ref_set(v_a_890_, v___x_905_);
v___x_907_ = 1;
v___x_908_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_909_ = lean_box(0);
v___x_910_ = lean_box(v___x_902_);
v___x_911_ = lean_box(v___x_907_);
v___f_912_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_912_, 0, v_mvarId_888_);
lean_closure_set(v___f_912_, 1, v_fvarId_889_);
lean_closure_set(v___f_912_, 2, v___x_908_);
lean_closure_set(v___f_912_, 3, v___x_910_);
lean_closure_set(v___f_912_, 4, v___x_909_);
lean_closure_set(v___f_912_, 5, v___x_900_);
lean_closure_set(v___f_912_, 6, v___x_911_);
v___x_913_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_912_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_913_;
}
else
{
lean_object* v_options_914_; uint8_t v_hasTrace_915_; 
lean_dec(v___x_900_);
lean_dec(v_fvarId_889_);
lean_dec(v_mvarId_888_);
v_options_914_ = lean_ctor_get(v_a_893_, 2);
v_hasTrace_915_ = lean_ctor_get_uint8(v_options_914_, sizeof(void*)*1);
if (v_hasTrace_915_ == 0)
{
goto v___jp_896_;
}
else
{
lean_object* v_inheritedTraceOptions_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_inheritedTraceOptions_916_ = lean_ctor_get(v_a_893_, 13);
v___x_917_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_918_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_919_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_916_, v_options_914_, v___x_918_);
if (v___x_919_ == 0)
{
goto v___jp_896_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_921_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_917_, v___x_920_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_dec_ref(v___x_921_);
goto v___jp_896_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
}
v___jp_896_:
{
uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = 0;
v___x_898_ = lean_box(v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_930_, lean_object* v___x_931_, lean_object* v_as_932_, size_t v_sz_933_, size_t v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_a_943_; uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_934_, v_sz_933_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
lean_dec(v___x_931_);
lean_dec_ref(v___x_930_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v_b_935_);
return v___x_948_;
}
else
{
lean_object* v_subst_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_a_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
lean_dec_ref(v_b_935_);
v_subst_949_ = lean_ctor_get(v___x_930_, 2);
v___x_950_ = lean_box(0);
v___x_951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_952_ = lean_array_uget_borrowed(v_as_932_, v_i_934_);
lean_inc(v_subst_949_);
v___x_953_ = l_Lean_Meta_FVarSubst_apply(v_subst_949_, v_a_952_);
v___x_954_ = l_Lean_Expr_isFVar(v___x_953_);
if (v___x_954_ == 0)
{
lean_dec_ref(v___x_953_);
v_a_943_ = v___x_951_;
goto v___jp_942_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = l_Lean_Expr_fvarId_x21(v___x_953_);
lean_dec_ref(v___x_953_);
lean_inc(v___x_955_);
v___x_956_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_955_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; uint8_t v___x_958_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = lean_unbox(v_a_957_);
lean_dec(v_a_957_);
if (v___x_958_ == 0)
{
lean_dec(v___x_955_);
v_a_943_ = v___x_951_;
goto v___jp_942_;
}
else
{
lean_object* v___x_959_; 
lean_inc(v___x_931_);
v___x_959_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_931_, v___x_955_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_970_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_970_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_970_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_970_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
uint8_t v___x_964_; 
v___x_964_ = lean_unbox(v_a_960_);
if (v___x_964_ == 0)
{
lean_del_object(v___x_962_);
lean_dec(v_a_960_);
v_a_943_ = v___x_951_;
goto v___jp_942_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
lean_dec(v___x_931_);
lean_dec_ref(v___x_930_);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_a_960_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_950_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_966_);
v___x_968_ = v___x_962_;
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
lean_dec(v___x_931_);
lean_dec_ref(v___x_930_);
v_a_971_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_959_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_959_);
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
lean_dec(v___x_955_);
lean_dec(v___x_931_);
lean_dec_ref(v___x_930_);
v_a_979_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_956_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_956_);
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
v___jp_942_:
{
size_t v___x_944_; size_t v___x_945_; 
v___x_944_ = ((size_t)1ULL);
v___x_945_ = lean_usize_add(v_i_934_, v___x_944_);
lean_inc_ref(v_a_943_);
v_i_934_ = v___x_945_;
v_b_935_ = v_a_943_;
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
lean_dec_ref(v_fst_1005_);
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
lean_dec_ref(v___x_1085_);
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
lean_dec_ref(v___x_1113_);
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
lean_dec_ref(v___x_1207_);
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
lean_dec_ref(v___x_1244_);
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
lean_object* v___f_1312_; lean_object* v___x_5507__overap_1313_; lean_object* v___x_1314_; 
v___f_1312_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_5507__overap_1313_ = lean_panic_fn_borrowed(v___f_1312_, v_msg_1306_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
v___x_1314_ = lean_apply_5(v___x_5507__overap_1313_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, lean_box(0));
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
v___x_1342_ = lean_st_ref_set(v___y_1323_, v___x_1341_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(lean_object* v_k_1365_, uint8_t v_allowLevelAssignments_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg___boxed(lean_object* v_k_1389_, lean_object* v_allowLevelAssignments_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1396_; lean_object* v_res_1397_; 
v_allowLevelAssignments_boxed_1396_ = lean_unbox(v_allowLevelAssignments_1390_);
v_res_1397_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(v_k_1389_, v_allowLevelAssignments_boxed_1396_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4(lean_object* v_00_u03b1_1398_, lean_object* v_k_1399_, uint8_t v_allowLevelAssignments_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(v_k_1399_, v_allowLevelAssignments_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___boxed(lean_object* v_00_u03b1_1407_, lean_object* v_k_1408_, lean_object* v_allowLevelAssignments_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1415_; lean_object* v_res_1416_; 
v_allowLevelAssignments_boxed_1415_ = lean_unbox(v_allowLevelAssignments_1409_);
v_res_1416_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4(v_00_u03b1_1407_, v_k_1408_, v_allowLevelAssignments_boxed_1415_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(lean_object* v_keys_1417_, lean_object* v_vals_1418_, lean_object* v_i_1419_, lean_object* v_k_1420_){
_start:
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = lean_array_get_size(v_keys_1417_);
v___x_1422_ = lean_nat_dec_lt(v_i_1419_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; 
lean_dec(v_i_1419_);
v___x_1423_ = lean_box(0);
return v___x_1423_;
}
else
{
lean_object* v_k_x27_1424_; uint8_t v___x_1425_; 
v_k_x27_1424_ = lean_array_fget_borrowed(v_keys_1417_, v_i_1419_);
v___x_1425_ = l_Lean_instBEqLevelMVarId_beq(v_k_1420_, v_k_x27_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_unsigned_to_nat(1u);
v___x_1427_ = lean_nat_add(v_i_1419_, v___x_1426_);
lean_dec(v_i_1419_);
v_i_1419_ = v___x_1427_;
goto _start;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_array_fget_borrowed(v_vals_1418_, v_i_1419_);
lean_dec(v_i_1419_);
lean_inc(v___x_1429_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_keys_1431_, lean_object* v_vals_1432_, lean_object* v_i_1433_, lean_object* v_k_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(v_keys_1431_, v_vals_1432_, v_i_1433_, v_k_1434_);
lean_dec(v_k_1434_);
lean_dec_ref(v_vals_1432_);
lean_dec_ref(v_keys_1431_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* v_x_1436_, size_t v_x_1437_, lean_object* v_x_1438_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v_es_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1460_; 
v_es_1439_ = lean_ctor_get(v_x_1436_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_x_1436_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1441_ = v_x_1436_;
v_isShared_1442_ = v_isSharedCheck_1460_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_es_1439_);
lean_dec(v_x_1436_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1460_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; lean_object* v_j_1447_; lean_object* v___x_1448_; 
v___x_1443_ = lean_box(2);
v___x_1444_ = ((size_t)5ULL);
v___x_1445_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1446_ = lean_usize_land(v_x_1437_, v___x_1445_);
v_j_1447_ = lean_usize_to_nat(v___x_1446_);
v___x_1448_ = lean_array_get(v___x_1443_, v_es_1439_, v_j_1447_);
lean_dec(v_j_1447_);
lean_dec_ref(v_es_1439_);
switch(lean_obj_tag(v___x_1448_))
{
case 0:
{
lean_object* v_key_1449_; lean_object* v_val_1450_; uint8_t v___x_1451_; 
v_key_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_key_1449_);
v_val_1450_ = lean_ctor_get(v___x_1448_, 1);
lean_inc(v_val_1450_);
lean_dec_ref(v___x_1448_);
v___x_1451_ = l_Lean_instBEqLevelMVarId_beq(v_x_1438_, v_key_1449_);
lean_dec(v_key_1449_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
lean_dec(v_val_1450_);
lean_del_object(v___x_1441_);
v___x_1452_ = lean_box(0);
return v___x_1452_;
}
else
{
lean_object* v___x_1454_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set_tag(v___x_1441_, 1);
lean_ctor_set(v___x_1441_, 0, v_val_1450_);
v___x_1454_ = v___x_1441_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_val_1450_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
case 1:
{
lean_object* v_node_1456_; size_t v___x_1457_; 
lean_del_object(v___x_1441_);
v_node_1456_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_node_1456_);
lean_dec_ref(v___x_1448_);
v___x_1457_ = lean_usize_shift_right(v_x_1437_, v___x_1444_);
v_x_1436_ = v_node_1456_;
v_x_1437_ = v___x_1457_;
goto _start;
}
default: 
{
lean_object* v___x_1459_; 
lean_del_object(v___x_1441_);
v___x_1459_ = lean_box(0);
return v___x_1459_;
}
}
}
}
else
{
lean_object* v_ks_1461_; lean_object* v_vs_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_ks_1461_ = lean_ctor_get(v_x_1436_, 0);
lean_inc_ref(v_ks_1461_);
v_vs_1462_ = lean_ctor_get(v_x_1436_, 1);
lean_inc_ref(v_vs_1462_);
lean_dec_ref(v_x_1436_);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(v_ks_1461_, v_vs_1462_, v___x_1463_, v_x_1438_);
lean_dec_ref(v_vs_1462_);
lean_dec_ref(v_ks_1461_);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
size_t v_x_9481__boxed_1468_; lean_object* v_res_1469_; 
v_x_9481__boxed_1468_ = lean_unbox_usize(v_x_1466_);
lean_dec(v_x_1466_);
v_res_1469_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(v_x_1465_, v_x_9481__boxed_1468_, v_x_1467_);
lean_dec(v_x_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
uint64_t v___x_1472_; size_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = l_Lean_instHashableLevelMVarId_hash(v_x_1471_);
v___x_1473_ = lean_uint64_to_usize(v___x_1472_);
v___x_1474_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(v_x_1470_, v___x_1473_, v_x_1471_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_x_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(v_x_1475_, v_x_1476_);
lean_dec(v_x_1476_);
return v_res_1477_;
}
}
static lean_object* _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0(void){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_instMonadEIO(lean_box(0));
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(lean_object* v_msg_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_toApplicative_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1553_; 
v___x_1489_ = lean_obj_once(&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0, &l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0_once, _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0);
v___x_1490_ = l_StateRefT_x27_instMonad___redArg(v___x_1489_);
v_toApplicative_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v___x_1490_, 1);
lean_dec(v_unused_1554_);
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1553_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_toApplicative_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1553_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_toFunctor_1495_; lean_object* v_toSeq_1496_; lean_object* v_toSeqLeft_1497_; lean_object* v_toSeqRight_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1551_; 
v_toFunctor_1495_ = lean_ctor_get(v_toApplicative_1491_, 0);
v_toSeq_1496_ = lean_ctor_get(v_toApplicative_1491_, 2);
v_toSeqLeft_1497_ = lean_ctor_get(v_toApplicative_1491_, 3);
v_toSeqRight_1498_ = lean_ctor_get(v_toApplicative_1491_, 4);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_toApplicative_1491_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v_toApplicative_1491_, 1);
lean_dec(v_unused_1552_);
v___x_1500_ = v_toApplicative_1491_;
v_isShared_1501_ = v_isSharedCheck_1551_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_toSeqRight_1498_);
lean_inc(v_toSeqLeft_1497_);
lean_inc(v_toSeq_1496_);
lean_inc(v_toFunctor_1495_);
lean_dec(v_toApplicative_1491_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1551_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___f_1502_; lean_object* v___f_1503_; lean_object* v___f_1504_; lean_object* v___f_1505_; lean_object* v___x_1506_; lean_object* v___f_1507_; lean_object* v___f_1508_; lean_object* v___f_1509_; lean_object* v___x_1511_; 
v___f_1502_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__1));
v___f_1503_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__2));
lean_inc_ref(v_toFunctor_1495_);
v___f_1504_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1504_, 0, v_toFunctor_1495_);
v___f_1505_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1505_, 0, v_toFunctor_1495_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___f_1504_);
lean_ctor_set(v___x_1506_, 1, v___f_1505_);
v___f_1507_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1507_, 0, v_toSeqRight_1498_);
v___f_1508_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1508_, 0, v_toSeqLeft_1497_);
v___f_1509_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1509_, 0, v_toSeq_1496_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 4, v___f_1507_);
lean_ctor_set(v___x_1500_, 3, v___f_1508_);
lean_ctor_set(v___x_1500_, 2, v___f_1509_);
lean_ctor_set(v___x_1500_, 1, v___f_1502_);
lean_ctor_set(v___x_1500_, 0, v___x_1506_);
v___x_1511_ = v___x_1500_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v___f_1502_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v___f_1509_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v___f_1508_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v___f_1507_);
v___x_1511_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1513_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___f_1503_);
lean_ctor_set(v___x_1493_, 0, v___x_1511_);
v___x_1513_ = v___x_1493_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v___f_1503_);
v___x_1513_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v_toApplicative_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1547_; 
v___x_1514_ = l_StateRefT_x27_instMonad___redArg(v___x_1513_);
v_toApplicative_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1514_, 1);
lean_dec(v_unused_1548_);
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1547_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_toApplicative_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1547_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_toFunctor_1519_; lean_object* v_toSeq_1520_; lean_object* v_toSeqLeft_1521_; lean_object* v_toSeqRight_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1545_; 
v_toFunctor_1519_ = lean_ctor_get(v_toApplicative_1515_, 0);
v_toSeq_1520_ = lean_ctor_get(v_toApplicative_1515_, 2);
v_toSeqLeft_1521_ = lean_ctor_get(v_toApplicative_1515_, 3);
v_toSeqRight_1522_ = lean_ctor_get(v_toApplicative_1515_, 4);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_toApplicative_1515_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v_toApplicative_1515_, 1);
lean_dec(v_unused_1546_);
v___x_1524_ = v_toApplicative_1515_;
v_isShared_1525_ = v_isSharedCheck_1545_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_toSeqRight_1522_);
lean_inc(v_toSeqLeft_1521_);
lean_inc(v_toSeq_1520_);
lean_inc(v_toFunctor_1519_);
lean_dec(v_toApplicative_1515_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1545_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___f_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; lean_object* v___f_1531_; lean_object* v___f_1532_; lean_object* v___f_1533_; lean_object* v___x_1535_; 
v___f_1526_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__3));
v___f_1527_ = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__4));
lean_inc_ref(v_toFunctor_1519_);
v___f_1528_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1528_, 0, v_toFunctor_1519_);
v___f_1529_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1529_, 0, v_toFunctor_1519_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___f_1528_);
lean_ctor_set(v___x_1530_, 1, v___f_1529_);
v___f_1531_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1531_, 0, v_toSeqRight_1522_);
v___f_1532_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1532_, 0, v_toSeqLeft_1521_);
v___f_1533_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1533_, 0, v_toSeq_1520_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 4, v___f_1531_);
lean_ctor_set(v___x_1524_, 3, v___f_1532_);
lean_ctor_set(v___x_1524_, 2, v___f_1533_);
lean_ctor_set(v___x_1524_, 1, v___f_1526_);
lean_ctor_set(v___x_1524_, 0, v___x_1530_);
v___x_1535_ = v___x_1524_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___f_1526_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v___f_1533_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v___f_1532_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v___f_1531_);
v___x_1535_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 1, v___f_1527_);
lean_ctor_set(v___x_1517_, 0, v___x_1535_);
v___x_1537_ = v___x_1517_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___f_1527_);
v___x_1537_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_9109__overap_1541_; lean_object* v___x_1542_; 
v___x_1538_ = 0;
v___x_1539_ = lean_box(v___x_1538_);
v___x_1540_ = l_instInhabitedOfMonad___redArg(v___x_1537_, v___x_1539_);
v___x_9109__overap_1541_ = lean_panic_fn_borrowed(v___x_1540_, v_msg_1483_);
lean_dec(v___x_1540_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
v___x_1542_ = lean_apply_5(v___x_9109__overap_1541_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, lean_box(0));
return v___x_1542_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_msg_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(v_msg_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(lean_object* v_mvarId_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v_mctx_1572_; lean_object* v_levelAssignDepth_1573_; lean_object* v_lDepth_1574_; lean_object* v___x_1575_; 
v___x_1571_ = lean_st_ref_get(v___y_1567_);
v_mctx_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc_ref(v_mctx_1572_);
lean_dec(v___x_1571_);
v_levelAssignDepth_1573_ = lean_ctor_get(v_mctx_1572_, 1);
lean_inc(v_levelAssignDepth_1573_);
v_lDepth_1574_ = lean_ctor_get(v_mctx_1572_, 3);
lean_inc_ref(v_lDepth_1574_);
lean_dec_ref(v_mctx_1572_);
v___x_1575_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(v_lDepth_1574_, v_mvarId_1565_);
if (lean_obj_tag(v___x_1575_) == 1)
{
lean_object* v_val_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_mvarId_1565_);
v_val_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_val_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1580_ = lean_nat_dec_le(v_levelAssignDepth_1573_, v_val_1576_);
lean_dec(v_val_1576_);
lean_dec(v_levelAssignDepth_1573_);
v___x_1581_ = lean_box(v___x_1580_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec(v___x_1575_);
lean_dec(v_levelAssignDepth_1573_);
v___x_1586_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__0));
v___x_1587_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__1));
v___x_1588_ = lean_unsigned_to_nat(451u);
v___x_1589_ = lean_unsigned_to_nat(14u);
v___x_1590_ = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__2));
v___x_1591_ = 1;
v___x_1592_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1565_, v___x_1591_);
v___x_1593_ = lean_string_append(v___x_1590_, v___x_1592_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = l_mkPanicMessageWithDecl(v___x_1586_, v___x_1587_, v___x_1588_, v___x_1589_, v___x_1593_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(v___x_1594_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___boxed(lean_object* v_mvarId_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(v_mvarId_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(lean_object* v_x_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___y_1610_; lean_object* v___y_1611_; uint8_t v_a_1612_; lean_object* v_lvl_u2081_1618_; lean_object* v_lvl_u2082_1619_; 
switch(lean_obj_tag(v_x_1603_))
{
case 1:
{
lean_object* v_a_1626_; uint8_t v___x_1627_; 
v_a_1626_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_a_1626_);
lean_dec_ref(v_x_1603_);
v___x_1627_ = l_Lean_Level_hasMVar(v_a_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_a_1626_);
v___x_1628_ = lean_box(v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
else
{
v_x_1603_ = v_a_1626_;
goto _start;
}
}
case 2:
{
lean_object* v_a_1631_; lean_object* v_a_1632_; 
v_a_1631_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_a_1631_);
v_a_1632_ = lean_ctor_get(v_x_1603_, 1);
lean_inc(v_a_1632_);
lean_dec_ref(v_x_1603_);
v_lvl_u2081_1618_ = v_a_1631_;
v_lvl_u2082_1619_ = v_a_1632_;
goto v___jp_1617_;
}
case 3:
{
lean_object* v_a_1633_; lean_object* v_a_1634_; 
v_a_1633_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_a_1633_);
v_a_1634_ = lean_ctor_get(v_x_1603_, 1);
lean_inc(v_a_1634_);
lean_dec_ref(v_x_1603_);
v_lvl_u2081_1618_ = v_a_1633_;
v_lvl_u2082_1619_ = v_a_1634_;
goto v___jp_1617_;
}
case 5:
{
lean_object* v_a_1635_; lean_object* v___x_1636_; 
v_a_1635_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_a_1635_);
lean_dec_ref(v_x_1603_);
v___x_1636_ = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(v_a_1635_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
return v___x_1636_;
}
default: 
{
uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v_x_1603_);
v___x_1637_ = 0;
v___x_1638_ = lean_box(v___x_1637_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
v___jp_1609_:
{
if (v_a_1612_ == 0)
{
uint8_t v___x_1613_; 
lean_dec_ref(v___y_1611_);
v___x_1613_ = l_Lean_Level_hasMVar(v___y_1610_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec(v___y_1610_);
v___x_1614_ = lean_box(v___x_1613_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
else
{
v_x_1603_ = v___y_1610_;
goto _start;
}
}
else
{
lean_dec(v___y_1610_);
return v___y_1611_;
}
}
v___jp_1617_:
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Lean_Level_hasMVar(v_lvl_u2081_1618_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec(v_lvl_u2081_1618_);
v___x_1621_ = lean_box(v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
v___y_1610_ = v_lvl_u2082_1619_;
v___y_1611_ = v___x_1622_;
v_a_1612_ = v___x_1620_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(v_lvl_u2081_1618_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; uint8_t v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
v___x_1625_ = lean_unbox(v_a_1624_);
lean_dec(v_a_1624_);
v___y_1610_ = v_lvl_u2082_1619_;
v___y_1611_ = v___x_1623_;
v_a_1612_ = v___x_1625_;
goto v___jp_1609_;
}
else
{
lean_dec(v_lvl_u2082_1619_);
return v___x_1623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4___boxed(lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(v_x_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(lean_object* v_x_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
if (lean_obj_tag(v_x_1647_) == 0)
{
uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = 0;
v___x_1654_ = lean_box(v___x_1653_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v_head_1656_; lean_object* v_tail_1657_; lean_object* v___x_1658_; 
v_head_1656_ = lean_ctor_get(v_x_1647_, 0);
lean_inc(v_head_1656_);
v_tail_1657_ = lean_ctor_get(v_x_1647_, 1);
lean_inc(v_tail_1657_);
lean_dec_ref(v_x_1647_);
v___x_1658_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(v_head_1656_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; uint8_t v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
v___x_1660_ = lean_unbox(v_a_1659_);
lean_dec(v_a_1659_);
if (v___x_1660_ == 0)
{
lean_dec_ref(v___x_1658_);
v_x_1647_ = v_tail_1657_;
goto _start;
}
else
{
lean_dec(v_tail_1657_);
return v___x_1658_;
}
}
else
{
lean_dec(v_tail_1657_);
return v___x_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5___boxed(lean_object* v_x_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(v_x_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(lean_object* v_mvarId_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v_mctx_1673_; lean_object* v_decl_1674_; lean_object* v_depth_1675_; lean_object* v_depth_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1672_ = lean_st_ref_get(v___y_1670_);
v_mctx_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc_ref_n(v_mctx_1673_, 2);
lean_dec(v___x_1672_);
v_decl_1674_ = l_Lean_MetavarContext_getDecl(v_mctx_1673_, v_mvarId_1669_);
v_depth_1675_ = lean_ctor_get(v_decl_1674_, 3);
lean_inc(v_depth_1675_);
lean_dec_ref(v_decl_1674_);
v_depth_1676_ = lean_ctor_get(v_mctx_1673_, 0);
lean_inc(v_depth_1676_);
lean_dec_ref(v_mctx_1673_);
v___x_1677_ = lean_nat_dec_eq(v_depth_1675_, v_depth_1676_);
lean_dec(v_depth_1676_);
lean_dec(v_depth_1675_);
v___x_1678_ = lean_box(v___x_1677_);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg___boxed(lean_object* v_mvarId_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(v_mvarId_1680_, v___y_1681_);
lean_dec(v___y_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___y_1691_; lean_object* v___y_1692_; uint8_t v_a_1693_; lean_object* v_d_1699_; lean_object* v_b_1700_; 
switch(lean_obj_tag(v_x_1684_))
{
case 2:
{
lean_object* v_mvarId_1707_; lean_object* v___x_1708_; 
v_mvarId_1707_ = lean_ctor_get(v_x_1684_, 0);
lean_inc(v_mvarId_1707_);
lean_dec_ref(v_x_1684_);
v___x_1708_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(v_mvarId_1707_, v___y_1686_);
return v___x_1708_;
}
case 3:
{
lean_object* v_u_1709_; lean_object* v___x_1710_; 
v_u_1709_ = lean_ctor_get(v_x_1684_, 0);
lean_inc(v_u_1709_);
lean_dec_ref(v_x_1684_);
v___x_1710_ = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(v_u_1709_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
return v___x_1710_;
}
case 4:
{
lean_object* v_us_1711_; lean_object* v___x_1712_; 
v_us_1711_ = lean_ctor_get(v_x_1684_, 1);
lean_inc(v_us_1711_);
lean_dec_ref(v_x_1684_);
v___x_1712_ = l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(v_us_1711_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
return v___x_1712_;
}
case 5:
{
lean_object* v_fn_1713_; lean_object* v_arg_1714_; lean_object* v___y_1716_; uint8_t v_a_1717_; uint8_t v___x_1722_; 
v_fn_1713_ = lean_ctor_get(v_x_1684_, 0);
lean_inc_ref(v_fn_1713_);
v_arg_1714_ = lean_ctor_get(v_x_1684_, 1);
lean_inc_ref(v_arg_1714_);
lean_dec_ref(v_x_1684_);
v___x_1722_ = l_Lean_Expr_hasMVar(v_fn_1713_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec_ref(v_fn_1713_);
v___x_1723_ = lean_box(v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
v___y_1716_ = v___x_1724_;
v_a_1717_ = v___x_1722_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_fn_1713_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; uint8_t v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
v___x_1727_ = lean_unbox(v_a_1726_);
lean_dec(v_a_1726_);
v___y_1716_ = v___x_1725_;
v_a_1717_ = v___x_1727_;
goto v___jp_1715_;
}
else
{
lean_dec_ref(v_arg_1714_);
return v___x_1725_;
}
}
v___jp_1715_:
{
if (v_a_1717_ == 0)
{
uint8_t v___x_1718_; 
lean_dec_ref(v___y_1716_);
v___x_1718_ = l_Lean_Expr_hasMVar(v_arg_1714_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec_ref(v_arg_1714_);
v___x_1719_ = lean_box(v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
return v___x_1720_;
}
else
{
v_x_1684_ = v_arg_1714_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1714_);
return v___y_1716_;
}
}
}
case 6:
{
lean_object* v_binderType_1728_; lean_object* v_body_1729_; 
v_binderType_1728_ = lean_ctor_get(v_x_1684_, 1);
lean_inc_ref(v_binderType_1728_);
v_body_1729_ = lean_ctor_get(v_x_1684_, 2);
lean_inc_ref(v_body_1729_);
lean_dec_ref(v_x_1684_);
v_d_1699_ = v_binderType_1728_;
v_b_1700_ = v_body_1729_;
goto v___jp_1698_;
}
case 7:
{
lean_object* v_binderType_1730_; lean_object* v_body_1731_; 
v_binderType_1730_ = lean_ctor_get(v_x_1684_, 1);
lean_inc_ref(v_binderType_1730_);
v_body_1731_ = lean_ctor_get(v_x_1684_, 2);
lean_inc_ref(v_body_1731_);
lean_dec_ref(v_x_1684_);
v_d_1699_ = v_binderType_1730_;
v_b_1700_ = v_body_1731_;
goto v___jp_1698_;
}
case 8:
{
lean_object* v_type_1732_; lean_object* v_value_1733_; lean_object* v_body_1734_; lean_object* v___y_1736_; uint8_t v_a_1737_; lean_object* v___y_1743_; uint8_t v_a_1744_; uint8_t v___x_1751_; 
v_type_1732_ = lean_ctor_get(v_x_1684_, 1);
lean_inc_ref(v_type_1732_);
v_value_1733_ = lean_ctor_get(v_x_1684_, 2);
lean_inc_ref(v_value_1733_);
v_body_1734_ = lean_ctor_get(v_x_1684_, 3);
lean_inc_ref(v_body_1734_);
lean_dec_ref(v_x_1684_);
v___x_1751_ = l_Lean_Expr_hasMVar(v_type_1732_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref(v_type_1732_);
v___x_1752_ = lean_box(v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
v___y_1743_ = v___x_1753_;
v_a_1744_ = v___x_1751_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_type_1732_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; uint8_t v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
v___x_1756_ = lean_unbox(v_a_1755_);
lean_dec(v_a_1755_);
v___y_1743_ = v___x_1754_;
v_a_1744_ = v___x_1756_;
goto v___jp_1742_;
}
else
{
lean_dec_ref(v_body_1734_);
lean_dec_ref(v_value_1733_);
return v___x_1754_;
}
}
v___jp_1735_:
{
if (v_a_1737_ == 0)
{
uint8_t v___x_1738_; 
lean_dec_ref(v___y_1736_);
v___x_1738_ = l_Lean_Expr_hasMVar(v_body_1734_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec_ref(v_body_1734_);
v___x_1739_ = lean_box(v___x_1738_);
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
else
{
v_x_1684_ = v_body_1734_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1734_);
return v___y_1736_;
}
}
v___jp_1742_:
{
if (v_a_1744_ == 0)
{
uint8_t v___x_1745_; 
lean_dec_ref(v___y_1743_);
v___x_1745_ = l_Lean_Expr_hasMVar(v_value_1733_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v_value_1733_);
v___x_1746_ = lean_box(v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
v___y_1736_ = v___x_1747_;
v_a_1737_ = v___x_1745_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_value_1733_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; uint8_t v___x_1750_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
v___x_1750_ = lean_unbox(v_a_1749_);
lean_dec(v_a_1749_);
v___y_1736_ = v___x_1748_;
v_a_1737_ = v___x_1750_;
goto v___jp_1735_;
}
else
{
lean_dec_ref(v_body_1734_);
return v___x_1748_;
}
}
}
else
{
lean_dec_ref(v_body_1734_);
lean_dec_ref(v_value_1733_);
return v___y_1743_;
}
}
}
case 10:
{
lean_object* v_expr_1757_; uint8_t v___x_1758_; 
v_expr_1757_ = lean_ctor_get(v_x_1684_, 1);
lean_inc_ref(v_expr_1757_);
lean_dec_ref(v_x_1684_);
v___x_1758_ = l_Lean_Expr_hasMVar(v_expr_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec_ref(v_expr_1757_);
v___x_1759_ = lean_box(v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
return v___x_1760_;
}
else
{
v_x_1684_ = v_expr_1757_;
goto _start;
}
}
case 11:
{
lean_object* v_struct_1762_; uint8_t v___x_1763_; 
v_struct_1762_ = lean_ctor_get(v_x_1684_, 2);
lean_inc_ref(v_struct_1762_);
lean_dec_ref(v_x_1684_);
v___x_1763_ = l_Lean_Expr_hasMVar(v_struct_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec_ref(v_struct_1762_);
v___x_1764_ = lean_box(v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
else
{
v_x_1684_ = v_struct_1762_;
goto _start;
}
}
default: 
{
uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec_ref(v_x_1684_);
v___x_1767_ = 0;
v___x_1768_ = lean_box(v___x_1767_);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
v___jp_1690_:
{
if (v_a_1693_ == 0)
{
uint8_t v___x_1694_; 
lean_dec_ref(v___y_1692_);
v___x_1694_ = l_Lean_Expr_hasMVar(v___y_1691_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec_ref(v___y_1691_);
v___x_1695_ = lean_box(v___x_1694_);
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
return v___x_1696_;
}
else
{
v_x_1684_ = v___y_1691_;
goto _start;
}
}
else
{
lean_dec_ref(v___y_1691_);
return v___y_1692_;
}
}
v___jp_1698_:
{
uint8_t v___x_1701_; 
v___x_1701_ = l_Lean_Expr_hasMVar(v_d_1699_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec_ref(v_d_1699_);
v___x_1702_ = lean_box(v___x_1701_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
v___y_1691_ = v_b_1700_;
v___y_1692_ = v___x_1703_;
v_a_1693_ = v___x_1701_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_d_1699_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; uint8_t v___x_1706_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
v___x_1706_ = lean_unbox(v_a_1705_);
lean_dec(v_a_1705_);
v___y_1691_ = v_b_1700_;
v___y_1692_ = v___x_1704_;
v_a_1693_ = v___x_1706_;
goto v___jp_1690_;
}
else
{
lean_dec_ref(v_b_1700_);
return v___x_1704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_x_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_x_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1779_, size_t v_sz_1780_, size_t v_i_1781_, lean_object* v_b_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_a_1789_; uint8_t v___x_1793_; 
v___x_1793_ = lean_usize_dec_lt(v_i_1781_, v_sz_1780_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_b_1782_);
return v___x_1794_;
}
else
{
lean_object* v_snd_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1957_; 
v_snd_1795_ = lean_ctor_get(v_b_1782_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_b_1782_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; 
v_unused_1958_ = lean_ctor_get(v_b_1782_, 0);
lean_dec(v_unused_1958_);
v___x_1797_ = v_b_1782_;
v_isShared_1798_ = v_isSharedCheck_1957_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_snd_1795_);
lean_dec(v_b_1782_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1957_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_array_1799_; lean_object* v_start_1800_; lean_object* v_stop_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_array_1799_ = lean_ctor_get(v_snd_1795_, 0);
v_start_1800_ = lean_ctor_get(v_snd_1795_, 1);
v_stop_1801_ = lean_ctor_get(v_snd_1795_, 2);
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_nat_dec_lt(v_start_1800_, v_stop_1801_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1805_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1802_);
v___x_1805_ = v___x_1797_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_snd_1795_);
v___x_1805_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
}
else
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1953_; 
lean_inc(v_stop_1801_);
lean_inc(v_start_1800_);
lean_inc_ref(v_array_1799_);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_snd_1795_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; lean_object* v_unused_1955_; lean_object* v_unused_1956_; 
v_unused_1954_ = lean_ctor_get(v_snd_1795_, 2);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_snd_1795_, 1);
lean_dec(v_unused_1955_);
v_unused_1956_ = lean_ctor_get(v_snd_1795_, 0);
lean_dec(v_unused_1956_);
v___x_1809_ = v_snd_1795_;
v_isShared_1810_ = v_isSharedCheck_1953_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_snd_1795_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1953_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1811_ = lean_array_fget(v_array_1799_, v_start_1800_);
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lean_nat_add(v_start_1800_, v___x_1812_);
lean_dec(v_start_1800_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v___x_1813_);
v___x_1815_ = v___x_1809_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_array_1799_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_stop_1801_);
v___x_1815_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_unbox(v___x_1811_);
lean_dec(v___x_1811_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1818_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 1, v___x_1815_);
lean_ctor_set(v___x_1797_, 0, v___x_1802_);
v___x_1818_ = v___x_1797_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1815_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
v_a_1789_ = v___x_1818_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_a_1820_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___x_1892_; 
v_a_1820_ = lean_array_uget_borrowed(v_as_1779_, v_i_1781_);
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1785_);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v_a_1820_);
v___x_1892_ = lean_infer_type(v_a_1820_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = l_Lean_Meta_matchEq_x3f(v_a_1893_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1894_);
if (lean_obj_tag(v_a_1895_) == 1)
{
lean_object* v_val_1896_; lean_object* v_snd_1897_; lean_object* v_fst_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1934_; 
v_val_1896_ = lean_ctor_get(v_a_1895_, 0);
lean_inc(v_val_1896_);
lean_dec_ref(v_a_1895_);
v_snd_1897_ = lean_ctor_get(v_val_1896_, 1);
lean_inc(v_snd_1897_);
lean_dec(v_val_1896_);
v_fst_1898_ = lean_ctor_get(v_snd_1897_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_snd_1897_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v_snd_1897_, 1);
lean_dec(v_unused_1935_);
v___x_1900_ = v_snd_1897_;
v_isShared_1901_ = v_isSharedCheck_1934_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_fst_1898_);
lean_dec(v_snd_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1934_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_Meta_mkEqRefl(v_fst_1898_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v___x_1902_);
lean_inc(v_a_1820_);
v___x_1904_ = l_Lean_Meta_isExprDefEq(v_a_1820_, v_a_1903_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1917_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1917_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1917_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_unbox(v_a_1905_);
lean_dec(v_a_1905_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_del_object(v___x_1797_);
v___x_1910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v___x_1815_);
lean_ctor_set(v___x_1900_, 0, v___x_1910_);
v___x_1912_ = v___x_1900_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v___x_1815_);
v___x_1912_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1914_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1912_);
v___x_1914_ = v___x_1907_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_del_object(v___x_1907_);
lean_del_object(v___x_1900_);
v___y_1822_ = v___y_1783_;
v___y_1823_ = v___y_1784_;
v___y_1824_ = v___y_1785_;
v___y_1825_ = v___y_1786_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_del_object(v___x_1900_);
lean_dec_ref(v___x_1815_);
lean_del_object(v___x_1797_);
v_a_1918_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1904_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1904_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_del_object(v___x_1900_);
lean_dec_ref(v___x_1815_);
lean_del_object(v___x_1797_);
v_a_1926_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1902_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1902_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
else
{
lean_dec(v_a_1895_);
v___y_1822_ = v___y_1783_;
v___y_1823_ = v___y_1784_;
v___y_1824_ = v___y_1785_;
v___y_1825_ = v___y_1786_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v___x_1815_);
lean_del_object(v___x_1797_);
v_a_1936_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1894_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1894_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v___x_1815_);
lean_del_object(v___x_1797_);
v_a_1944_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1892_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1892_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
v___jp_1821_:
{
lean_object* v___x_1826_; 
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
lean_inc(v_a_1820_);
v___x_1826_ = lean_infer_type(v_a_1820_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = l_Lean_Meta_matchHEq_x3f(v_a_1827_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v___x_1828_);
if (lean_obj_tag(v_a_1829_) == 1)
{
lean_object* v_val_1830_; lean_object* v_snd_1831_; lean_object* v_fst_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1871_; 
lean_del_object(v___x_1797_);
v_val_1830_ = lean_ctor_get(v_a_1829_, 0);
lean_inc(v_val_1830_);
lean_dec_ref(v_a_1829_);
v_snd_1831_ = lean_ctor_get(v_val_1830_, 1);
lean_inc(v_snd_1831_);
lean_dec(v_val_1830_);
v_fst_1832_ = lean_ctor_get(v_snd_1831_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_snd_1831_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v_snd_1831_, 1);
lean_dec(v_unused_1872_);
v___x_1834_ = v_snd_1831_;
v_isShared_1835_ = v_isSharedCheck_1871_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_fst_1832_);
lean_dec(v_snd_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1871_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_Meta_mkHEqRefl(v_fst_1832_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1836_);
lean_inc(v_a_1820_);
v___x_1838_ = l_Lean_Meta_isExprDefEq(v_a_1820_, v_a_1837_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1854_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1854_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1854_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_unbox(v_a_1839_);
lean_dec(v_a_1839_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1815_);
lean_ctor_set(v___x_1834_, 0, v___x_1844_);
v___x_1846_ = v___x_1834_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___x_1815_);
v___x_1846_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1846_);
v___x_1848_ = v___x_1841_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_object* v___x_1852_; 
lean_del_object(v___x_1841_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1815_);
lean_ctor_set(v___x_1834_, 0, v___x_1802_);
v___x_1852_ = v___x_1834_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___x_1815_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v_a_1789_ = v___x_1852_;
goto v___jp_1788_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_del_object(v___x_1834_);
lean_dec_ref(v___x_1815_);
v_a_1855_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1838_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1838_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_del_object(v___x_1834_);
lean_dec_ref(v___x_1815_);
v_a_1863_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1836_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1836_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
else
{
lean_object* v___x_1874_; 
lean_dec(v_a_1829_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 1, v___x_1815_);
lean_ctor_set(v___x_1797_, 0, v___x_1802_);
v___x_1874_ = v___x_1797_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1815_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
v_a_1789_ = v___x_1874_;
goto v___jp_1788_;
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v___x_1815_);
lean_del_object(v___x_1797_);
v_a_1876_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1828_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1828_);
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
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v___x_1815_);
lean_del_object(v___x_1797_);
v_a_1884_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1826_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1826_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
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
v___jp_1788_:
{
size_t v___x_1790_; size_t v___x_1791_; 
v___x_1790_ = ((size_t)1ULL);
v___x_1791_ = lean_usize_add(v_i_1781_, v___x_1790_);
v_i_1781_ = v___x_1791_;
v_b_1782_ = v_a_1789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1959_, lean_object* v_sz_1960_, lean_object* v_i_1961_, lean_object* v_b_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
size_t v_sz_boxed_1968_; size_t v_i_boxed_1969_; lean_object* v_res_1970_; 
v_sz_boxed_1968_ = lean_unbox_usize(v_sz_1960_);
lean_dec(v_sz_1960_);
v_i_boxed_1969_ = lean_unbox_usize(v_i_1961_);
lean_dec(v_i_1961_);
v_res_1970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1959_, v_sz_boxed_1968_, v_i_boxed_1969_, v_b_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec_ref(v_as_1959_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1971_, uint8_t v___x_1972_, lean_object* v_localDecl_1973_, lean_object* v_mvarId_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; 
lean_inc_ref(v___x_1971_);
v___x_1980_ = l_Lean_Meta_forallMetaTelescope(v___x_1971_, v___x_1972_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v_fst_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2071_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref(v___x_1980_);
v_fst_1982_ = lean_ctor_get(v_a_1981_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_a_1981_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v_a_1981_, 1);
lean_dec(v_unused_2072_);
v___x_1984_ = v_a_1981_;
v_isShared_1985_ = v_isSharedCheck_2071_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_fst_1982_);
lean_dec(v_a_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2071_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1986_ = l_Lean_Meta_mkGenDiseqMask(v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = lean_array_get_size(v___x_1986_);
v___x_1989_ = l_Array_toSubarray___redArg(v___x_1986_, v___x_1987_, v___x_1988_);
v___x_1990_ = lean_box(0);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 1, v___x_1989_);
lean_ctor_set(v___x_1984_, 0, v___x_1990_);
v___x_1992_ = v___x_1984_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_1989_);
v___x_1992_ = v_reuseFailAlloc_2070_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
size_t v_sz_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
v_sz_1993_ = lean_array_size(v_fst_1982_);
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1982_, v_sz_1993_, v___x_1994_, v___x_1992_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2061_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2061_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2061_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_fst_2000_; 
v_fst_2000_ = lean_ctor_get(v_a_1996_, 0);
lean_inc(v_fst_2000_);
lean_dec(v_a_1996_);
if (lean_obj_tag(v_fst_2000_) == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2056_; 
lean_del_object(v___x_1998_);
v___x_2001_ = l_Lean_LocalDecl_toExpr(v_localDecl_1973_);
v___x_2002_ = l_Lean_mkAppN(v___x_2001_, v_fst_1982_);
lean_dec(v_fst_1982_);
v___x_2003_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2002_, v___y_1976_);
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2056_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2056_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; 
lean_inc(v_a_2004_);
v___x_2008_ = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_a_2004_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2047_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2047_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2047_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_unbox(v_a_2009_);
lean_dec(v_a_2009_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
lean_del_object(v___x_2011_);
v___x_2014_ = l_Lean_MVarId_getType(v_mvarId_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = l_Lean_Meta_mkFalseElim(v_a_2015_, v_a_2004_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2027_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 1);
lean_ctor_set(v___x_2006_, 0, v_a_2017_);
v___x_2022_ = v___x_2006_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2022_);
v___x_2024_ = v___x_2019_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_del_object(v___x_2006_);
v_a_2028_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2016_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2016_);
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
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
v_a_2036_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2014_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2014_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v___x_2045_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_dec(v_mvarId_1974_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_1990_);
v___x_2045_ = v___x_2011_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_1990_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_dec(v_mvarId_1974_);
v_a_2048_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2008_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2008_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
else
{
lean_object* v_val_2057_; lean_object* v___x_2059_; 
lean_dec(v_fst_1982_);
lean_dec(v_mvarId_1974_);
lean_dec_ref(v_localDecl_1973_);
v_val_2057_ = lean_ctor_get(v_fst_2000_, 0);
lean_inc(v_val_2057_);
lean_dec_ref(v_fst_2000_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_val_2057_);
v___x_2059_ = v___x_1998_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_val_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_fst_1982_);
lean_dec(v_mvarId_1974_);
lean_dec_ref(v_localDecl_1973_);
v_a_2062_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_1995_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_1995_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_mvarId_1974_);
lean_dec_ref(v_localDecl_1973_);
lean_dec_ref(v___x_1971_);
v_a_2073_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_1980_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_1980_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_2081_, lean_object* v___x_2082_, lean_object* v_localDecl_2083_, lean_object* v_mvarId_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v___x_10435__boxed_2090_; lean_object* v_res_2091_; 
v___x_10435__boxed_2090_ = lean_unbox(v___x_2082_);
v_res_2091_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_2081_, v___x_10435__boxed_2090_, v_localDecl_2083_, v_mvarId_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_2096_ = lean_unsigned_to_nat(2u);
v___x_2097_ = lean_unsigned_to_nat(120u);
v___x_2098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_2099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_2100_ = l_mkPanicMessageWithDecl(v___x_2099_, v___x_2098_, v___x_2097_, v___x_2096_, v___x_2095_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_2101_, lean_object* v_localDecl_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = l_Lean_LocalDecl_type(v_localDecl_2102_);
lean_inc_ref(v___x_2108_);
v___x_2109_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_localDecl_2102_);
lean_dec(v_mvarId_2101_);
v___x_2110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_2111_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_2110_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
return v___x_2111_;
}
else
{
uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___f_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2112_ = 0;
v___x_2113_ = lean_box(v___x_2112_);
lean_inc(v_mvarId_2101_);
v___f_2114_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2114_, 0, v___x_2108_);
lean_closure_set(v___f_2114_, 1, v___x_2113_);
lean_closure_set(v___f_2114_, 2, v_localDecl_2102_);
lean_closure_set(v___f_2114_, 3, v_mvarId_2101_);
v___x_2115_ = 0;
v___x_2116_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(v___f_2114_, v___x_2115_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2136_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2136_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2136_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
if (lean_obj_tag(v_a_2117_) == 1)
{
lean_object* v_val_2121_; lean_object* v___x_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
lean_del_object(v___x_2119_);
v_val_2121_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_val_2121_);
lean_dec_ref(v_a_2117_);
v___x_2122_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2101_, v_val_2121_, v_a_2104_);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v___x_2122_, 0);
lean_dec(v_unused_2131_);
v___x_2124_ = v___x_2122_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v___x_2122_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_box(v___x_2109_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
lean_dec(v_a_2117_);
lean_dec(v_mvarId_2101_);
v___x_2132_ = lean_box(v___x_2115_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2132_);
v___x_2134_ = v___x_2119_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_mvarId_2101_);
v_a_2137_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2116_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2116_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_2145_, lean_object* v_localDecl_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2145_, v_localDecl_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(lean_object* v_mvarId_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(v_mvarId_2153_, v___y_2155_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___boxed(lean_object* v_mvarId_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(v_mvarId_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(v_x_2168_, v_x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b2_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7(v_00_u03b2_2171_, v_x_2172_, v_x_2173_);
lean_dec(v_x_2173_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_2175_, lean_object* v_x_2176_, size_t v_x_2177_, lean_object* v_x_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(v_x_2176_, v_x_2177_, v_x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b2_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_){
_start:
{
size_t v_x_10787__boxed_2184_; lean_object* v_res_2185_; 
v_x_10787__boxed_2184_ = lean_unbox_usize(v_x_2182_);
lean_dec(v_x_2182_);
v_res_2185_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9(v_00_u03b2_2180_, v_x_2181_, v_x_10787__boxed_2184_, v_x_2183_);
lean_dec(v_x_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* v_00_u03b2_2186_, lean_object* v_keys_2187_, lean_object* v_vals_2188_, lean_object* v_heq_2189_, lean_object* v_i_2190_, lean_object* v_k_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(v_keys_2187_, v_vals_2188_, v_i_2190_, v_k_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b2_2193_, lean_object* v_keys_2194_, lean_object* v_vals_2195_, lean_object* v_heq_2196_, lean_object* v_i_2197_, lean_object* v_k_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11(v_00_u03b2_2193_, v_keys_2194_, v_vals_2195_, v_heq_2196_, v_i_2197_, v_k_2198_);
lean_dec(v_k_2198_);
lean_dec_ref(v_vals_2195_);
lean_dec_ref(v_keys_2194_);
return v_res_2199_;
}
}
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1(void){
_start:
{
uint8_t v___x_2203_; uint64_t v___x_2204_; 
v___x_2203_ = 1;
v___x_2204_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6));
v___x_2215_ = l_Lean_mkConst(v___x_2214_, v___x_2213_);
return v___x_2215_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8(void){
_start:
{
lean_object* v___x_2216_; lean_object* v_dummy_2217_; 
v___x_2216_ = lean_box(0);
v_dummy_2217_ = l_Lean_Expr_sort___override(v___x_2216_);
return v_dummy_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_2218_, lean_object* v_mvarId_2219_, lean_object* v_as_2220_, size_t v_sz_2221_, size_t v_i_2222_, lean_object* v_b_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
uint8_t v___x_2229_; 
v___x_2229_ = lean_usize_dec_lt(v_i_2222_, v_sz_2221_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; 
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_b_2223_);
return v___x_2230_;
}
else
{
lean_object* v_snd_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2899_; 
v_snd_2231_ = lean_ctor_get(v_b_2223_, 1);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_b_2223_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v_b_2223_, 0);
lean_dec(v_unused_2900_);
v___x_2233_ = v_b_2223_;
v_isShared_2234_ = v_isSharedCheck_2899_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_snd_2231_);
lean_dec(v_b_2223_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2899_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v_a_2236_; lean_object* v___x_2242_; lean_object* v_a_2244_; lean_object* v_a_2249_; 
v___x_2242_ = lean_box(0);
v_a_2249_ = lean_array_uget(v_as_2220_, v_i_2222_);
if (lean_obj_tag(v_a_2249_) == 0)
{
lean_del_object(v___x_2233_);
v_a_2244_ = v_snd_2231_;
goto v___jp_2243_;
}
else
{
lean_object* v_val_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2898_; 
v_val_2250_ = lean_ctor_get(v_a_2249_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_a_2249_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2252_ = v_a_2249_;
v_isShared_2253_ = v_isSharedCheck_2898_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_val_2250_);
lean_dec(v_a_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2898_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___x_2295_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; uint8_t v___y_2322_; uint8_t v___x_2323_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; uint8_t v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; uint8_t v___y_2334_; lean_object* v___y_2335_; uint8_t v___y_2336_; uint8_t v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; uint8_t v___y_2349_; uint8_t v___y_2350_; lean_object* v___y_2351_; uint8_t v___y_2352_; 
v___x_2254_ = lean_box(0);
v___x_2295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2323_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2250_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2367_; uint8_t v___y_2369_; uint8_t v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; uint8_t v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; uint8_t v___y_2384_; uint8_t v___y_2385_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; uint8_t v___y_2391_; lean_object* v___y_2392_; uint8_t v___y_2393_; lean_object* v_a_2394_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; uint8_t v___y_2401_; lean_object* v___y_2402_; uint8_t v___y_2403_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; uint8_t v___y_2492_; lean_object* v___y_2493_; uint8_t v___y_2494_; uint8_t v___y_2495_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; uint8_t v___y_2501_; lean_object* v___y_2502_; uint8_t v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; uint8_t v___y_2510_; lean_object* v___y_2511_; uint8_t v___y_2512_; uint8_t v___y_2513_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; uint8_t v___y_2529_; lean_object* v___y_2530_; uint8_t v___y_2531_; uint8_t v___y_2532_; uint8_t v___y_2534_; uint8_t v_isHEq_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; uint8_t v___y_2549_; uint8_t v_isEq_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___x_2835_; 
v___x_2367_ = l_Lean_LocalDecl_type(v_val_2250_);
lean_inc_ref(v___x_2367_);
v___x_2835_ = l_Lean_Meta_matchNot_x3f(v___x_2367_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v___x_2835_);
if (lean_obj_tag(v_a_2836_) == 1)
{
lean_object* v_val_2837_; lean_object* v___x_2838_; 
v_val_2837_ = lean_ctor_get(v_a_2836_, 0);
lean_inc(v_val_2837_);
lean_dec_ref(v_a_2836_);
v___x_2838_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2837_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref(v___x_2838_);
if (lean_obj_tag(v_a_2839_) == 1)
{
lean_object* v_val_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec_ref(v_config_2218_);
v_val_2840_ = lean_ctor_get(v_a_2839_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_a_2839_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2842_ = v_a_2839_;
v_isShared_2843_ = v_isSharedCheck_2881_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_val_2840_);
lean_dec(v_a_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2881_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; 
lean_inc(v_mvarId_2219_);
v___x_2844_ = l_Lean_MVarId_getType(v_mvarId_2219_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = l_Lean_LocalDecl_toExpr(v_val_2250_);
v___x_2847_ = l_Lean_mkFVar(v_val_2840_);
v___x_2848_ = l_Lean_Expr_app___override(v___x_2846_, v___x_2847_);
v___x_2849_ = l_Lean_Meta_mkFalseElim(v_a_2845_, v___x_2848_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2219_, v_a_2850_, v___y_2225_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2854_; 
lean_dec_ref(v___x_2851_);
v___x_2852_ = lean_box(v___x_2229_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2852_);
v___x_2854_ = v___x_2842_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2254_);
v_a_2236_ = v___x_2855_;
goto v___jp_2235_;
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_del_object(v___x_2842_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
v_a_2857_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2851_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2851_);
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
lean_del_object(v___x_2842_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2865_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2849_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2849_);
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
lean_del_object(v___x_2842_);
lean_dec(v_val_2840_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2873_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2844_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2844_);
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
lean_dec(v_a_2839_);
v___y_2701_ = v___y_2224_;
v___y_2702_ = v___y_2225_;
v___y_2703_ = v___y_2226_;
v___y_2704_ = v___y_2227_;
goto v___jp_2700_;
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2882_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2838_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2838_);
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
lean_dec(v_a_2836_);
v___y_2701_ = v___y_2224_;
v___y_2702_ = v___y_2225_;
v___y_2703_ = v___y_2226_;
v___y_2704_ = v___y_2227_;
goto v___jp_2700_;
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2890_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2835_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2835_);
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
v___jp_2368_:
{
uint8_t v_genDiseq_2375_; 
v_genDiseq_2375_ = lean_ctor_get_uint8(v_config_2218_, sizeof(void*)*1 + 2);
if (v_genDiseq_2375_ == 0)
{
lean_dec_ref(v___x_2367_);
v___y_2346_ = v___y_2371_;
v___y_2347_ = v___y_2374_;
v___y_2348_ = v___y_2373_;
v___y_2349_ = v___y_2369_;
v___y_2350_ = v___y_2370_;
v___y_2351_ = v___y_2372_;
v___y_2352_ = v___x_2323_;
goto v___jp_2345_;
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2367_);
v___y_2346_ = v___y_2371_;
v___y_2347_ = v___y_2374_;
v___y_2348_ = v___y_2373_;
v___y_2349_ = v___y_2369_;
v___y_2350_ = v___y_2370_;
v___y_2351_ = v___y_2372_;
v___y_2352_ = v___x_2376_;
goto v___jp_2345_;
}
}
v___jp_2377_:
{
if (v___y_2385_ == 0)
{
lean_dec_ref(v___y_2383_);
v___y_2369_ = v___y_2381_;
v___y_2370_ = v___y_2384_;
v___y_2371_ = v___y_2380_;
v___y_2372_ = v___y_2382_;
v___y_2373_ = v___y_2378_;
v___y_2374_ = v___y_2379_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2386_; 
lean_dec_ref(v___x_2367_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___y_2383_);
return v___x_2386_;
}
}
v___jp_2387_:
{
uint8_t v___x_2395_; 
v___x_2395_ = l_Lean_Exception_isInterrupt(v_a_2394_);
if (v___x_2395_ == 0)
{
uint8_t v___x_2396_; 
lean_inc_ref(v_a_2394_);
v___x_2396_ = l_Lean_Exception_isRuntime(v_a_2394_);
v___y_2378_ = v___y_2388_;
v___y_2379_ = v___y_2389_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v___y_2391_;
v___y_2382_ = v___y_2392_;
v___y_2383_ = v_a_2394_;
v___y_2384_ = v___y_2393_;
v___y_2385_ = v___x_2396_;
goto v___jp_2377_;
}
else
{
v___y_2378_ = v___y_2388_;
v___y_2379_ = v___y_2389_;
v___y_2380_ = v___y_2390_;
v___y_2381_ = v___y_2391_;
v___y_2382_ = v___y_2392_;
v___y_2383_ = v_a_2394_;
v___y_2384_ = v___y_2393_;
v___y_2385_ = v___x_2395_;
goto v___jp_2377_;
}
}
v___jp_2397_:
{
lean_object* v___x_2404_; 
lean_inc_ref(v___x_2367_);
v___x_2404_ = l_Lean_Meta_mkDecide(v___x_2367_, v___y_2400_, v___y_2402_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; uint8_t v_foApprox_2407_; uint8_t v_ctxApprox_2408_; uint8_t v_quasiPatternApprox_2409_; uint8_t v_constApprox_2410_; uint8_t v_isDefEqStuckEx_2411_; uint8_t v_unificationHints_2412_; uint8_t v_proofIrrelevance_2413_; uint8_t v_assignSyntheticOpaque_2414_; uint8_t v_offsetCnstrs_2415_; uint8_t v_etaStruct_2416_; uint8_t v_univApprox_2417_; uint8_t v_iota_2418_; uint8_t v_beta_2419_; uint8_t v_proj_2420_; uint8_t v_zeta_2421_; uint8_t v_zetaDelta_2422_; uint8_t v_zetaUnused_2423_; uint8_t v_zetaHave_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2486_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref(v___x_2404_);
v___x_2406_ = l_Lean_Meta_Context_config(v___y_2400_);
v_foApprox_2407_ = lean_ctor_get_uint8(v___x_2406_, 0);
v_ctxApprox_2408_ = lean_ctor_get_uint8(v___x_2406_, 1);
v_quasiPatternApprox_2409_ = lean_ctor_get_uint8(v___x_2406_, 2);
v_constApprox_2410_ = lean_ctor_get_uint8(v___x_2406_, 3);
v_isDefEqStuckEx_2411_ = lean_ctor_get_uint8(v___x_2406_, 4);
v_unificationHints_2412_ = lean_ctor_get_uint8(v___x_2406_, 5);
v_proofIrrelevance_2413_ = lean_ctor_get_uint8(v___x_2406_, 6);
v_assignSyntheticOpaque_2414_ = lean_ctor_get_uint8(v___x_2406_, 7);
v_offsetCnstrs_2415_ = lean_ctor_get_uint8(v___x_2406_, 8);
v_etaStruct_2416_ = lean_ctor_get_uint8(v___x_2406_, 10);
v_univApprox_2417_ = lean_ctor_get_uint8(v___x_2406_, 11);
v_iota_2418_ = lean_ctor_get_uint8(v___x_2406_, 12);
v_beta_2419_ = lean_ctor_get_uint8(v___x_2406_, 13);
v_proj_2420_ = lean_ctor_get_uint8(v___x_2406_, 14);
v_zeta_2421_ = lean_ctor_get_uint8(v___x_2406_, 15);
v_zetaDelta_2422_ = lean_ctor_get_uint8(v___x_2406_, 16);
v_zetaUnused_2423_ = lean_ctor_get_uint8(v___x_2406_, 17);
v_zetaHave_2424_ = lean_ctor_get_uint8(v___x_2406_, 18);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2426_ = v___x_2406_;
v_isShared_2427_ = v_isSharedCheck_2486_;
goto v_resetjp_2425_;
}
else
{
lean_dec(v___x_2406_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2486_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
uint8_t v_trackZetaDelta_2428_; lean_object* v_zetaDeltaSet_2429_; lean_object* v_lctx_2430_; lean_object* v_localInstances_2431_; lean_object* v_defEqCtx_x3f_2432_; lean_object* v_synthPendingDepth_2433_; lean_object* v_canUnfold_x3f_2434_; uint8_t v_univApprox_2435_; uint8_t v_inTypeClassResolution_2436_; uint8_t v_cacheInferType_2437_; uint8_t v___x_2438_; lean_object* v_config_2440_; 
v_trackZetaDelta_2428_ = lean_ctor_get_uint8(v___y_2400_, sizeof(void*)*7);
v_zetaDeltaSet_2429_ = lean_ctor_get(v___y_2400_, 1);
v_lctx_2430_ = lean_ctor_get(v___y_2400_, 2);
v_localInstances_2431_ = lean_ctor_get(v___y_2400_, 3);
v_defEqCtx_x3f_2432_ = lean_ctor_get(v___y_2400_, 4);
v_synthPendingDepth_2433_ = lean_ctor_get(v___y_2400_, 5);
v_canUnfold_x3f_2434_ = lean_ctor_get(v___y_2400_, 6);
v_univApprox_2435_ = lean_ctor_get_uint8(v___y_2400_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2436_ = lean_ctor_get_uint8(v___y_2400_, sizeof(void*)*7 + 2);
v_cacheInferType_2437_ = lean_ctor_get_uint8(v___y_2400_, sizeof(void*)*7 + 3);
v___x_2438_ = 1;
if (v_isShared_2427_ == 0)
{
v_config_2440_ = v___x_2426_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 0, v_foApprox_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 1, v_ctxApprox_2408_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 2, v_quasiPatternApprox_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 3, v_constApprox_2410_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 4, v_isDefEqStuckEx_2411_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 5, v_unificationHints_2412_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 6, v_proofIrrelevance_2413_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 7, v_assignSyntheticOpaque_2414_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 8, v_offsetCnstrs_2415_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 10, v_etaStruct_2416_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 11, v_univApprox_2417_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 12, v_iota_2418_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 13, v_beta_2419_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 14, v_proj_2420_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 15, v_zeta_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 16, v_zetaDelta_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 17, v_zetaUnused_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 18, v_zetaHave_2424_);
v_config_2440_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
uint64_t v___x_2441_; uint64_t v___x_2442_; uint64_t v___x_2443_; uint64_t v___x_2444_; uint64_t v___x_2445_; uint64_t v_key_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_ctor_set_uint8(v_config_2440_, 9, v___x_2438_);
v___x_2441_ = l_Lean_Meta_Context_configKey(v___y_2400_);
v___x_2442_ = 2ULL;
v___x_2443_ = lean_uint64_shift_right(v___x_2441_, v___x_2442_);
v___x_2444_ = lean_uint64_shift_left(v___x_2443_, v___x_2442_);
v___x_2445_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_2446_ = lean_uint64_lor(v___x_2444_, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2447_, 0, v_config_2440_);
lean_ctor_set_uint64(v___x_2447_, sizeof(void*)*1, v_key_2446_);
lean_inc(v_canUnfold_x3f_2434_);
lean_inc(v_synthPendingDepth_2433_);
lean_inc(v_defEqCtx_x3f_2432_);
lean_inc_ref(v_localInstances_2431_);
lean_inc_ref(v_lctx_2430_);
lean_inc(v_zetaDeltaSet_2429_);
v___x_2448_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v_zetaDeltaSet_2429_);
lean_ctor_set(v___x_2448_, 2, v_lctx_2430_);
lean_ctor_set(v___x_2448_, 3, v_localInstances_2431_);
lean_ctor_set(v___x_2448_, 4, v_defEqCtx_x3f_2432_);
lean_ctor_set(v___x_2448_, 5, v_synthPendingDepth_2433_);
lean_ctor_set(v___x_2448_, 6, v_canUnfold_x3f_2434_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*7, v_trackZetaDelta_2428_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*7 + 1, v_univApprox_2435_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2436_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*7 + 3, v_cacheInferType_2437_);
lean_inc(v___y_2399_);
lean_inc_ref(v___y_2398_);
lean_inc(v___y_2402_);
lean_inc(v_a_2405_);
v___x_2449_ = lean_whnf(v_a_2405_, v___x_2448_, v___y_2402_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref(v___x_2449_);
v___x_2451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_2452_ = l_Lean_Expr_isConstOf(v_a_2450_, v___x_2451_);
lean_dec(v_a_2450_);
if (v___x_2452_ == 0)
{
lean_dec(v_a_2405_);
v___y_2369_ = v___y_2401_;
v___y_2370_ = v___y_2403_;
v___y_2371_ = v___y_2400_;
v___y_2372_ = v___y_2402_;
v___y_2373_ = v___y_2398_;
v___y_2374_ = v___y_2399_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2453_; 
lean_inc(v_a_2405_);
v___x_2453_ = l_Lean_Meta_mkEqRefl(v_a_2405_, v___y_2400_, v___y_2402_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2455_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref(v___x_2453_);
lean_inc(v_mvarId_2219_);
v___x_2455_ = l_Lean_MVarId_getType(v_mvarId_2219_, v___y_2400_, v___y_2402_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_nargs_2457_; lean_object* v___x_2458_; lean_object* v_dummy_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2455_);
v_nargs_2457_ = l_Lean_Expr_getAppNumArgs(v_a_2405_);
v___x_2458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_2459_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_2457_);
v___x_2460_ = lean_mk_array(v_nargs_2457_, v_dummy_2459_);
v___x_2461_ = lean_unsigned_to_nat(1u);
v___x_2462_ = lean_nat_sub(v_nargs_2457_, v___x_2461_);
lean_dec(v_nargs_2457_);
v___x_2463_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2405_, v___x_2460_, v___x_2462_);
v___x_2464_ = lean_array_push(v___x_2463_, v_a_2454_);
v___x_2465_ = l_Lean_mkAppN(v___x_2458_, v___x_2464_);
lean_dec_ref(v___x_2464_);
lean_inc(v_val_2250_);
v___x_2466_ = l_Lean_LocalDecl_toExpr(v_val_2250_);
v___x_2467_ = l_Lean_Meta_mkAbsurd(v_a_2456_, v___x_2466_, v___x_2465_, v___y_2400_, v___y_2402_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref(v___x_2467_);
lean_inc(v_mvarId_2219_);
v___x_2469_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2219_, v_a_2468_, v___y_2402_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2478_; 
lean_dec_ref(v___x_2367_);
lean_dec(v_val_2250_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2469_, 0);
lean_dec(v_unused_2479_);
v___x_2471_ = v___x_2469_;
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
else
{
lean_dec(v___x_2469_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_box(v___x_2229_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set_tag(v___x_2471_, 1);
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2254_);
v_a_2236_ = v___x_2476_;
goto v___jp_2235_;
}
}
}
else
{
lean_object* v_a_2480_; 
v_a_2480_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2480_);
lean_dec_ref(v___x_2469_);
v___y_2388_ = v___y_2398_;
v___y_2389_ = v___y_2399_;
v___y_2390_ = v___y_2400_;
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___y_2403_;
v_a_2394_ = v_a_2480_;
goto v___jp_2387_;
}
}
else
{
lean_object* v_a_2481_; 
v_a_2481_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2481_);
lean_dec_ref(v___x_2467_);
v___y_2388_ = v___y_2398_;
v___y_2389_ = v___y_2399_;
v___y_2390_ = v___y_2400_;
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___y_2403_;
v_a_2394_ = v_a_2481_;
goto v___jp_2387_;
}
}
else
{
lean_object* v_a_2482_; 
lean_dec(v_a_2454_);
lean_dec(v_a_2405_);
v_a_2482_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2482_);
lean_dec_ref(v___x_2455_);
v___y_2388_ = v___y_2398_;
v___y_2389_ = v___y_2399_;
v___y_2390_ = v___y_2400_;
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___y_2403_;
v_a_2394_ = v_a_2482_;
goto v___jp_2387_;
}
}
else
{
lean_object* v_a_2483_; 
lean_dec(v_a_2405_);
v_a_2483_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2483_);
lean_dec_ref(v___x_2453_);
v___y_2388_ = v___y_2398_;
v___y_2389_ = v___y_2399_;
v___y_2390_ = v___y_2400_;
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___y_2403_;
v_a_2394_ = v_a_2483_;
goto v___jp_2387_;
}
}
}
else
{
lean_object* v_a_2484_; 
lean_dec(v_a_2405_);
v_a_2484_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2484_);
lean_dec_ref(v___x_2449_);
v___y_2388_ = v___y_2398_;
v___y_2389_ = v___y_2399_;
v___y_2390_ = v___y_2400_;
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___y_2403_;
v_a_2394_ = v_a_2484_;
goto v___jp_2387_;
}
}
}
}
else
{
lean_object* v_a_2487_; 
v_a_2487_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2487_);
lean_dec_ref(v___x_2404_);
v___y_2388_ = v___y_2398_;
v___y_2389_ = v___y_2399_;
v___y_2390_ = v___y_2400_;
v___y_2391_ = v___y_2401_;
v___y_2392_ = v___y_2402_;
v___y_2393_ = v___y_2403_;
v_a_2394_ = v_a_2487_;
goto v___jp_2387_;
}
}
v___jp_2488_:
{
if (v___y_2495_ == 0)
{
v___y_2369_ = v___y_2492_;
v___y_2370_ = v___y_2494_;
v___y_2371_ = v___y_2491_;
v___y_2372_ = v___y_2493_;
v___y_2373_ = v___y_2489_;
v___y_2374_ = v___y_2490_;
goto v___jp_2368_;
}
else
{
v___y_2398_ = v___y_2489_;
v___y_2399_ = v___y_2490_;
v___y_2400_ = v___y_2491_;
v___y_2401_ = v___y_2492_;
v___y_2402_ = v___y_2493_;
v___y_2403_ = v___y_2494_;
goto v___jp_2397_;
}
}
v___jp_2496_:
{
if (v___y_2504_ == 0)
{
lean_dec_ref(v___y_2497_);
v___y_2489_ = v___y_2498_;
v___y_2490_ = v___y_2499_;
v___y_2491_ = v___y_2500_;
v___y_2492_ = v___y_2501_;
v___y_2493_ = v___y_2502_;
v___y_2494_ = v___y_2503_;
v___y_2495_ = v___x_2323_;
goto v___jp_2488_;
}
else
{
uint8_t v___x_2505_; 
v___x_2505_ = l_Lean_Expr_hasFVar(v___y_2497_);
lean_dec_ref(v___y_2497_);
if (v___x_2505_ == 0)
{
v___y_2398_ = v___y_2498_;
v___y_2399_ = v___y_2499_;
v___y_2400_ = v___y_2500_;
v___y_2401_ = v___y_2501_;
v___y_2402_ = v___y_2502_;
v___y_2403_ = v___y_2503_;
goto v___jp_2397_;
}
else
{
v___y_2489_ = v___y_2498_;
v___y_2490_ = v___y_2499_;
v___y_2491_ = v___y_2500_;
v___y_2492_ = v___y_2501_;
v___y_2493_ = v___y_2502_;
v___y_2494_ = v___y_2503_;
v___y_2495_ = v___x_2323_;
goto v___jp_2488_;
}
}
}
v___jp_2506_:
{
lean_object* v___x_2514_; 
lean_inc_ref(v___x_2367_);
v___x_2514_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2367_, v___y_2511_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; uint8_t v___x_2516_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref(v___x_2514_);
v___x_2516_ = l_Lean_Expr_hasMVar(v_a_2515_);
if (v___x_2516_ == 0)
{
v___y_2497_ = v_a_2515_;
v___y_2498_ = v___y_2507_;
v___y_2499_ = v___y_2508_;
v___y_2500_ = v___y_2509_;
v___y_2501_ = v___y_2510_;
v___y_2502_ = v___y_2511_;
v___y_2503_ = v___y_2512_;
v___y_2504_ = v___y_2513_;
goto v___jp_2496_;
}
else
{
v___y_2497_ = v_a_2515_;
v___y_2498_ = v___y_2507_;
v___y_2499_ = v___y_2508_;
v___y_2500_ = v___y_2509_;
v___y_2501_ = v___y_2510_;
v___y_2502_ = v___y_2511_;
v___y_2503_ = v___y_2512_;
v___y_2504_ = v___x_2323_;
goto v___jp_2496_;
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v___x_2367_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2517_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2514_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2514_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
v___jp_2525_:
{
if (v___y_2532_ == 0)
{
v___y_2369_ = v___y_2529_;
v___y_2370_ = v___y_2531_;
v___y_2371_ = v___y_2528_;
v___y_2372_ = v___y_2530_;
v___y_2373_ = v___y_2526_;
v___y_2374_ = v___y_2527_;
goto v___jp_2368_;
}
else
{
v___y_2507_ = v___y_2526_;
v___y_2508_ = v___y_2527_;
v___y_2509_ = v___y_2528_;
v___y_2510_ = v___y_2529_;
v___y_2511_ = v___y_2530_;
v___y_2512_ = v___y_2531_;
v___y_2513_ = v___y_2532_;
goto v___jp_2506_;
}
}
v___jp_2533_:
{
uint8_t v_useDecide_2540_; 
v_useDecide_2540_ = lean_ctor_get_uint8(v_config_2218_, sizeof(void*)*1);
if (v_useDecide_2540_ == 0)
{
v___y_2526_ = v___y_2538_;
v___y_2527_ = v___y_2539_;
v___y_2528_ = v___y_2536_;
v___y_2529_ = v_isHEq_2535_;
v___y_2530_ = v___y_2537_;
v___y_2531_ = v___y_2534_;
v___y_2532_ = v___x_2323_;
goto v___jp_2525_;
}
else
{
uint8_t v___x_2541_; 
v___x_2541_ = l_Lean_Expr_hasFVar(v___x_2367_);
if (v___x_2541_ == 0)
{
v___y_2507_ = v___y_2538_;
v___y_2508_ = v___y_2539_;
v___y_2509_ = v___y_2536_;
v___y_2510_ = v_isHEq_2535_;
v___y_2511_ = v___y_2537_;
v___y_2512_ = v___y_2534_;
v___y_2513_ = v_useDecide_2540_;
goto v___jp_2506_;
}
else
{
v___y_2526_ = v___y_2538_;
v___y_2527_ = v___y_2539_;
v___y_2528_ = v___y_2536_;
v___y_2529_ = v_isHEq_2535_;
v___y_2530_ = v___y_2537_;
v___y_2531_ = v___y_2534_;
v___y_2532_ = v___x_2323_;
goto v___jp_2525_;
}
}
}
v___jp_2542_:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_Meta_isExprDefEq(v___y_2543_, v___y_2547_, v___y_2548_, v___y_2546_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; uint8_t v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref(v___x_2550_);
v___x_2552_ = lean_unbox(v_a_2551_);
lean_dec(v_a_2551_);
if (v___x_2552_ == 0)
{
v___y_2534_ = v___y_2549_;
v_isHEq_2535_ = v___x_2229_;
v___y_2536_ = v___y_2548_;
v___y_2537_ = v___y_2546_;
v___y_2538_ = v___y_2544_;
v___y_2539_ = v___y_2545_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2553_; 
lean_dec_ref(v___x_2367_);
lean_dec_ref(v_config_2218_);
lean_inc(v_mvarId_2219_);
v___x_2553_ = l_Lean_MVarId_getType(v_mvarId_2219_, v___y_2548_, v___y_2546_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref(v___x_2553_);
v___x_2555_ = l_Lean_LocalDecl_toExpr(v_val_2250_);
v___x_2556_ = l_Lean_Meta_mkEqOfHEq(v___x_2555_, v___x_2229_, v___y_2548_, v___y_2546_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref(v___x_2556_);
v___x_2558_ = l_Lean_Meta_mkNoConfusion(v_a_2554_, v_a_2557_, v___y_2548_, v___y_2546_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref(v___x_2558_);
v___x_2560_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2219_, v_a_2559_, v___y_2546_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec_ref(v___x_2560_);
v___x_2561_ = lean_box(v___x_2229_);
v___x_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
lean_ctor_set(v___x_2563_, 1, v___x_2254_);
v_a_2236_ = v___x_2563_;
goto v___jp_2235_;
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
v_a_2564_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2560_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2560_);
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
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2572_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2558_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2558_);
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
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_a_2554_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2580_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2556_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2556_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2588_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2553_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2553_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec_ref(v___x_2367_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2596_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2550_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2550_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
v___jp_2604_:
{
lean_object* v___x_2610_; 
lean_inc_ref(v___x_2367_);
v___x_2610_ = l_Lean_Meta_matchHEq_x3f(v___x_2367_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2610_);
if (lean_obj_tag(v_a_2611_) == 1)
{
lean_object* v_val_2612_; lean_object* v_snd_2613_; lean_object* v_snd_2614_; lean_object* v_fst_2615_; lean_object* v_fst_2616_; lean_object* v_fst_2617_; lean_object* v_snd_2618_; lean_object* v___x_2619_; 
v_val_2612_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_val_2612_);
lean_dec_ref(v_a_2611_);
v_snd_2613_ = lean_ctor_get(v_val_2612_, 1);
lean_inc(v_snd_2613_);
v_snd_2614_ = lean_ctor_get(v_snd_2613_, 1);
lean_inc(v_snd_2614_);
v_fst_2615_ = lean_ctor_get(v_val_2612_, 0);
lean_inc(v_fst_2615_);
lean_dec(v_val_2612_);
v_fst_2616_ = lean_ctor_get(v_snd_2613_, 0);
lean_inc(v_fst_2616_);
lean_dec(v_snd_2613_);
v_fst_2617_ = lean_ctor_get(v_snd_2614_, 0);
lean_inc(v_fst_2617_);
v_snd_2618_ = lean_ctor_get(v_snd_2614_, 1);
lean_inc(v_snd_2618_);
lean_dec(v_snd_2614_);
v___x_2619_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2616_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref(v___x_2619_);
if (lean_obj_tag(v_a_2620_) == 1)
{
lean_object* v_val_2621_; lean_object* v___x_2622_; 
v_val_2621_ = lean_ctor_get(v_a_2620_, 0);
lean_inc(v_val_2621_);
lean_dec_ref(v_a_2620_);
v___x_2622_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2618_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref(v___x_2622_);
if (lean_obj_tag(v_a_2623_) == 1)
{
lean_object* v_toConstantVal_2624_; lean_object* v_val_2625_; lean_object* v_toConstantVal_2626_; lean_object* v_name_2627_; lean_object* v_name_2628_; uint8_t v___x_2629_; 
v_toConstantVal_2624_ = lean_ctor_get(v_val_2621_, 0);
lean_inc_ref(v_toConstantVal_2624_);
lean_dec(v_val_2621_);
v_val_2625_ = lean_ctor_get(v_a_2623_, 0);
lean_inc(v_val_2625_);
lean_dec_ref(v_a_2623_);
v_toConstantVal_2626_ = lean_ctor_get(v_val_2625_, 0);
lean_inc_ref(v_toConstantVal_2626_);
lean_dec(v_val_2625_);
v_name_2627_ = lean_ctor_get(v_toConstantVal_2624_, 0);
lean_inc(v_name_2627_);
lean_dec_ref(v_toConstantVal_2624_);
v_name_2628_ = lean_ctor_get(v_toConstantVal_2626_, 0);
lean_inc(v_name_2628_);
lean_dec_ref(v_toConstantVal_2626_);
v___x_2629_ = lean_name_eq(v_name_2627_, v_name_2628_);
lean_dec(v_name_2628_);
lean_dec(v_name_2627_);
if (v___x_2629_ == 0)
{
v___y_2543_ = v_fst_2615_;
v___y_2544_ = v___y_2608_;
v___y_2545_ = v___y_2609_;
v___y_2546_ = v___y_2607_;
v___y_2547_ = v_fst_2617_;
v___y_2548_ = v___y_2606_;
v___y_2549_ = v_isEq_2605_;
goto v___jp_2542_;
}
else
{
if (v___x_2323_ == 0)
{
lean_dec(v_fst_2617_);
lean_dec(v_fst_2615_);
v___y_2534_ = v_isEq_2605_;
v_isHEq_2535_ = v___x_2229_;
v___y_2536_ = v___y_2606_;
v___y_2537_ = v___y_2607_;
v___y_2538_ = v___y_2608_;
v___y_2539_ = v___y_2609_;
goto v___jp_2533_;
}
else
{
v___y_2543_ = v_fst_2615_;
v___y_2544_ = v___y_2608_;
v___y_2545_ = v___y_2609_;
v___y_2546_ = v___y_2607_;
v___y_2547_ = v_fst_2617_;
v___y_2548_ = v___y_2606_;
v___y_2549_ = v_isEq_2605_;
goto v___jp_2542_;
}
}
}
else
{
lean_dec(v_a_2623_);
lean_dec(v_val_2621_);
lean_dec(v_fst_2617_);
lean_dec(v_fst_2615_);
v___y_2534_ = v_isEq_2605_;
v_isHEq_2535_ = v___x_2229_;
v___y_2536_ = v___y_2606_;
v___y_2537_ = v___y_2607_;
v___y_2538_ = v___y_2608_;
v___y_2539_ = v___y_2609_;
goto v___jp_2533_;
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_val_2621_);
lean_dec(v_fst_2617_);
lean_dec(v_fst_2615_);
lean_dec_ref(v___x_2367_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2630_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2622_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2622_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_dec(v_a_2620_);
lean_dec(v_snd_2618_);
lean_dec(v_fst_2617_);
lean_dec(v_fst_2615_);
v___y_2534_ = v_isEq_2605_;
v_isHEq_2535_ = v___x_2229_;
v___y_2536_ = v___y_2606_;
v___y_2537_ = v___y_2607_;
v___y_2538_ = v___y_2608_;
v___y_2539_ = v___y_2609_;
goto v___jp_2533_;
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_snd_2618_);
lean_dec(v_fst_2617_);
lean_dec(v_fst_2615_);
lean_dec_ref(v___x_2367_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2638_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2619_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2619_);
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
else
{
lean_dec(v_a_2611_);
v___y_2534_ = v_isEq_2605_;
v_isHEq_2535_ = v___x_2323_;
v___y_2536_ = v___y_2606_;
v___y_2537_ = v___y_2607_;
v___y_2538_ = v___y_2608_;
v___y_2539_ = v___y_2609_;
goto v___jp_2533_;
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v___x_2367_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2646_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2610_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2610_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
v___jp_2654_:
{
lean_object* v___x_2659_; 
lean_inc_ref(v___x_2367_);
v___x_2659_ = l_Lean_Meta_matchEq_x3f(v___x_2367_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2659_);
if (lean_obj_tag(v_a_2660_) == 1)
{
lean_object* v_val_2661_; lean_object* v_snd_2662_; lean_object* v_fst_2663_; lean_object* v_snd_2664_; lean_object* v___x_2665_; 
v_val_2661_ = lean_ctor_get(v_a_2660_, 0);
lean_inc(v_val_2661_);
lean_dec_ref(v_a_2660_);
v_snd_2662_ = lean_ctor_get(v_val_2661_, 1);
lean_inc(v_snd_2662_);
lean_dec(v_val_2661_);
v_fst_2663_ = lean_ctor_get(v_snd_2662_, 0);
lean_inc(v_fst_2663_);
v_snd_2664_ = lean_ctor_get(v_snd_2662_, 1);
lean_inc(v_snd_2664_);
lean_dec(v_snd_2662_);
v___x_2665_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2663_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref(v___x_2665_);
if (lean_obj_tag(v_a_2666_) == 1)
{
lean_object* v_val_2667_; lean_object* v___x_2668_; 
v_val_2667_ = lean_ctor_get(v_a_2666_, 0);
lean_inc(v_val_2667_);
lean_dec_ref(v_a_2666_);
v___x_2668_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2664_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2668_);
if (lean_obj_tag(v_a_2669_) == 1)
{
lean_object* v_toConstantVal_2670_; lean_object* v_val_2671_; lean_object* v_toConstantVal_2672_; lean_object* v_name_2673_; lean_object* v_name_2674_; uint8_t v___x_2675_; 
v_toConstantVal_2670_ = lean_ctor_get(v_val_2667_, 0);
lean_inc_ref(v_toConstantVal_2670_);
lean_dec(v_val_2667_);
v_val_2671_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_val_2671_);
lean_dec_ref(v_a_2669_);
v_toConstantVal_2672_ = lean_ctor_get(v_val_2671_, 0);
lean_inc_ref(v_toConstantVal_2672_);
lean_dec(v_val_2671_);
v_name_2673_ = lean_ctor_get(v_toConstantVal_2670_, 0);
lean_inc(v_name_2673_);
lean_dec_ref(v_toConstantVal_2670_);
v_name_2674_ = lean_ctor_get(v_toConstantVal_2672_, 0);
lean_inc(v_name_2674_);
lean_dec_ref(v_toConstantVal_2672_);
v___x_2675_ = lean_name_eq(v_name_2673_, v_name_2674_);
lean_dec(v_name_2674_);
lean_dec(v_name_2673_);
if (v___x_2675_ == 0)
{
lean_dec_ref(v___x_2367_);
lean_dec_ref(v_config_2218_);
v___y_2256_ = v___y_2658_;
v___y_2257_ = v___y_2656_;
v___y_2258_ = v___y_2657_;
v___y_2259_ = v___y_2655_;
goto v___jp_2255_;
}
else
{
if (v___x_2323_ == 0)
{
lean_del_object(v___x_2252_);
v_isEq_2605_ = v___x_2229_;
v___y_2606_ = v___y_2655_;
v___y_2607_ = v___y_2656_;
v___y_2608_ = v___y_2657_;
v___y_2609_ = v___y_2658_;
goto v___jp_2604_;
}
else
{
lean_dec_ref(v___x_2367_);
lean_dec_ref(v_config_2218_);
v___y_2256_ = v___y_2658_;
v___y_2257_ = v___y_2656_;
v___y_2258_ = v___y_2657_;
v___y_2259_ = v___y_2655_;
goto v___jp_2255_;
}
}
}
else
{
lean_dec(v_a_2669_);
lean_dec(v_val_2667_);
lean_del_object(v___x_2252_);
v_isEq_2605_ = v___x_2229_;
v___y_2606_ = v___y_2655_;
v___y_2607_ = v___y_2656_;
v___y_2608_ = v___y_2657_;
v___y_2609_ = v___y_2658_;
goto v___jp_2604_;
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_val_2667_);
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2676_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2668_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2668_);
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
else
{
lean_dec(v_a_2666_);
lean_dec(v_snd_2664_);
lean_del_object(v___x_2252_);
v_isEq_2605_ = v___x_2229_;
v___y_2606_ = v___y_2655_;
v___y_2607_ = v___y_2656_;
v___y_2608_ = v___y_2657_;
v___y_2609_ = v___y_2658_;
goto v___jp_2604_;
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_snd_2664_);
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2684_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2665_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2665_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_dec(v_a_2660_);
lean_del_object(v___x_2252_);
v_isEq_2605_ = v___x_2323_;
v___y_2606_ = v___y_2655_;
v___y_2607_ = v___y_2656_;
v___y_2608_ = v___y_2657_;
v___y_2609_ = v___y_2658_;
goto v___jp_2604_;
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2692_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2659_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2659_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
v___jp_2700_:
{
lean_object* v___x_2705_; 
lean_inc_ref(v___x_2367_);
v___x_2705_ = l_refutableHasNotBit_x3f(v___x_2367_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref(v___x_2705_);
if (lean_obj_tag(v_a_2706_) == 1)
{
lean_object* v_val_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2746_; 
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec_ref(v_config_2218_);
v_val_2707_ = lean_ctor_get(v_a_2706_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_a_2706_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2709_ = v_a_2706_;
v_isShared_2710_ = v_isSharedCheck_2746_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_val_2707_);
lean_dec(v_a_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2746_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; 
lean_inc(v_mvarId_2219_);
v___x_2711_ = l_Lean_MVarId_getType(v_mvarId_2219_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = l_Lean_LocalDecl_toExpr(v_val_2250_);
v___x_2714_ = l_Lean_Meta_mkAbsurd(v_a_2712_, v_val_2707_, v___x_2713_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref(v___x_2714_);
v___x_2716_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2219_, v_a_2715_, v___y_2702_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
lean_dec_ref(v___x_2716_);
v___x_2717_ = lean_box(v___x_2229_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2717_);
v___x_2719_ = v___x_2709_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v___x_2254_);
v_a_2236_ = v___x_2720_;
goto v___jp_2235_;
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_del_object(v___x_2709_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
v_a_2722_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2716_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2716_);
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
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_del_object(v___x_2709_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2730_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2714_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2714_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_del_object(v___x_2709_);
lean_dec(v_val_2707_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2738_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2711_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2711_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
else
{
lean_object* v___x_2747_; 
lean_dec(v_a_2706_);
lean_inc_ref(v___x_2367_);
v___x_2747_ = l_Lean_Meta_matchNe_x3f(v___x_2367_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref(v___x_2747_);
if (lean_obj_tag(v_a_2748_) == 1)
{
lean_object* v_val_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2818_; 
v_val_2749_ = lean_ctor_get(v_a_2748_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_a_2748_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2751_ = v_a_2748_;
v_isShared_2752_ = v_isSharedCheck_2818_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_val_2749_);
lean_dec(v_a_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2818_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_snd_2753_; lean_object* v_fst_2754_; lean_object* v_snd_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2817_; 
v_snd_2753_ = lean_ctor_get(v_val_2749_, 1);
lean_inc(v_snd_2753_);
lean_dec(v_val_2749_);
v_fst_2754_ = lean_ctor_get(v_snd_2753_, 0);
v_snd_2755_ = lean_ctor_get(v_snd_2753_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_snd_2753_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2757_ = v_snd_2753_;
v_isShared_2758_ = v_isSharedCheck_2817_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_snd_2755_);
lean_inc(v_fst_2754_);
lean_dec(v_snd_2753_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2817_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; 
lean_inc(v_fst_2754_);
v___x_2759_ = l_Lean_Meta_isExprDefEq(v_fst_2754_, v_snd_2755_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; uint8_t v___x_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = lean_unbox(v_a_2760_);
lean_dec(v_a_2760_);
if (v___x_2761_ == 0)
{
lean_del_object(v___x_2757_);
lean_dec(v_fst_2754_);
lean_del_object(v___x_2751_);
v___y_2655_ = v___y_2701_;
v___y_2656_ = v___y_2702_;
v___y_2657_ = v___y_2703_;
v___y_2658_ = v___y_2704_;
goto v___jp_2654_;
}
else
{
lean_object* v___x_2762_; 
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec_ref(v_config_2218_);
lean_inc(v_mvarId_2219_);
v___x_2762_ = l_Lean_MVarId_getType(v_mvarId_2219_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref(v___x_2762_);
v___x_2764_ = l_Lean_Meta_mkEqRefl(v_fst_2754_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = l_Lean_LocalDecl_toExpr(v_val_2250_);
v___x_2767_ = l_Lean_Meta_mkAbsurd(v_a_2763_, v_a_2765_, v___x_2766_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref(v___x_2767_);
v___x_2769_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2219_, v_a_2768_, v___y_2702_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec_ref(v___x_2769_);
v___x_2770_ = lean_box(v___x_2229_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___x_2770_);
v___x_2772_ = v___x_2751_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2774_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2254_);
lean_ctor_set(v___x_2757_, 0, v___x_2772_);
v___x_2774_ = v___x_2757_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2254_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
v_a_2236_ = v___x_2774_;
goto v___jp_2235_;
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_del_object(v___x_2757_);
lean_del_object(v___x_2751_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
v_a_2777_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2769_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2769_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_del_object(v___x_2757_);
lean_del_object(v___x_2751_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2785_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2767_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2767_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec(v_a_2763_);
lean_del_object(v___x_2757_);
lean_del_object(v___x_2751_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2793_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2764_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2764_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_del_object(v___x_2757_);
lean_dec(v_fst_2754_);
lean_del_object(v___x_2751_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2801_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2762_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2762_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_del_object(v___x_2757_);
lean_dec(v_fst_2754_);
lean_del_object(v___x_2751_);
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2809_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2759_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2759_);
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
}
}
else
{
lean_dec(v_a_2748_);
v___y_2655_ = v___y_2701_;
v___y_2656_ = v___y_2702_;
v___y_2657_ = v___y_2703_;
v___y_2658_ = v___y_2704_;
goto v___jp_2654_;
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2819_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2747_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2747_);
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
lean_dec_ref(v___x_2367_);
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2827_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2705_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2705_);
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
}
else
{
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
v_a_2244_ = v___x_2295_;
goto v___jp_2243_;
}
v___jp_2255_:
{
lean_object* v___x_2260_; 
lean_inc(v_mvarId_2219_);
v___x_2260_ = l_Lean_MVarId_getType(v_mvarId_2219_, v___y_2259_, v___y_2257_, v___y_2258_, v___y_2256_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = l_Lean_LocalDecl_toExpr(v_val_2250_);
v___x_2263_ = l_Lean_Meta_mkNoConfusion(v_a_2261_, v___x_2262_, v___y_2259_, v___y_2257_, v___y_2258_, v___y_2256_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2219_, v_a_2264_, v___y_2257_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_dec_ref(v___x_2265_);
v___x_2266_ = lean_box(v___x_2229_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2266_);
v___x_2268_ = v___x_2252_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___x_2254_);
v_a_2236_ = v___x_2269_;
goto v___jp_2235_;
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_del_object(v___x_2252_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
v_a_2271_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2265_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2265_);
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
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_del_object(v___x_2252_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2279_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2263_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2263_);
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
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_del_object(v___x_2252_);
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
v_a_2287_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2260_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2260_);
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
v___jp_2296_:
{
lean_object* v_searchFuel_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_searchFuel_2301_ = lean_ctor_get(v_config_2218_, 0);
v___x_2302_ = l_Lean_LocalDecl_fvarId(v_val_2250_);
lean_dec(v_val_2250_);
lean_inc(v_searchFuel_2301_);
lean_inc(v_mvarId_2219_);
v___x_2303_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2219_, v___x_2302_, v_searchFuel_2301_, v___y_2300_, v___y_2299_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; uint8_t v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = lean_unbox(v_a_2304_);
lean_dec(v_a_2304_);
if (v___x_2305_ == 0)
{
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
v_a_2244_ = v___x_2295_;
goto v___jp_2243_;
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v___x_2306_ = lean_box(v___x_2229_);
v___x_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v___x_2254_);
v_a_2236_ = v___x_2308_;
goto v___jp_2235_;
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2309_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2303_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2303_);
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
v___jp_2317_:
{
if (v___y_2322_ == 0)
{
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
v_a_2244_ = v___x_2295_;
goto v___jp_2243_;
}
else
{
v___y_2297_ = v___y_2318_;
v___y_2298_ = v___y_2319_;
v___y_2299_ = v___y_2320_;
v___y_2300_ = v___y_2321_;
goto v___jp_2296_;
}
}
v___jp_2324_:
{
if (v___y_2328_ == 0)
{
v___y_2297_ = v___y_2325_;
v___y_2298_ = v___y_2326_;
v___y_2299_ = v___y_2327_;
v___y_2300_ = v___y_2329_;
goto v___jp_2296_;
}
else
{
v___y_2318_ = v___y_2325_;
v___y_2319_ = v___y_2326_;
v___y_2320_ = v___y_2327_;
v___y_2321_ = v___y_2329_;
v___y_2322_ = v___x_2323_;
goto v___jp_2317_;
}
}
v___jp_2330_:
{
if (v___y_2336_ == 0)
{
v___y_2318_ = v___y_2331_;
v___y_2319_ = v___y_2332_;
v___y_2320_ = v___y_2333_;
v___y_2321_ = v___y_2335_;
v___y_2322_ = v___x_2323_;
goto v___jp_2317_;
}
else
{
v___y_2325_ = v___y_2331_;
v___y_2326_ = v___y_2332_;
v___y_2327_ = v___y_2333_;
v___y_2328_ = v___y_2334_;
v___y_2329_ = v___y_2335_;
goto v___jp_2324_;
}
}
v___jp_2337_:
{
uint8_t v_emptyType_2344_; 
v_emptyType_2344_ = lean_ctor_get_uint8(v_config_2218_, sizeof(void*)*1 + 1);
if (v_emptyType_2344_ == 0)
{
v___y_2331_ = v___y_2342_;
v___y_2332_ = v___y_2343_;
v___y_2333_ = v___y_2341_;
v___y_2334_ = v___y_2338_;
v___y_2335_ = v___y_2340_;
v___y_2336_ = v___x_2323_;
goto v___jp_2330_;
}
else
{
if (v___y_2339_ == 0)
{
v___y_2325_ = v___y_2342_;
v___y_2326_ = v___y_2343_;
v___y_2327_ = v___y_2341_;
v___y_2328_ = v___y_2338_;
v___y_2329_ = v___y_2340_;
goto v___jp_2324_;
}
else
{
v___y_2331_ = v___y_2342_;
v___y_2332_ = v___y_2343_;
v___y_2333_ = v___y_2341_;
v___y_2334_ = v___y_2338_;
v___y_2335_ = v___y_2340_;
v___y_2336_ = v___x_2323_;
goto v___jp_2330_;
}
}
}
v___jp_2345_:
{
if (v___y_2352_ == 0)
{
v___y_2338_ = v___y_2349_;
v___y_2339_ = v___y_2350_;
v___y_2340_ = v___y_2346_;
v___y_2341_ = v___y_2351_;
v___y_2342_ = v___y_2348_;
v___y_2343_ = v___y_2347_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2353_; 
lean_inc(v_val_2250_);
lean_inc(v_mvarId_2219_);
v___x_2353_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2219_, v_val_2250_, v___y_2346_, v___y_2351_, v___y_2348_, v___y_2347_);
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
v___y_2338_ = v___y_2349_;
v___y_2339_ = v___y_2350_;
v___y_2340_ = v___y_2346_;
v___y_2341_ = v___y_2351_;
v___y_2342_ = v___y_2348_;
v___y_2343_ = v___y_2347_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec(v_val_2250_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v___x_2356_ = lean_box(v___x_2229_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v___x_2254_);
v_a_2236_ = v___x_2358_;
goto v___jp_2235_;
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec(v_val_2250_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2219_);
lean_dec_ref(v_config_2218_);
v_a_2359_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2353_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2353_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
}
}
v___jp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2237_, 0, v_a_2236_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2237_);
v___x_2239_ = v___x_2233_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_snd_2231_);
v___x_2239_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
v___jp_2243_:
{
lean_object* v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; 
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2242_);
lean_ctor_set(v___x_2245_, 1, v_a_2244_);
v___x_2246_ = ((size_t)1ULL);
v___x_2247_ = lean_usize_add(v_i_2222_, v___x_2246_);
v_i_2222_ = v___x_2247_;
v_b_2223_ = v___x_2245_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2901_, lean_object* v_mvarId_2902_, lean_object* v_as_2903_, lean_object* v_sz_2904_, lean_object* v_i_2905_, lean_object* v_b_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
size_t v_sz_boxed_2912_; size_t v_i_boxed_2913_; lean_object* v_res_2914_; 
v_sz_boxed_2912_ = lean_unbox_usize(v_sz_2904_);
lean_dec(v_sz_2904_);
v_i_boxed_2913_ = lean_unbox_usize(v_i_2905_);
lean_dec(v_i_2905_);
v_res_2914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2901_, v_mvarId_2902_, v_as_2903_, v_sz_boxed_2912_, v_i_boxed_2913_, v_b_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec_ref(v_as_2903_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2915_, lean_object* v_mvarId_2916_, lean_object* v_as_2917_, size_t v_sz_2918_, size_t v_i_2919_, lean_object* v_b_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_usize_dec_lt(v_i_2919_, v_sz_2918_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; 
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v_b_2920_);
return v___x_2927_;
}
else
{
lean_object* v_snd_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_3596_; 
v_snd_2928_ = lean_ctor_get(v_b_2920_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_b_2920_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; 
v_unused_3597_ = lean_ctor_get(v_b_2920_, 0);
lean_dec(v_unused_3597_);
v___x_2930_ = v_b_2920_;
v_isShared_2931_ = v_isSharedCheck_3596_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_snd_2928_);
lean_dec(v_b_2920_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_3596_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v_a_2933_; lean_object* v___x_2939_; lean_object* v_a_2941_; lean_object* v_a_2946_; 
v___x_2939_ = lean_box(0);
v_a_2946_ = lean_array_uget(v_as_2917_, v_i_2919_);
if (lean_obj_tag(v_a_2946_) == 0)
{
lean_del_object(v___x_2930_);
v_a_2941_ = v_snd_2928_;
goto v___jp_2940_;
}
else
{
lean_object* v_val_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_3595_; 
v_val_2947_ = lean_ctor_get(v_a_2946_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_a_2946_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_2949_ = v_a_2946_;
v_isShared_2950_ = v_isSharedCheck_3595_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_val_2947_);
lean_dec(v_a_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_3595_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___x_2992_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; uint8_t v___y_3019_; uint8_t v___x_3020_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; uint8_t v___y_3026_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; uint8_t v___y_3032_; uint8_t v___y_3033_; uint8_t v___y_3035_; uint8_t v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3043_; uint8_t v___y_3044_; lean_object* v___y_3045_; uint8_t v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; uint8_t v___y_3049_; 
v___x_2951_ = lean_box(0);
v___x_2992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_3020_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2947_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3064_; uint8_t v___y_3066_; uint8_t v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; uint8_t v___y_3079_; lean_object* v___y_3080_; uint8_t v___y_3081_; uint8_t v___y_3082_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; uint8_t v___y_3090_; lean_object* v_a_3091_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; uint8_t v___y_3098_; lean_object* v___y_3099_; uint8_t v___y_3100_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; uint8_t v___y_3189_; lean_object* v___y_3190_; uint8_t v___y_3191_; uint8_t v___y_3192_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; uint8_t v___y_3199_; uint8_t v___y_3200_; uint8_t v___y_3201_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; uint8_t v___y_3209_; uint8_t v___y_3210_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; uint8_t v___y_3226_; lean_object* v___y_3227_; uint8_t v___y_3228_; uint8_t v___y_3229_; uint8_t v___y_3231_; uint8_t v_isHEq_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; uint8_t v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; uint8_t v_isEq_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___x_3532_; 
v___x_3064_ = l_Lean_LocalDecl_type(v_val_2947_);
lean_inc_ref(v___x_3064_);
v___x_3532_ = l_Lean_Meta_matchNot_x3f(v___x_3064_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref(v___x_3532_);
if (lean_obj_tag(v_a_3533_) == 1)
{
lean_object* v_val_3534_; lean_object* v___x_3535_; 
v_val_3534_ = lean_ctor_get(v_a_3533_, 0);
lean_inc(v_val_3534_);
lean_dec_ref(v_a_3533_);
v___x_3535_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3534_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref(v___x_3535_);
if (lean_obj_tag(v_a_3536_) == 1)
{
lean_object* v_val_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3578_; 
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec_ref(v_config_2915_);
v_val_3537_ = lean_ctor_get(v_a_3536_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_a_3536_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3539_ = v_a_3536_;
v_isShared_3540_ = v_isSharedCheck_3578_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_val_3537_);
lean_dec(v_a_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3578_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; 
lean_inc(v_mvarId_2916_);
v___x_3541_ = l_Lean_MVarId_getType(v_mvarId_2916_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = l_Lean_LocalDecl_toExpr(v_val_2947_);
v___x_3544_ = l_Lean_mkFVar(v_val_3537_);
v___x_3545_ = l_Lean_Expr_app___override(v___x_3543_, v___x_3544_);
v___x_3546_ = l_Lean_Meta_mkFalseElim(v_a_3542_, v___x_3545_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3548_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref(v___x_3546_);
v___x_3548_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2916_, v_a_3547_, v___y_2922_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
lean_dec_ref(v___x_3548_);
v___x_3549_ = lean_box(v___x_2926_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3549_);
v___x_3551_ = v___x_3539_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
lean_ctor_set(v___x_3552_, 1, v___x_2951_);
v_a_2933_ = v___x_3552_;
goto v___jp_2932_;
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_del_object(v___x_3539_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
v_a_3554_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3548_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3548_);
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
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_del_object(v___x_3539_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3562_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3546_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3546_);
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
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_del_object(v___x_3539_);
lean_dec(v_val_3537_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3570_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3541_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3541_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
else
{
lean_dec(v_a_3536_);
v___y_3398_ = v___y_2921_;
v___y_3399_ = v___y_2922_;
v___y_3400_ = v___y_2923_;
v___y_3401_ = v___y_2924_;
goto v___jp_3397_;
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3579_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3535_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3535_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
lean_dec(v_a_3533_);
v___y_3398_ = v___y_2921_;
v___y_3399_ = v___y_2922_;
v___y_3400_ = v___y_2923_;
v___y_3401_ = v___y_2924_;
goto v___jp_3397_;
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3587_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3532_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3532_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
v___jp_3065_:
{
uint8_t v_genDiseq_3072_; 
v_genDiseq_3072_ = lean_ctor_get_uint8(v_config_2915_, sizeof(void*)*1 + 2);
if (v_genDiseq_3072_ == 0)
{
lean_dec_ref(v___x_3064_);
v___y_3043_ = v___y_3069_;
v___y_3044_ = v___y_3066_;
v___y_3045_ = v___y_3071_;
v___y_3046_ = v___y_3067_;
v___y_3047_ = v___y_3070_;
v___y_3048_ = v___y_3068_;
v___y_3049_ = v___x_3020_;
goto v___jp_3042_;
}
else
{
uint8_t v___x_3073_; 
v___x_3073_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3064_);
v___y_3043_ = v___y_3069_;
v___y_3044_ = v___y_3066_;
v___y_3045_ = v___y_3071_;
v___y_3046_ = v___y_3067_;
v___y_3047_ = v___y_3070_;
v___y_3048_ = v___y_3068_;
v___y_3049_ = v___x_3073_;
goto v___jp_3042_;
}
}
v___jp_3074_:
{
if (v___y_3082_ == 0)
{
lean_dec_ref(v___y_3075_);
v___y_3066_ = v___y_3079_;
v___y_3067_ = v___y_3081_;
v___y_3068_ = v___y_3080_;
v___y_3069_ = v___y_3078_;
v___y_3070_ = v___y_3077_;
v___y_3071_ = v___y_3076_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3083_; 
lean_dec_ref(v___x_3064_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v___x_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___y_3075_);
return v___x_3083_;
}
}
v___jp_3084_:
{
uint8_t v___x_3092_; 
v___x_3092_ = l_Lean_Exception_isInterrupt(v_a_3091_);
if (v___x_3092_ == 0)
{
uint8_t v___x_3093_; 
lean_inc_ref(v_a_3091_);
v___x_3093_ = l_Lean_Exception_isRuntime(v_a_3091_);
v___y_3075_ = v_a_3091_;
v___y_3076_ = v___y_3085_;
v___y_3077_ = v___y_3087_;
v___y_3078_ = v___y_3086_;
v___y_3079_ = v___y_3089_;
v___y_3080_ = v___y_3088_;
v___y_3081_ = v___y_3090_;
v___y_3082_ = v___x_3093_;
goto v___jp_3074_;
}
else
{
v___y_3075_ = v_a_3091_;
v___y_3076_ = v___y_3085_;
v___y_3077_ = v___y_3087_;
v___y_3078_ = v___y_3086_;
v___y_3079_ = v___y_3089_;
v___y_3080_ = v___y_3088_;
v___y_3081_ = v___y_3090_;
v___y_3082_ = v___x_3092_;
goto v___jp_3074_;
}
}
v___jp_3094_:
{
lean_object* v___x_3101_; 
lean_inc_ref(v___x_3064_);
v___x_3101_ = l_Lean_Meta_mkDecide(v___x_3064_, v___y_3099_, v___y_3097_, v___y_3096_, v___y_3095_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; uint8_t v_foApprox_3104_; uint8_t v_ctxApprox_3105_; uint8_t v_quasiPatternApprox_3106_; uint8_t v_constApprox_3107_; uint8_t v_isDefEqStuckEx_3108_; uint8_t v_unificationHints_3109_; uint8_t v_proofIrrelevance_3110_; uint8_t v_assignSyntheticOpaque_3111_; uint8_t v_offsetCnstrs_3112_; uint8_t v_etaStruct_3113_; uint8_t v_univApprox_3114_; uint8_t v_iota_3115_; uint8_t v_beta_3116_; uint8_t v_proj_3117_; uint8_t v_zeta_3118_; uint8_t v_zetaDelta_3119_; uint8_t v_zetaUnused_3120_; uint8_t v_zetaHave_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3183_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref(v___x_3101_);
v___x_3103_ = l_Lean_Meta_Context_config(v___y_3099_);
v_foApprox_3104_ = lean_ctor_get_uint8(v___x_3103_, 0);
v_ctxApprox_3105_ = lean_ctor_get_uint8(v___x_3103_, 1);
v_quasiPatternApprox_3106_ = lean_ctor_get_uint8(v___x_3103_, 2);
v_constApprox_3107_ = lean_ctor_get_uint8(v___x_3103_, 3);
v_isDefEqStuckEx_3108_ = lean_ctor_get_uint8(v___x_3103_, 4);
v_unificationHints_3109_ = lean_ctor_get_uint8(v___x_3103_, 5);
v_proofIrrelevance_3110_ = lean_ctor_get_uint8(v___x_3103_, 6);
v_assignSyntheticOpaque_3111_ = lean_ctor_get_uint8(v___x_3103_, 7);
v_offsetCnstrs_3112_ = lean_ctor_get_uint8(v___x_3103_, 8);
v_etaStruct_3113_ = lean_ctor_get_uint8(v___x_3103_, 10);
v_univApprox_3114_ = lean_ctor_get_uint8(v___x_3103_, 11);
v_iota_3115_ = lean_ctor_get_uint8(v___x_3103_, 12);
v_beta_3116_ = lean_ctor_get_uint8(v___x_3103_, 13);
v_proj_3117_ = lean_ctor_get_uint8(v___x_3103_, 14);
v_zeta_3118_ = lean_ctor_get_uint8(v___x_3103_, 15);
v_zetaDelta_3119_ = lean_ctor_get_uint8(v___x_3103_, 16);
v_zetaUnused_3120_ = lean_ctor_get_uint8(v___x_3103_, 17);
v_zetaHave_3121_ = lean_ctor_get_uint8(v___x_3103_, 18);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3123_ = v___x_3103_;
v_isShared_3124_ = v_isSharedCheck_3183_;
goto v_resetjp_3122_;
}
else
{
lean_dec(v___x_3103_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3183_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
uint8_t v_trackZetaDelta_3125_; lean_object* v_zetaDeltaSet_3126_; lean_object* v_lctx_3127_; lean_object* v_localInstances_3128_; lean_object* v_defEqCtx_x3f_3129_; lean_object* v_synthPendingDepth_3130_; lean_object* v_canUnfold_x3f_3131_; uint8_t v_univApprox_3132_; uint8_t v_inTypeClassResolution_3133_; uint8_t v_cacheInferType_3134_; uint8_t v___x_3135_; lean_object* v_config_3137_; 
v_trackZetaDelta_3125_ = lean_ctor_get_uint8(v___y_3099_, sizeof(void*)*7);
v_zetaDeltaSet_3126_ = lean_ctor_get(v___y_3099_, 1);
v_lctx_3127_ = lean_ctor_get(v___y_3099_, 2);
v_localInstances_3128_ = lean_ctor_get(v___y_3099_, 3);
v_defEqCtx_x3f_3129_ = lean_ctor_get(v___y_3099_, 4);
v_synthPendingDepth_3130_ = lean_ctor_get(v___y_3099_, 5);
v_canUnfold_x3f_3131_ = lean_ctor_get(v___y_3099_, 6);
v_univApprox_3132_ = lean_ctor_get_uint8(v___y_3099_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3133_ = lean_ctor_get_uint8(v___y_3099_, sizeof(void*)*7 + 2);
v_cacheInferType_3134_ = lean_ctor_get_uint8(v___y_3099_, sizeof(void*)*7 + 3);
v___x_3135_ = 1;
if (v_isShared_3124_ == 0)
{
v_config_3137_ = v___x_3123_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 0, v_foApprox_3104_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 1, v_ctxApprox_3105_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 2, v_quasiPatternApprox_3106_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 3, v_constApprox_3107_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 4, v_isDefEqStuckEx_3108_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 5, v_unificationHints_3109_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 6, v_proofIrrelevance_3110_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 7, v_assignSyntheticOpaque_3111_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 8, v_offsetCnstrs_3112_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 10, v_etaStruct_3113_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 11, v_univApprox_3114_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 12, v_iota_3115_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 13, v_beta_3116_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 14, v_proj_3117_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 15, v_zeta_3118_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 16, v_zetaDelta_3119_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 17, v_zetaUnused_3120_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, 18, v_zetaHave_3121_);
v_config_3137_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
uint64_t v___x_3138_; uint64_t v___x_3139_; uint64_t v___x_3140_; uint64_t v___x_3141_; uint64_t v___x_3142_; uint64_t v_key_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_ctor_set_uint8(v_config_3137_, 9, v___x_3135_);
v___x_3138_ = l_Lean_Meta_Context_configKey(v___y_3099_);
v___x_3139_ = 2ULL;
v___x_3140_ = lean_uint64_shift_right(v___x_3138_, v___x_3139_);
v___x_3141_ = lean_uint64_shift_left(v___x_3140_, v___x_3139_);
v___x_3142_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_3143_ = lean_uint64_lor(v___x_3141_, v___x_3142_);
v___x_3144_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3144_, 0, v_config_3137_);
lean_ctor_set_uint64(v___x_3144_, sizeof(void*)*1, v_key_3143_);
lean_inc(v_canUnfold_x3f_3131_);
lean_inc(v_synthPendingDepth_3130_);
lean_inc(v_defEqCtx_x3f_3129_);
lean_inc_ref(v_localInstances_3128_);
lean_inc_ref(v_lctx_3127_);
lean_inc(v_zetaDeltaSet_3126_);
v___x_3145_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
lean_ctor_set(v___x_3145_, 1, v_zetaDeltaSet_3126_);
lean_ctor_set(v___x_3145_, 2, v_lctx_3127_);
lean_ctor_set(v___x_3145_, 3, v_localInstances_3128_);
lean_ctor_set(v___x_3145_, 4, v_defEqCtx_x3f_3129_);
lean_ctor_set(v___x_3145_, 5, v_synthPendingDepth_3130_);
lean_ctor_set(v___x_3145_, 6, v_canUnfold_x3f_3131_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*7, v_trackZetaDelta_3125_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*7 + 1, v_univApprox_3132_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3133_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*7 + 3, v_cacheInferType_3134_);
lean_inc(v___y_3095_);
lean_inc_ref(v___y_3096_);
lean_inc(v___y_3097_);
lean_inc(v_a_3102_);
v___x_3146_ = lean_whnf(v_a_3102_, v___x_3145_, v___y_3097_, v___y_3096_, v___y_3095_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref(v___x_3146_);
v___x_3148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_3149_ = l_Lean_Expr_isConstOf(v_a_3147_, v___x_3148_);
lean_dec(v_a_3147_);
if (v___x_3149_ == 0)
{
lean_dec(v_a_3102_);
v___y_3066_ = v___y_3098_;
v___y_3067_ = v___y_3100_;
v___y_3068_ = v___y_3099_;
v___y_3069_ = v___y_3097_;
v___y_3070_ = v___y_3096_;
v___y_3071_ = v___y_3095_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3150_; 
lean_inc(v_a_3102_);
v___x_3150_ = l_Lean_Meta_mkEqRefl(v_a_3102_, v___y_3099_, v___y_3097_, v___y_3096_, v___y_3095_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3152_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref(v___x_3150_);
lean_inc(v_mvarId_2916_);
v___x_3152_ = l_Lean_MVarId_getType(v_mvarId_2916_, v___y_3099_, v___y_3097_, v___y_3096_, v___y_3095_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v_nargs_3154_; lean_object* v___x_3155_; lean_object* v_dummy_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3152_);
v_nargs_3154_ = l_Lean_Expr_getAppNumArgs(v_a_3102_);
v___x_3155_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_3156_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_3154_);
v___x_3157_ = lean_mk_array(v_nargs_3154_, v_dummy_3156_);
v___x_3158_ = lean_unsigned_to_nat(1u);
v___x_3159_ = lean_nat_sub(v_nargs_3154_, v___x_3158_);
lean_dec(v_nargs_3154_);
v___x_3160_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3102_, v___x_3157_, v___x_3159_);
v___x_3161_ = lean_array_push(v___x_3160_, v_a_3151_);
v___x_3162_ = l_Lean_mkAppN(v___x_3155_, v___x_3161_);
lean_dec_ref(v___x_3161_);
lean_inc(v_val_2947_);
v___x_3163_ = l_Lean_LocalDecl_toExpr(v_val_2947_);
v___x_3164_ = l_Lean_Meta_mkAbsurd(v_a_3153_, v___x_3163_, v___x_3162_, v___y_3099_, v___y_3097_, v___y_3096_, v___y_3095_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
lean_inc(v_mvarId_2916_);
v___x_3166_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2916_, v_a_3165_, v___y_3097_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v___x_3064_);
lean_dec(v_val_2947_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v___x_3166_, 0);
lean_dec(v_unused_3176_);
v___x_3168_ = v___x_3166_;
v_isShared_3169_ = v_isSharedCheck_3175_;
goto v_resetjp_3167_;
}
else
{
lean_dec(v___x_3166_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3175_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = lean_box(v___x_2926_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set_tag(v___x_3168_, 1);
lean_ctor_set(v___x_3168_, 0, v___x_3170_);
v___x_3172_ = v___x_3168_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; 
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_2951_);
v_a_2933_ = v___x_3173_;
goto v___jp_2932_;
}
}
}
else
{
lean_object* v_a_3177_; 
v_a_3177_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3177_);
lean_dec_ref(v___x_3166_);
v___y_3085_ = v___y_3095_;
v___y_3086_ = v___y_3097_;
v___y_3087_ = v___y_3096_;
v___y_3088_ = v___y_3099_;
v___y_3089_ = v___y_3098_;
v___y_3090_ = v___y_3100_;
v_a_3091_ = v_a_3177_;
goto v___jp_3084_;
}
}
else
{
lean_object* v_a_3178_; 
v_a_3178_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3178_);
lean_dec_ref(v___x_3164_);
v___y_3085_ = v___y_3095_;
v___y_3086_ = v___y_3097_;
v___y_3087_ = v___y_3096_;
v___y_3088_ = v___y_3099_;
v___y_3089_ = v___y_3098_;
v___y_3090_ = v___y_3100_;
v_a_3091_ = v_a_3178_;
goto v___jp_3084_;
}
}
else
{
lean_object* v_a_3179_; 
lean_dec(v_a_3151_);
lean_dec(v_a_3102_);
v_a_3179_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3179_);
lean_dec_ref(v___x_3152_);
v___y_3085_ = v___y_3095_;
v___y_3086_ = v___y_3097_;
v___y_3087_ = v___y_3096_;
v___y_3088_ = v___y_3099_;
v___y_3089_ = v___y_3098_;
v___y_3090_ = v___y_3100_;
v_a_3091_ = v_a_3179_;
goto v___jp_3084_;
}
}
else
{
lean_object* v_a_3180_; 
lean_dec(v_a_3102_);
v_a_3180_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3150_);
v___y_3085_ = v___y_3095_;
v___y_3086_ = v___y_3097_;
v___y_3087_ = v___y_3096_;
v___y_3088_ = v___y_3099_;
v___y_3089_ = v___y_3098_;
v___y_3090_ = v___y_3100_;
v_a_3091_ = v_a_3180_;
goto v___jp_3084_;
}
}
}
else
{
lean_object* v_a_3181_; 
lean_dec(v_a_3102_);
v_a_3181_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3181_);
lean_dec_ref(v___x_3146_);
v___y_3085_ = v___y_3095_;
v___y_3086_ = v___y_3097_;
v___y_3087_ = v___y_3096_;
v___y_3088_ = v___y_3099_;
v___y_3089_ = v___y_3098_;
v___y_3090_ = v___y_3100_;
v_a_3091_ = v_a_3181_;
goto v___jp_3084_;
}
}
}
}
else
{
lean_object* v_a_3184_; 
v_a_3184_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v___x_3101_);
v___y_3085_ = v___y_3095_;
v___y_3086_ = v___y_3097_;
v___y_3087_ = v___y_3096_;
v___y_3088_ = v___y_3099_;
v___y_3089_ = v___y_3098_;
v___y_3090_ = v___y_3100_;
v_a_3091_ = v_a_3184_;
goto v___jp_3084_;
}
}
v___jp_3185_:
{
if (v___y_3192_ == 0)
{
v___y_3066_ = v___y_3189_;
v___y_3067_ = v___y_3191_;
v___y_3068_ = v___y_3190_;
v___y_3069_ = v___y_3188_;
v___y_3070_ = v___y_3187_;
v___y_3071_ = v___y_3186_;
goto v___jp_3065_;
}
else
{
v___y_3095_ = v___y_3186_;
v___y_3096_ = v___y_3187_;
v___y_3097_ = v___y_3188_;
v___y_3098_ = v___y_3189_;
v___y_3099_ = v___y_3190_;
v___y_3100_ = v___y_3191_;
goto v___jp_3094_;
}
}
v___jp_3193_:
{
if (v___y_3201_ == 0)
{
lean_dec_ref(v___y_3197_);
v___y_3186_ = v___y_3194_;
v___y_3187_ = v___y_3196_;
v___y_3188_ = v___y_3195_;
v___y_3189_ = v___y_3199_;
v___y_3190_ = v___y_3198_;
v___y_3191_ = v___y_3200_;
v___y_3192_ = v___x_3020_;
goto v___jp_3185_;
}
else
{
uint8_t v___x_3202_; 
v___x_3202_ = l_Lean_Expr_hasFVar(v___y_3197_);
lean_dec_ref(v___y_3197_);
if (v___x_3202_ == 0)
{
v___y_3095_ = v___y_3194_;
v___y_3096_ = v___y_3196_;
v___y_3097_ = v___y_3195_;
v___y_3098_ = v___y_3199_;
v___y_3099_ = v___y_3198_;
v___y_3100_ = v___y_3200_;
goto v___jp_3094_;
}
else
{
v___y_3186_ = v___y_3194_;
v___y_3187_ = v___y_3196_;
v___y_3188_ = v___y_3195_;
v___y_3189_ = v___y_3199_;
v___y_3190_ = v___y_3198_;
v___y_3191_ = v___y_3200_;
v___y_3192_ = v___x_3020_;
goto v___jp_3185_;
}
}
}
v___jp_3203_:
{
lean_object* v___x_3211_; 
lean_inc_ref(v___x_3064_);
v___x_3211_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3064_, v___y_3206_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; uint8_t v___x_3213_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref(v___x_3211_);
v___x_3213_ = l_Lean_Expr_hasMVar(v_a_3212_);
if (v___x_3213_ == 0)
{
v___y_3194_ = v___y_3204_;
v___y_3195_ = v___y_3206_;
v___y_3196_ = v___y_3205_;
v___y_3197_ = v_a_3212_;
v___y_3198_ = v___y_3207_;
v___y_3199_ = v___y_3208_;
v___y_3200_ = v___y_3209_;
v___y_3201_ = v___y_3210_;
goto v___jp_3193_;
}
else
{
v___y_3194_ = v___y_3204_;
v___y_3195_ = v___y_3206_;
v___y_3196_ = v___y_3205_;
v___y_3197_ = v_a_3212_;
v___y_3198_ = v___y_3207_;
v___y_3199_ = v___y_3208_;
v___y_3200_ = v___y_3209_;
v___y_3201_ = v___x_3020_;
goto v___jp_3193_;
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v___x_3064_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3214_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3211_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3211_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
v___jp_3222_:
{
if (v___y_3229_ == 0)
{
v___y_3066_ = v___y_3226_;
v___y_3067_ = v___y_3228_;
v___y_3068_ = v___y_3227_;
v___y_3069_ = v___y_3225_;
v___y_3070_ = v___y_3224_;
v___y_3071_ = v___y_3223_;
goto v___jp_3065_;
}
else
{
v___y_3204_ = v___y_3223_;
v___y_3205_ = v___y_3224_;
v___y_3206_ = v___y_3225_;
v___y_3207_ = v___y_3227_;
v___y_3208_ = v___y_3226_;
v___y_3209_ = v___y_3228_;
v___y_3210_ = v___y_3229_;
goto v___jp_3203_;
}
}
v___jp_3230_:
{
uint8_t v_useDecide_3237_; 
v_useDecide_3237_ = lean_ctor_get_uint8(v_config_2915_, sizeof(void*)*1);
if (v_useDecide_3237_ == 0)
{
v___y_3223_ = v___y_3236_;
v___y_3224_ = v___y_3235_;
v___y_3225_ = v___y_3234_;
v___y_3226_ = v___y_3231_;
v___y_3227_ = v___y_3233_;
v___y_3228_ = v_isHEq_3232_;
v___y_3229_ = v___x_3020_;
goto v___jp_3222_;
}
else
{
uint8_t v___x_3238_; 
v___x_3238_ = l_Lean_Expr_hasFVar(v___x_3064_);
if (v___x_3238_ == 0)
{
v___y_3204_ = v___y_3236_;
v___y_3205_ = v___y_3235_;
v___y_3206_ = v___y_3234_;
v___y_3207_ = v___y_3233_;
v___y_3208_ = v___y_3231_;
v___y_3209_ = v_isHEq_3232_;
v___y_3210_ = v_useDecide_3237_;
goto v___jp_3203_;
}
else
{
v___y_3223_ = v___y_3236_;
v___y_3224_ = v___y_3235_;
v___y_3225_ = v___y_3234_;
v___y_3226_ = v___y_3231_;
v___y_3227_ = v___y_3233_;
v___y_3228_ = v_isHEq_3232_;
v___y_3229_ = v___x_3020_;
goto v___jp_3222_;
}
}
}
v___jp_3239_:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_Meta_isExprDefEq(v___y_3245_, v___y_3244_, v___y_3240_, v___y_3242_, v___y_3246_, v___y_3241_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; uint8_t v___x_3249_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref(v___x_3247_);
v___x_3249_ = lean_unbox(v_a_3248_);
lean_dec(v_a_3248_);
if (v___x_3249_ == 0)
{
v___y_3231_ = v___y_3243_;
v_isHEq_3232_ = v___x_2926_;
v___y_3233_ = v___y_3240_;
v___y_3234_ = v___y_3242_;
v___y_3235_ = v___y_3246_;
v___y_3236_ = v___y_3241_;
goto v___jp_3230_;
}
else
{
lean_object* v___x_3250_; 
lean_dec_ref(v___x_3064_);
lean_dec_ref(v_config_2915_);
lean_inc(v_mvarId_2916_);
v___x_3250_ = l_Lean_MVarId_getType(v_mvarId_2916_, v___y_3240_, v___y_3242_, v___y_3246_, v___y_3241_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref(v___x_3250_);
v___x_3252_ = l_Lean_LocalDecl_toExpr(v_val_2947_);
v___x_3253_ = l_Lean_Meta_mkEqOfHEq(v___x_3252_, v___x_2926_, v___y_3240_, v___y_3242_, v___y_3246_, v___y_3241_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3255_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref(v___x_3253_);
v___x_3255_ = l_Lean_Meta_mkNoConfusion(v_a_3251_, v_a_3254_, v___y_3240_, v___y_3242_, v___y_3246_, v___y_3241_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref(v___x_3255_);
v___x_3257_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2916_, v_a_3256_, v___y_3242_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_dec_ref(v___x_3257_);
v___x_3258_ = lean_box(v___x_2926_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v___x_2951_);
v_a_2933_ = v___x_3260_;
goto v___jp_2932_;
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
v_a_3261_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3257_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3257_);
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
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3269_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3255_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3255_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v_a_3251_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3277_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3253_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3253_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3285_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3250_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3250_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec_ref(v___x_3064_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3293_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3247_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3247_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
v___jp_3301_:
{
lean_object* v___x_3307_; 
lean_inc_ref(v___x_3064_);
v___x_3307_ = l_Lean_Meta_matchHEq_x3f(v___x_3064_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref(v___x_3307_);
if (lean_obj_tag(v_a_3308_) == 1)
{
lean_object* v_val_3309_; lean_object* v_snd_3310_; lean_object* v_snd_3311_; lean_object* v_fst_3312_; lean_object* v_fst_3313_; lean_object* v_fst_3314_; lean_object* v_snd_3315_; lean_object* v___x_3316_; 
v_val_3309_ = lean_ctor_get(v_a_3308_, 0);
lean_inc(v_val_3309_);
lean_dec_ref(v_a_3308_);
v_snd_3310_ = lean_ctor_get(v_val_3309_, 1);
lean_inc(v_snd_3310_);
v_snd_3311_ = lean_ctor_get(v_snd_3310_, 1);
lean_inc(v_snd_3311_);
v_fst_3312_ = lean_ctor_get(v_val_3309_, 0);
lean_inc(v_fst_3312_);
lean_dec(v_val_3309_);
v_fst_3313_ = lean_ctor_get(v_snd_3310_, 0);
lean_inc(v_fst_3313_);
lean_dec(v_snd_3310_);
v_fst_3314_ = lean_ctor_get(v_snd_3311_, 0);
lean_inc(v_fst_3314_);
v_snd_3315_ = lean_ctor_get(v_snd_3311_, 1);
lean_inc(v_snd_3315_);
lean_dec(v_snd_3311_);
v___x_3316_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3313_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref(v___x_3316_);
if (lean_obj_tag(v_a_3317_) == 1)
{
lean_object* v_val_3318_; lean_object* v___x_3319_; 
v_val_3318_ = lean_ctor_get(v_a_3317_, 0);
lean_inc(v_val_3318_);
lean_dec_ref(v_a_3317_);
v___x_3319_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3315_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref(v___x_3319_);
if (lean_obj_tag(v_a_3320_) == 1)
{
lean_object* v_toConstantVal_3321_; lean_object* v_val_3322_; lean_object* v_toConstantVal_3323_; lean_object* v_name_3324_; lean_object* v_name_3325_; uint8_t v___x_3326_; 
v_toConstantVal_3321_ = lean_ctor_get(v_val_3318_, 0);
lean_inc_ref(v_toConstantVal_3321_);
lean_dec(v_val_3318_);
v_val_3322_ = lean_ctor_get(v_a_3320_, 0);
lean_inc(v_val_3322_);
lean_dec_ref(v_a_3320_);
v_toConstantVal_3323_ = lean_ctor_get(v_val_3322_, 0);
lean_inc_ref(v_toConstantVal_3323_);
lean_dec(v_val_3322_);
v_name_3324_ = lean_ctor_get(v_toConstantVal_3321_, 0);
lean_inc(v_name_3324_);
lean_dec_ref(v_toConstantVal_3321_);
v_name_3325_ = lean_ctor_get(v_toConstantVal_3323_, 0);
lean_inc(v_name_3325_);
lean_dec_ref(v_toConstantVal_3323_);
v___x_3326_ = lean_name_eq(v_name_3324_, v_name_3325_);
lean_dec(v_name_3325_);
lean_dec(v_name_3324_);
if (v___x_3326_ == 0)
{
v___y_3240_ = v___y_3303_;
v___y_3241_ = v___y_3306_;
v___y_3242_ = v___y_3304_;
v___y_3243_ = v_isEq_3302_;
v___y_3244_ = v_fst_3314_;
v___y_3245_ = v_fst_3312_;
v___y_3246_ = v___y_3305_;
goto v___jp_3239_;
}
else
{
if (v___x_3020_ == 0)
{
lean_dec(v_fst_3314_);
lean_dec(v_fst_3312_);
v___y_3231_ = v_isEq_3302_;
v_isHEq_3232_ = v___x_2926_;
v___y_3233_ = v___y_3303_;
v___y_3234_ = v___y_3304_;
v___y_3235_ = v___y_3305_;
v___y_3236_ = v___y_3306_;
goto v___jp_3230_;
}
else
{
v___y_3240_ = v___y_3303_;
v___y_3241_ = v___y_3306_;
v___y_3242_ = v___y_3304_;
v___y_3243_ = v_isEq_3302_;
v___y_3244_ = v_fst_3314_;
v___y_3245_ = v_fst_3312_;
v___y_3246_ = v___y_3305_;
goto v___jp_3239_;
}
}
}
else
{
lean_dec(v_a_3320_);
lean_dec(v_val_3318_);
lean_dec(v_fst_3314_);
lean_dec(v_fst_3312_);
v___y_3231_ = v_isEq_3302_;
v_isHEq_3232_ = v___x_2926_;
v___y_3233_ = v___y_3303_;
v___y_3234_ = v___y_3304_;
v___y_3235_ = v___y_3305_;
v___y_3236_ = v___y_3306_;
goto v___jp_3230_;
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec(v_val_3318_);
lean_dec(v_fst_3314_);
lean_dec(v_fst_3312_);
lean_dec_ref(v___x_3064_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3327_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3319_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3319_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
lean_dec(v_a_3317_);
lean_dec(v_snd_3315_);
lean_dec(v_fst_3314_);
lean_dec(v_fst_3312_);
v___y_3231_ = v_isEq_3302_;
v_isHEq_3232_ = v___x_2926_;
v___y_3233_ = v___y_3303_;
v___y_3234_ = v___y_3304_;
v___y_3235_ = v___y_3305_;
v___y_3236_ = v___y_3306_;
goto v___jp_3230_;
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_snd_3315_);
lean_dec(v_fst_3314_);
lean_dec(v_fst_3312_);
lean_dec_ref(v___x_3064_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3335_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3316_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3316_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
else
{
lean_dec(v_a_3308_);
v___y_3231_ = v_isEq_3302_;
v_isHEq_3232_ = v___x_3020_;
v___y_3233_ = v___y_3303_;
v___y_3234_ = v___y_3304_;
v___y_3235_ = v___y_3305_;
v___y_3236_ = v___y_3306_;
goto v___jp_3230_;
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec_ref(v___x_3064_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3343_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3307_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3307_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
v___jp_3351_:
{
lean_object* v___x_3356_; 
lean_inc_ref(v___x_3064_);
v___x_3356_ = l_Lean_Meta_matchEq_x3f(v___x_3064_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref(v___x_3356_);
if (lean_obj_tag(v_a_3357_) == 1)
{
lean_object* v_val_3358_; lean_object* v_snd_3359_; lean_object* v_fst_3360_; lean_object* v_snd_3361_; lean_object* v___x_3362_; 
v_val_3358_ = lean_ctor_get(v_a_3357_, 0);
lean_inc(v_val_3358_);
lean_dec_ref(v_a_3357_);
v_snd_3359_ = lean_ctor_get(v_val_3358_, 1);
lean_inc(v_snd_3359_);
lean_dec(v_val_3358_);
v_fst_3360_ = lean_ctor_get(v_snd_3359_, 0);
lean_inc(v_fst_3360_);
v_snd_3361_ = lean_ctor_get(v_snd_3359_, 1);
lean_inc(v_snd_3361_);
lean_dec(v_snd_3359_);
v___x_3362_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3360_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref(v___x_3362_);
if (lean_obj_tag(v_a_3363_) == 1)
{
lean_object* v_val_3364_; lean_object* v___x_3365_; 
v_val_3364_ = lean_ctor_get(v_a_3363_, 0);
lean_inc(v_val_3364_);
lean_dec_ref(v_a_3363_);
v___x_3365_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3361_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3366_);
lean_dec_ref(v___x_3365_);
if (lean_obj_tag(v_a_3366_) == 1)
{
lean_object* v_toConstantVal_3367_; lean_object* v_val_3368_; lean_object* v_toConstantVal_3369_; lean_object* v_name_3370_; lean_object* v_name_3371_; uint8_t v___x_3372_; 
v_toConstantVal_3367_ = lean_ctor_get(v_val_3364_, 0);
lean_inc_ref(v_toConstantVal_3367_);
lean_dec(v_val_3364_);
v_val_3368_ = lean_ctor_get(v_a_3366_, 0);
lean_inc(v_val_3368_);
lean_dec_ref(v_a_3366_);
v_toConstantVal_3369_ = lean_ctor_get(v_val_3368_, 0);
lean_inc_ref(v_toConstantVal_3369_);
lean_dec(v_val_3368_);
v_name_3370_ = lean_ctor_get(v_toConstantVal_3367_, 0);
lean_inc(v_name_3370_);
lean_dec_ref(v_toConstantVal_3367_);
v_name_3371_ = lean_ctor_get(v_toConstantVal_3369_, 0);
lean_inc(v_name_3371_);
lean_dec_ref(v_toConstantVal_3369_);
v___x_3372_ = lean_name_eq(v_name_3370_, v_name_3371_);
lean_dec(v_name_3371_);
lean_dec(v_name_3370_);
if (v___x_3372_ == 0)
{
lean_dec_ref(v___x_3064_);
lean_dec_ref(v_config_2915_);
v___y_2953_ = v___y_3354_;
v___y_2954_ = v___y_3355_;
v___y_2955_ = v___y_3352_;
v___y_2956_ = v___y_3353_;
goto v___jp_2952_;
}
else
{
if (v___x_3020_ == 0)
{
lean_del_object(v___x_2949_);
v_isEq_3302_ = v___x_2926_;
v___y_3303_ = v___y_3352_;
v___y_3304_ = v___y_3353_;
v___y_3305_ = v___y_3354_;
v___y_3306_ = v___y_3355_;
goto v___jp_3301_;
}
else
{
lean_dec_ref(v___x_3064_);
lean_dec_ref(v_config_2915_);
v___y_2953_ = v___y_3354_;
v___y_2954_ = v___y_3355_;
v___y_2955_ = v___y_3352_;
v___y_2956_ = v___y_3353_;
goto v___jp_2952_;
}
}
}
else
{
lean_dec(v_a_3366_);
lean_dec(v_val_3364_);
lean_del_object(v___x_2949_);
v_isEq_3302_ = v___x_2926_;
v___y_3303_ = v___y_3352_;
v___y_3304_ = v___y_3353_;
v___y_3305_ = v___y_3354_;
v___y_3306_ = v___y_3355_;
goto v___jp_3301_;
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v_val_3364_);
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3373_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3365_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3365_);
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
else
{
lean_dec(v_a_3363_);
lean_dec(v_snd_3361_);
lean_del_object(v___x_2949_);
v_isEq_3302_ = v___x_2926_;
v___y_3303_ = v___y_3352_;
v___y_3304_ = v___y_3353_;
v___y_3305_ = v___y_3354_;
v___y_3306_ = v___y_3355_;
goto v___jp_3301_;
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec(v_snd_3361_);
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3381_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3362_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3362_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_dec(v_a_3357_);
lean_del_object(v___x_2949_);
v_isEq_3302_ = v___x_3020_;
v___y_3303_ = v___y_3352_;
v___y_3304_ = v___y_3353_;
v___y_3305_ = v___y_3354_;
v___y_3306_ = v___y_3355_;
goto v___jp_3301_;
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3389_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3356_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3356_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
v___jp_3397_:
{
lean_object* v___x_3402_; 
lean_inc_ref(v___x_3064_);
v___x_3402_ = l_refutableHasNotBit_x3f(v___x_3064_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_a_3403_);
lean_dec_ref(v___x_3402_);
if (lean_obj_tag(v_a_3403_) == 1)
{
lean_object* v_val_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec_ref(v_config_2915_);
v_val_3404_ = lean_ctor_get(v_a_3403_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_a_3403_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3406_ = v_a_3403_;
v_isShared_3407_ = v_isSharedCheck_3443_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_val_3404_);
lean_dec(v_a_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3443_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; 
lean_inc(v_mvarId_2916_);
v___x_3408_ = l_Lean_MVarId_getType(v_mvarId_2916_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = l_Lean_LocalDecl_toExpr(v_val_2947_);
v___x_3411_ = l_Lean_Meta_mkAbsurd(v_a_3409_, v_val_3404_, v___x_3410_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v___x_3413_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref(v___x_3411_);
v___x_3413_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2916_, v_a_3412_, v___y_3399_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec_ref(v___x_3413_);
v___x_3414_ = lean_box(v___x_2926_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3414_);
v___x_3416_ = v___x_3406_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
lean_ctor_set(v___x_3417_, 1, v___x_2951_);
v_a_2933_ = v___x_3417_;
goto v___jp_2932_;
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_del_object(v___x_3406_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
v_a_3419_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3413_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3413_);
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
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_del_object(v___x_3406_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3427_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3411_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3411_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_del_object(v___x_3406_);
lean_dec(v_val_3404_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3435_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3408_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3408_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
else
{
lean_object* v___x_3444_; 
lean_dec(v_a_3403_);
lean_inc_ref(v___x_3064_);
v___x_3444_ = l_Lean_Meta_matchNe_x3f(v___x_3064_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v___x_3444_);
if (lean_obj_tag(v_a_3445_) == 1)
{
lean_object* v_val_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3515_; 
v_val_3446_ = lean_ctor_get(v_a_3445_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_a_3445_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3448_ = v_a_3445_;
v_isShared_3449_ = v_isSharedCheck_3515_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_val_3446_);
lean_dec(v_a_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3515_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v_snd_3450_; lean_object* v_fst_3451_; lean_object* v_snd_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3514_; 
v_snd_3450_ = lean_ctor_get(v_val_3446_, 1);
lean_inc(v_snd_3450_);
lean_dec(v_val_3446_);
v_fst_3451_ = lean_ctor_get(v_snd_3450_, 0);
v_snd_3452_ = lean_ctor_get(v_snd_3450_, 1);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_snd_3450_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3454_ = v_snd_3450_;
v_isShared_3455_ = v_isSharedCheck_3514_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_snd_3452_);
lean_inc(v_fst_3451_);
lean_dec(v_snd_3450_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3514_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; 
lean_inc(v_fst_3451_);
v___x_3456_ = l_Lean_Meta_isExprDefEq(v_fst_3451_, v_snd_3452_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; uint8_t v___x_3458_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref(v___x_3456_);
v___x_3458_ = lean_unbox(v_a_3457_);
lean_dec(v_a_3457_);
if (v___x_3458_ == 0)
{
lean_del_object(v___x_3454_);
lean_dec(v_fst_3451_);
lean_del_object(v___x_3448_);
v___y_3352_ = v___y_3398_;
v___y_3353_ = v___y_3399_;
v___y_3354_ = v___y_3400_;
v___y_3355_ = v___y_3401_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3459_; 
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec_ref(v_config_2915_);
lean_inc(v_mvarId_2916_);
v___x_3459_ = l_Lean_MVarId_getType(v_mvarId_2916_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref(v___x_3459_);
v___x_3461_ = l_Lean_Meta_mkEqRefl(v_fst_3451_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
v___x_3463_ = l_Lean_LocalDecl_toExpr(v_val_2947_);
v___x_3464_ = l_Lean_Meta_mkAbsurd(v_a_3460_, v_a_3462_, v___x_3463_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3466_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref(v___x_3464_);
v___x_3466_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2916_, v_a_3465_, v___y_3399_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
lean_dec_ref(v___x_3466_);
v___x_3467_ = lean_box(v___x_2926_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3467_);
v___x_3469_ = v___x_3448_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3471_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v___x_2951_);
lean_ctor_set(v___x_3454_, 0, v___x_3469_);
v___x_3471_ = v___x_3454_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v___x_2951_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
v_a_2933_ = v___x_3471_;
goto v___jp_2932_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_del_object(v___x_3454_);
lean_del_object(v___x_3448_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
v_a_3474_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3466_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3466_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_del_object(v___x_3454_);
lean_del_object(v___x_3448_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3482_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3464_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3464_);
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
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec(v_a_3460_);
lean_del_object(v___x_3454_);
lean_del_object(v___x_3448_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3490_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3461_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3461_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_del_object(v___x_3454_);
lean_dec(v_fst_3451_);
lean_del_object(v___x_3448_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_3498_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3459_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3459_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_del_object(v___x_3454_);
lean_dec(v_fst_3451_);
lean_del_object(v___x_3448_);
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3506_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3456_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3456_);
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
}
}
else
{
lean_dec(v_a_3445_);
v___y_3352_ = v___y_3398_;
v___y_3353_ = v___y_3399_;
v___y_3354_ = v___y_3400_;
v___y_3355_ = v___y_3401_;
goto v___jp_3351_;
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3516_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3444_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3444_);
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
lean_dec_ref(v___x_3064_);
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3524_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3402_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3402_);
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
else
{
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
v_a_2941_ = v___x_2992_;
goto v___jp_2940_;
}
v___jp_2952_:
{
lean_object* v___x_2957_; 
lean_inc(v_mvarId_2916_);
v___x_2957_ = l_Lean_MVarId_getType(v_mvarId_2916_, v___y_2955_, v___y_2956_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref(v___x_2957_);
v___x_2959_ = l_Lean_LocalDecl_toExpr(v_val_2947_);
v___x_2960_ = l_Lean_Meta_mkNoConfusion(v_a_2958_, v___x_2959_, v___y_2955_, v___y_2956_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref(v___x_2960_);
v___x_2962_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2916_, v_a_2961_, v___y_2956_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
lean_dec_ref(v___x_2962_);
v___x_2963_ = lean_box(v___x_2926_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2963_);
v___x_2965_ = v___x_2949_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v___x_2951_);
v_a_2933_ = v___x_2966_;
goto v___jp_2932_;
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_del_object(v___x_2949_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
v_a_2968_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2962_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2962_);
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
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_del_object(v___x_2949_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_2976_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2960_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2960_);
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
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_del_object(v___x_2949_);
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
v_a_2984_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2957_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2957_);
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
v___jp_2993_:
{
lean_object* v_searchFuel_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_searchFuel_2998_ = lean_ctor_get(v_config_2915_, 0);
v___x_2999_ = l_Lean_LocalDecl_fvarId(v_val_2947_);
lean_dec(v_val_2947_);
lean_inc(v_searchFuel_2998_);
lean_inc(v_mvarId_2916_);
v___x_3000_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2916_, v___x_2999_, v_searchFuel_2998_, v___y_2994_, v___y_2997_, v___y_2996_, v___y_2995_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; uint8_t v___x_3002_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref(v___x_3000_);
v___x_3002_ = lean_unbox(v_a_3001_);
lean_dec(v_a_3001_);
if (v___x_3002_ == 0)
{
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
v_a_2941_ = v___x_2992_;
goto v___jp_2940_;
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v___x_3003_ = lean_box(v___x_2926_);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
lean_ctor_set(v___x_3005_, 1, v___x_2951_);
v_a_2933_ = v___x_3005_;
goto v___jp_2932_;
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3006_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_3000_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3000_);
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
v___jp_3014_:
{
if (v___y_3019_ == 0)
{
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
v_a_2941_ = v___x_2992_;
goto v___jp_2940_;
}
else
{
v___y_2994_ = v___y_3015_;
v___y_2995_ = v___y_3017_;
v___y_2996_ = v___y_3016_;
v___y_2997_ = v___y_3018_;
goto v___jp_2993_;
}
}
v___jp_3021_:
{
if (v___y_3026_ == 0)
{
v___y_2994_ = v___y_3022_;
v___y_2995_ = v___y_3024_;
v___y_2996_ = v___y_3023_;
v___y_2997_ = v___y_3025_;
goto v___jp_2993_;
}
else
{
v___y_3015_ = v___y_3022_;
v___y_3016_ = v___y_3023_;
v___y_3017_ = v___y_3024_;
v___y_3018_ = v___y_3025_;
v___y_3019_ = v___x_3020_;
goto v___jp_3014_;
}
}
v___jp_3027_:
{
if (v___y_3033_ == 0)
{
v___y_3015_ = v___y_3028_;
v___y_3016_ = v___y_3030_;
v___y_3017_ = v___y_3029_;
v___y_3018_ = v___y_3031_;
v___y_3019_ = v___x_3020_;
goto v___jp_3014_;
}
else
{
v___y_3022_ = v___y_3028_;
v___y_3023_ = v___y_3030_;
v___y_3024_ = v___y_3029_;
v___y_3025_ = v___y_3031_;
v___y_3026_ = v___y_3032_;
goto v___jp_3021_;
}
}
v___jp_3034_:
{
uint8_t v_emptyType_3041_; 
v_emptyType_3041_ = lean_ctor_get_uint8(v_config_2915_, sizeof(void*)*1 + 1);
if (v_emptyType_3041_ == 0)
{
v___y_3028_ = v___y_3037_;
v___y_3029_ = v___y_3040_;
v___y_3030_ = v___y_3039_;
v___y_3031_ = v___y_3038_;
v___y_3032_ = v___y_3036_;
v___y_3033_ = v___x_3020_;
goto v___jp_3027_;
}
else
{
if (v___y_3035_ == 0)
{
v___y_3022_ = v___y_3037_;
v___y_3023_ = v___y_3039_;
v___y_3024_ = v___y_3040_;
v___y_3025_ = v___y_3038_;
v___y_3026_ = v___y_3036_;
goto v___jp_3021_;
}
else
{
v___y_3028_ = v___y_3037_;
v___y_3029_ = v___y_3040_;
v___y_3030_ = v___y_3039_;
v___y_3031_ = v___y_3038_;
v___y_3032_ = v___y_3036_;
v___y_3033_ = v___x_3020_;
goto v___jp_3027_;
}
}
}
v___jp_3042_:
{
if (v___y_3049_ == 0)
{
v___y_3035_ = v___y_3044_;
v___y_3036_ = v___y_3046_;
v___y_3037_ = v___y_3048_;
v___y_3038_ = v___y_3043_;
v___y_3039_ = v___y_3047_;
v___y_3040_ = v___y_3045_;
goto v___jp_3034_;
}
else
{
lean_object* v___x_3050_; 
lean_inc(v_val_2947_);
lean_inc(v_mvarId_2916_);
v___x_3050_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2916_, v_val_2947_, v___y_3048_, v___y_3043_, v___y_3047_, v___y_3045_);
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
v___y_3035_ = v___y_3044_;
v___y_3036_ = v___y_3046_;
v___y_3037_ = v___y_3048_;
v___y_3038_ = v___y_3043_;
v___y_3039_ = v___y_3047_;
v___y_3040_ = v___y_3045_;
goto v___jp_3034_;
}
else
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec(v_val_2947_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v___x_3053_ = lean_box(v___x_2926_);
v___x_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_2951_);
v_a_2933_ = v___x_3055_;
goto v___jp_2932_;
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v_val_2947_);
lean_del_object(v___x_2930_);
lean_dec(v_snd_2928_);
lean_dec(v_mvarId_2916_);
lean_dec_ref(v_config_2915_);
v_a_3056_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3050_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3050_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
}
}
v___jp_2932_:
{
lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_a_2933_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2934_);
v___x_2936_ = v___x_2930_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_snd_2928_);
v___x_2936_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
return v___x_2937_;
}
}
v___jp_2940_:
{
lean_object* v___x_2942_; size_t v___x_2943_; size_t v___x_2944_; lean_object* v___x_2945_; 
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2939_);
lean_ctor_set(v___x_2942_, 1, v_a_2941_);
v___x_2943_ = ((size_t)1ULL);
v___x_2944_ = lean_usize_add(v_i_2919_, v___x_2943_);
v___x_2945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2915_, v_mvarId_2916_, v_as_2917_, v_sz_2918_, v___x_2944_, v___x_2942_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
return v___x_2945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3598_, lean_object* v_mvarId_3599_, lean_object* v_as_3600_, lean_object* v_sz_3601_, lean_object* v_i_3602_, lean_object* v_b_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
size_t v_sz_boxed_3609_; size_t v_i_boxed_3610_; lean_object* v_res_3611_; 
v_sz_boxed_3609_ = lean_unbox_usize(v_sz_3601_);
lean_dec(v_sz_3601_);
v_i_boxed_3610_ = lean_unbox_usize(v_i_3602_);
lean_dec(v_i_3602_);
v_res_3611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3598_, v_mvarId_3599_, v_as_3600_, v_sz_boxed_3609_, v_i_boxed_3610_, v_b_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v_as_3600_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3615_, lean_object* v_mvarId_3616_, lean_object* v_as_3617_, size_t v_sz_3618_, size_t v_i_3619_, lean_object* v_b_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_usize_dec_lt(v_i_3619_, v_sz_3618_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; 
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v_b_3620_);
return v___x_3627_;
}
else
{
lean_object* v_snd_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_4316_; 
v_snd_3628_ = lean_ctor_get(v_b_3620_, 1);
v_isSharedCheck_4316_ = !lean_is_exclusive(v_b_3620_);
if (v_isSharedCheck_4316_ == 0)
{
lean_object* v_unused_4317_; 
v_unused_4317_ = lean_ctor_get(v_b_3620_, 0);
lean_dec(v_unused_4317_);
v___x_3630_ = v_b_3620_;
v_isShared_3631_ = v_isSharedCheck_4316_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_snd_3628_);
lean_dec(v_b_3620_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_4316_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v_a_3633_; lean_object* v___x_3639_; lean_object* v_a_3641_; lean_object* v_a_3646_; 
v___x_3639_ = lean_box(0);
v_a_3646_ = lean_array_uget(v_as_3617_, v_i_3619_);
if (lean_obj_tag(v_a_3646_) == 0)
{
lean_del_object(v___x_3630_);
v_a_3641_ = v_snd_3628_;
goto v___jp_3640_;
}
else
{
lean_object* v_val_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_4315_; 
v_val_3647_ = lean_ctor_get(v_a_3646_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v_a_3646_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_3649_ = v_a_3646_;
v_isShared_3650_ = v_isSharedCheck_4315_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_val_3647_);
lean_dec(v_a_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_4315_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3651_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___x_3693_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; uint8_t v___y_3721_; uint8_t v___x_3722_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; uint8_t v___y_3728_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; uint8_t v___y_3733_; lean_object* v___y_3734_; uint8_t v___y_3735_; uint8_t v___y_3737_; uint8_t v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3745_; uint8_t v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; uint8_t v___y_3750_; uint8_t v___y_3751_; 
v___x_3651_ = lean_box(0);
v___x_3693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3722_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3647_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3767_; uint8_t v___y_3769_; uint8_t v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3778_; uint8_t v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; uint8_t v___y_3783_; lean_object* v___y_3784_; uint8_t v___y_3785_; uint8_t v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; uint8_t v___y_3793_; lean_object* v_a_3794_; uint8_t v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; uint8_t v___y_3802_; lean_object* v___y_3803_; uint8_t v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; uint8_t v___y_3900_; lean_object* v___y_3901_; uint8_t v___y_3902_; uint8_t v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; uint8_t v___y_3910_; uint8_t v___y_3911_; uint8_t v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; uint8_t v___y_3919_; uint8_t v___y_3920_; uint8_t v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; uint8_t v___y_3937_; lean_object* v___y_3938_; uint8_t v___y_3939_; uint8_t v___y_3941_; uint8_t v_isHEq_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3950_; uint8_t v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; uint8_t v_isEq_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___x_4245_; 
v___x_3767_ = l_Lean_LocalDecl_type(v_val_3647_);
lean_inc_ref(v___x_3767_);
v___x_4245_ = l_Lean_Meta_matchNot_x3f(v___x_3767_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref(v___x_4245_);
if (lean_obj_tag(v_a_4246_) == 1)
{
lean_object* v_val_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4306_; 
v_val_4247_ = lean_ctor_get(v_a_4246_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_a_4246_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4249_ = v_a_4246_;
v_isShared_4250_ = v_isSharedCheck_4306_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_val_4247_);
lean_dec(v_a_4246_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4306_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4247_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref(v___x_4251_);
if (lean_obj_tag(v_a_4252_) == 1)
{
lean_object* v_val_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4297_; 
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec_ref(v_config_3615_);
v_val_4253_ = lean_ctor_get(v_a_4252_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v_a_4252_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4255_ = v_a_4252_;
v_isShared_4256_ = v_isSharedCheck_4297_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_val_4253_);
lean_dec(v_a_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4297_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4257_; 
lean_inc(v_mvarId_3616_);
v___x_4257_ = l_Lean_MVarId_getType(v_mvarId_3616_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref(v___x_4257_);
v___x_4259_ = l_Lean_LocalDecl_toExpr(v_val_3647_);
v___x_4260_ = l_Lean_mkFVar(v_val_4253_);
v___x_4261_ = l_Lean_Expr_app___override(v___x_4259_, v___x_4260_);
v___x_4262_ = l_Lean_Meta_mkFalseElim(v_a_4258_, v___x_4261_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4264_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref(v___x_4262_);
v___x_4264_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3616_, v_a_4263_, v___y_3622_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v___x_4265_; lean_object* v___x_4267_; 
lean_dec_ref(v___x_4264_);
v___x_4265_ = lean_box(v___x_3626_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v___x_4265_);
v___x_4267_ = v___x_4255_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4265_);
v___x_4267_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
lean_ctor_set(v___x_4268_, 1, v___x_3651_);
if (v_isShared_4250_ == 0)
{
lean_ctor_set_tag(v___x_4249_, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4268_);
v___x_4270_ = v___x_4249_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
v_a_3633_ = v___x_4270_;
goto v___jp_3632_;
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_del_object(v___x_4255_);
lean_del_object(v___x_4249_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
v_a_4273_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4264_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4264_);
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
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_del_object(v___x_4255_);
lean_del_object(v___x_4249_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
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
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_del_object(v___x_4255_);
lean_dec(v_val_4253_);
lean_del_object(v___x_4249_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_4289_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4257_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4257_);
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
}
else
{
lean_dec(v_a_4252_);
lean_del_object(v___x_4249_);
v___y_4109_ = v___y_3621_;
v___y_4110_ = v___y_3622_;
v___y_4111_ = v___y_3623_;
v___y_4112_ = v___y_3624_;
goto v___jp_4108_;
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_del_object(v___x_4249_);
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4298_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4251_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4251_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
}
else
{
lean_dec(v_a_4246_);
v___y_4109_ = v___y_3621_;
v___y_4110_ = v___y_3622_;
v___y_4111_ = v___y_3623_;
v___y_4112_ = v___y_3624_;
goto v___jp_4108_;
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4307_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4245_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4245_);
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
v___jp_3768_:
{
uint8_t v_genDiseq_3775_; 
v_genDiseq_3775_ = lean_ctor_get_uint8(v_config_3615_, sizeof(void*)*1 + 2);
if (v_genDiseq_3775_ == 0)
{
lean_dec_ref(v___x_3767_);
v___y_3745_ = v___y_3774_;
v___y_3746_ = v___y_3769_;
v___y_3747_ = v___y_3771_;
v___y_3748_ = v___y_3773_;
v___y_3749_ = v___y_3772_;
v___y_3750_ = v___y_3770_;
v___y_3751_ = v___x_3722_;
goto v___jp_3744_;
}
else
{
uint8_t v___x_3776_; 
v___x_3776_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3767_);
v___y_3745_ = v___y_3774_;
v___y_3746_ = v___y_3769_;
v___y_3747_ = v___y_3771_;
v___y_3748_ = v___y_3773_;
v___y_3749_ = v___y_3772_;
v___y_3750_ = v___y_3770_;
v___y_3751_ = v___x_3776_;
goto v___jp_3744_;
}
}
v___jp_3777_:
{
if (v___y_3785_ == 0)
{
lean_dec_ref(v___y_3778_);
v___y_3769_ = v___y_3779_;
v___y_3770_ = v___y_3783_;
v___y_3771_ = v___y_3782_;
v___y_3772_ = v___y_3781_;
v___y_3773_ = v___y_3784_;
v___y_3774_ = v___y_3780_;
goto v___jp_3768_;
}
else
{
lean_object* v___x_3786_; 
lean_dec_ref(v___x_3767_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v___x_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___y_3778_);
return v___x_3786_;
}
}
v___jp_3787_:
{
uint8_t v___x_3795_; 
v___x_3795_ = l_Lean_Exception_isInterrupt(v_a_3794_);
if (v___x_3795_ == 0)
{
uint8_t v___x_3796_; 
lean_inc_ref(v_a_3794_);
v___x_3796_ = l_Lean_Exception_isRuntime(v_a_3794_);
v___y_3778_ = v_a_3794_;
v___y_3779_ = v___y_3788_;
v___y_3780_ = v___y_3790_;
v___y_3781_ = v___y_3789_;
v___y_3782_ = v___y_3791_;
v___y_3783_ = v___y_3793_;
v___y_3784_ = v___y_3792_;
v___y_3785_ = v___x_3796_;
goto v___jp_3777_;
}
else
{
v___y_3778_ = v_a_3794_;
v___y_3779_ = v___y_3788_;
v___y_3780_ = v___y_3790_;
v___y_3781_ = v___y_3789_;
v___y_3782_ = v___y_3791_;
v___y_3783_ = v___y_3793_;
v___y_3784_ = v___y_3792_;
v___y_3785_ = v___x_3795_;
goto v___jp_3777_;
}
}
v___jp_3797_:
{
lean_object* v___x_3804_; 
lean_inc_ref(v___x_3767_);
v___x_3804_ = l_Lean_Meta_mkDecide(v___x_3767_, v___y_3801_, v___y_3800_, v___y_3803_, v___y_3799_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3806_; uint8_t v_foApprox_3807_; uint8_t v_ctxApprox_3808_; uint8_t v_quasiPatternApprox_3809_; uint8_t v_constApprox_3810_; uint8_t v_isDefEqStuckEx_3811_; uint8_t v_unificationHints_3812_; uint8_t v_proofIrrelevance_3813_; uint8_t v_assignSyntheticOpaque_3814_; uint8_t v_offsetCnstrs_3815_; uint8_t v_etaStruct_3816_; uint8_t v_univApprox_3817_; uint8_t v_iota_3818_; uint8_t v_beta_3819_; uint8_t v_proj_3820_; uint8_t v_zeta_3821_; uint8_t v_zetaDelta_3822_; uint8_t v_zetaUnused_3823_; uint8_t v_zetaHave_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3893_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref(v___x_3804_);
v___x_3806_ = l_Lean_Meta_Context_config(v___y_3801_);
v_foApprox_3807_ = lean_ctor_get_uint8(v___x_3806_, 0);
v_ctxApprox_3808_ = lean_ctor_get_uint8(v___x_3806_, 1);
v_quasiPatternApprox_3809_ = lean_ctor_get_uint8(v___x_3806_, 2);
v_constApprox_3810_ = lean_ctor_get_uint8(v___x_3806_, 3);
v_isDefEqStuckEx_3811_ = lean_ctor_get_uint8(v___x_3806_, 4);
v_unificationHints_3812_ = lean_ctor_get_uint8(v___x_3806_, 5);
v_proofIrrelevance_3813_ = lean_ctor_get_uint8(v___x_3806_, 6);
v_assignSyntheticOpaque_3814_ = lean_ctor_get_uint8(v___x_3806_, 7);
v_offsetCnstrs_3815_ = lean_ctor_get_uint8(v___x_3806_, 8);
v_etaStruct_3816_ = lean_ctor_get_uint8(v___x_3806_, 10);
v_univApprox_3817_ = lean_ctor_get_uint8(v___x_3806_, 11);
v_iota_3818_ = lean_ctor_get_uint8(v___x_3806_, 12);
v_beta_3819_ = lean_ctor_get_uint8(v___x_3806_, 13);
v_proj_3820_ = lean_ctor_get_uint8(v___x_3806_, 14);
v_zeta_3821_ = lean_ctor_get_uint8(v___x_3806_, 15);
v_zetaDelta_3822_ = lean_ctor_get_uint8(v___x_3806_, 16);
v_zetaUnused_3823_ = lean_ctor_get_uint8(v___x_3806_, 17);
v_zetaHave_3824_ = lean_ctor_get_uint8(v___x_3806_, 18);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3826_ = v___x_3806_;
v_isShared_3827_ = v_isSharedCheck_3893_;
goto v_resetjp_3825_;
}
else
{
lean_dec(v___x_3806_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3893_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
uint8_t v_trackZetaDelta_3828_; lean_object* v_zetaDeltaSet_3829_; lean_object* v_lctx_3830_; lean_object* v_localInstances_3831_; lean_object* v_defEqCtx_x3f_3832_; lean_object* v_synthPendingDepth_3833_; lean_object* v_canUnfold_x3f_3834_; uint8_t v_univApprox_3835_; uint8_t v_inTypeClassResolution_3836_; uint8_t v_cacheInferType_3837_; uint8_t v___x_3838_; lean_object* v_config_3840_; 
v_trackZetaDelta_3828_ = lean_ctor_get_uint8(v___y_3801_, sizeof(void*)*7);
v_zetaDeltaSet_3829_ = lean_ctor_get(v___y_3801_, 1);
v_lctx_3830_ = lean_ctor_get(v___y_3801_, 2);
v_localInstances_3831_ = lean_ctor_get(v___y_3801_, 3);
v_defEqCtx_x3f_3832_ = lean_ctor_get(v___y_3801_, 4);
v_synthPendingDepth_3833_ = lean_ctor_get(v___y_3801_, 5);
v_canUnfold_x3f_3834_ = lean_ctor_get(v___y_3801_, 6);
v_univApprox_3835_ = lean_ctor_get_uint8(v___y_3801_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3836_ = lean_ctor_get_uint8(v___y_3801_, sizeof(void*)*7 + 2);
v_cacheInferType_3837_ = lean_ctor_get_uint8(v___y_3801_, sizeof(void*)*7 + 3);
v___x_3838_ = 1;
if (v_isShared_3827_ == 0)
{
v_config_3840_ = v___x_3826_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 0, v_foApprox_3807_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 1, v_ctxApprox_3808_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 2, v_quasiPatternApprox_3809_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 3, v_constApprox_3810_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 4, v_isDefEqStuckEx_3811_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 5, v_unificationHints_3812_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 6, v_proofIrrelevance_3813_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 7, v_assignSyntheticOpaque_3814_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 8, v_offsetCnstrs_3815_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 10, v_etaStruct_3816_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 11, v_univApprox_3817_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 12, v_iota_3818_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 13, v_beta_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 14, v_proj_3820_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 15, v_zeta_3821_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 16, v_zetaDelta_3822_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 17, v_zetaUnused_3823_);
lean_ctor_set_uint8(v_reuseFailAlloc_3892_, 18, v_zetaHave_3824_);
v_config_3840_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
uint64_t v___x_3841_; uint64_t v___x_3842_; uint64_t v___x_3843_; uint64_t v___x_3844_; uint64_t v___x_3845_; uint64_t v_key_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_ctor_set_uint8(v_config_3840_, 9, v___x_3838_);
v___x_3841_ = l_Lean_Meta_Context_configKey(v___y_3801_);
v___x_3842_ = 2ULL;
v___x_3843_ = lean_uint64_shift_right(v___x_3841_, v___x_3842_);
v___x_3844_ = lean_uint64_shift_left(v___x_3843_, v___x_3842_);
v___x_3845_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_3846_ = lean_uint64_lor(v___x_3844_, v___x_3845_);
v___x_3847_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3847_, 0, v_config_3840_);
lean_ctor_set_uint64(v___x_3847_, sizeof(void*)*1, v_key_3846_);
lean_inc(v_canUnfold_x3f_3834_);
lean_inc(v_synthPendingDepth_3833_);
lean_inc(v_defEqCtx_x3f_3832_);
lean_inc_ref(v_localInstances_3831_);
lean_inc_ref(v_lctx_3830_);
lean_inc(v_zetaDeltaSet_3829_);
v___x_3848_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
lean_ctor_set(v___x_3848_, 1, v_zetaDeltaSet_3829_);
lean_ctor_set(v___x_3848_, 2, v_lctx_3830_);
lean_ctor_set(v___x_3848_, 3, v_localInstances_3831_);
lean_ctor_set(v___x_3848_, 4, v_defEqCtx_x3f_3832_);
lean_ctor_set(v___x_3848_, 5, v_synthPendingDepth_3833_);
lean_ctor_set(v___x_3848_, 6, v_canUnfold_x3f_3834_);
lean_ctor_set_uint8(v___x_3848_, sizeof(void*)*7, v_trackZetaDelta_3828_);
lean_ctor_set_uint8(v___x_3848_, sizeof(void*)*7 + 1, v_univApprox_3835_);
lean_ctor_set_uint8(v___x_3848_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3836_);
lean_ctor_set_uint8(v___x_3848_, sizeof(void*)*7 + 3, v_cacheInferType_3837_);
lean_inc(v___y_3799_);
lean_inc_ref(v___y_3803_);
lean_inc(v___y_3800_);
lean_inc(v_a_3805_);
v___x_3849_ = lean_whnf(v_a_3805_, v___x_3848_, v___y_3800_, v___y_3803_, v___y_3799_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref(v___x_3849_);
v___x_3851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_3852_ = l_Lean_Expr_isConstOf(v_a_3850_, v___x_3851_);
lean_dec(v_a_3850_);
if (v___x_3852_ == 0)
{
lean_dec(v_a_3805_);
v___y_3769_ = v___y_3798_;
v___y_3770_ = v___y_3802_;
v___y_3771_ = v___y_3801_;
v___y_3772_ = v___y_3800_;
v___y_3773_ = v___y_3803_;
v___y_3774_ = v___y_3799_;
goto v___jp_3768_;
}
else
{
lean_object* v___x_3853_; 
lean_inc(v_a_3805_);
v___x_3853_ = l_Lean_Meta_mkEqRefl(v_a_3805_, v___y_3801_, v___y_3800_, v___y_3803_, v___y_3799_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3855_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref(v___x_3853_);
lean_inc(v_mvarId_3616_);
v___x_3855_ = l_Lean_MVarId_getType(v_mvarId_3616_, v___y_3801_, v___y_3800_, v___y_3803_, v___y_3799_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v_nargs_3857_; lean_object* v___x_3858_; lean_object* v_dummy_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref(v___x_3855_);
v_nargs_3857_ = l_Lean_Expr_getAppNumArgs(v_a_3805_);
v___x_3858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_3859_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_3857_);
v___x_3860_ = lean_mk_array(v_nargs_3857_, v_dummy_3859_);
v___x_3861_ = lean_unsigned_to_nat(1u);
v___x_3862_ = lean_nat_sub(v_nargs_3857_, v___x_3861_);
lean_dec(v_nargs_3857_);
v___x_3863_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3805_, v___x_3860_, v___x_3862_);
v___x_3864_ = lean_array_push(v___x_3863_, v_a_3854_);
v___x_3865_ = l_Lean_mkAppN(v___x_3858_, v___x_3864_);
lean_dec_ref(v___x_3864_);
lean_inc(v_val_3647_);
v___x_3866_ = l_Lean_LocalDecl_toExpr(v_val_3647_);
v___x_3867_ = l_Lean_Meta_mkAbsurd(v_a_3856_, v___x_3866_, v___x_3865_, v___y_3801_, v___y_3800_, v___y_3803_, v___y_3799_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3887_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3887_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3887_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; 
lean_inc(v_mvarId_3616_);
v___x_3872_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3616_, v_a_3868_, v___y_3800_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v___x_3767_);
lean_dec(v_val_3647_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; 
v_unused_3885_ = lean_ctor_get(v___x_3872_, 0);
lean_dec(v_unused_3885_);
v___x_3874_ = v___x_3872_;
v_isShared_3875_ = v_isSharedCheck_3884_;
goto v_resetjp_3873_;
}
else
{
lean_dec(v___x_3872_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3884_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3876_ = lean_box(v___x_3626_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set_tag(v___x_3874_, 1);
lean_ctor_set(v___x_3874_, 0, v___x_3876_);
v___x_3878_ = v___x_3874_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3879_; lean_object* v___x_3881_; 
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
lean_ctor_set(v___x_3879_, 1, v___x_3651_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3879_);
v___x_3881_ = v___x_3870_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
v_a_3633_ = v___x_3881_;
goto v___jp_3632_;
}
}
}
}
else
{
lean_object* v_a_3886_; 
lean_del_object(v___x_3870_);
v_a_3886_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3886_);
lean_dec_ref(v___x_3872_);
v___y_3788_ = v___y_3798_;
v___y_3789_ = v___y_3800_;
v___y_3790_ = v___y_3799_;
v___y_3791_ = v___y_3801_;
v___y_3792_ = v___y_3803_;
v___y_3793_ = v___y_3802_;
v_a_3794_ = v_a_3886_;
goto v___jp_3787_;
}
}
}
else
{
lean_object* v_a_3888_; 
v_a_3888_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3888_);
lean_dec_ref(v___x_3867_);
v___y_3788_ = v___y_3798_;
v___y_3789_ = v___y_3800_;
v___y_3790_ = v___y_3799_;
v___y_3791_ = v___y_3801_;
v___y_3792_ = v___y_3803_;
v___y_3793_ = v___y_3802_;
v_a_3794_ = v_a_3888_;
goto v___jp_3787_;
}
}
else
{
lean_object* v_a_3889_; 
lean_dec(v_a_3854_);
lean_dec(v_a_3805_);
v_a_3889_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3889_);
lean_dec_ref(v___x_3855_);
v___y_3788_ = v___y_3798_;
v___y_3789_ = v___y_3800_;
v___y_3790_ = v___y_3799_;
v___y_3791_ = v___y_3801_;
v___y_3792_ = v___y_3803_;
v___y_3793_ = v___y_3802_;
v_a_3794_ = v_a_3889_;
goto v___jp_3787_;
}
}
else
{
lean_object* v_a_3890_; 
lean_dec(v_a_3805_);
v_a_3890_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3890_);
lean_dec_ref(v___x_3853_);
v___y_3788_ = v___y_3798_;
v___y_3789_ = v___y_3800_;
v___y_3790_ = v___y_3799_;
v___y_3791_ = v___y_3801_;
v___y_3792_ = v___y_3803_;
v___y_3793_ = v___y_3802_;
v_a_3794_ = v_a_3890_;
goto v___jp_3787_;
}
}
}
else
{
lean_object* v_a_3891_; 
lean_dec(v_a_3805_);
v_a_3891_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3891_);
lean_dec_ref(v___x_3849_);
v___y_3788_ = v___y_3798_;
v___y_3789_ = v___y_3800_;
v___y_3790_ = v___y_3799_;
v___y_3791_ = v___y_3801_;
v___y_3792_ = v___y_3803_;
v___y_3793_ = v___y_3802_;
v_a_3794_ = v_a_3891_;
goto v___jp_3787_;
}
}
}
}
else
{
lean_object* v_a_3894_; 
v_a_3894_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3894_);
lean_dec_ref(v___x_3804_);
v___y_3788_ = v___y_3798_;
v___y_3789_ = v___y_3800_;
v___y_3790_ = v___y_3799_;
v___y_3791_ = v___y_3801_;
v___y_3792_ = v___y_3803_;
v___y_3793_ = v___y_3802_;
v_a_3794_ = v_a_3894_;
goto v___jp_3787_;
}
}
v___jp_3895_:
{
if (v___y_3902_ == 0)
{
v___y_3769_ = v___y_3896_;
v___y_3770_ = v___y_3900_;
v___y_3771_ = v___y_3899_;
v___y_3772_ = v___y_3898_;
v___y_3773_ = v___y_3901_;
v___y_3774_ = v___y_3897_;
goto v___jp_3768_;
}
else
{
v___y_3798_ = v___y_3896_;
v___y_3799_ = v___y_3897_;
v___y_3800_ = v___y_3898_;
v___y_3801_ = v___y_3899_;
v___y_3802_ = v___y_3900_;
v___y_3803_ = v___y_3901_;
goto v___jp_3797_;
}
}
v___jp_3903_:
{
if (v___y_3911_ == 0)
{
lean_dec_ref(v___y_3908_);
v___y_3896_ = v___y_3904_;
v___y_3897_ = v___y_3906_;
v___y_3898_ = v___y_3905_;
v___y_3899_ = v___y_3907_;
v___y_3900_ = v___y_3910_;
v___y_3901_ = v___y_3909_;
v___y_3902_ = v___x_3722_;
goto v___jp_3895_;
}
else
{
uint8_t v___x_3912_; 
v___x_3912_ = l_Lean_Expr_hasFVar(v___y_3908_);
lean_dec_ref(v___y_3908_);
if (v___x_3912_ == 0)
{
v___y_3798_ = v___y_3904_;
v___y_3799_ = v___y_3906_;
v___y_3800_ = v___y_3905_;
v___y_3801_ = v___y_3907_;
v___y_3802_ = v___y_3910_;
v___y_3803_ = v___y_3909_;
goto v___jp_3797_;
}
else
{
v___y_3896_ = v___y_3904_;
v___y_3897_ = v___y_3906_;
v___y_3898_ = v___y_3905_;
v___y_3899_ = v___y_3907_;
v___y_3900_ = v___y_3910_;
v___y_3901_ = v___y_3909_;
v___y_3902_ = v___x_3722_;
goto v___jp_3895_;
}
}
}
v___jp_3913_:
{
lean_object* v___x_3921_; 
lean_inc_ref(v___x_3767_);
v___x_3921_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3767_, v___y_3916_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; uint8_t v___x_3923_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref(v___x_3921_);
v___x_3923_ = l_Lean_Expr_hasMVar(v_a_3922_);
if (v___x_3923_ == 0)
{
v___y_3904_ = v___y_3914_;
v___y_3905_ = v___y_3916_;
v___y_3906_ = v___y_3915_;
v___y_3907_ = v___y_3917_;
v___y_3908_ = v_a_3922_;
v___y_3909_ = v___y_3918_;
v___y_3910_ = v___y_3919_;
v___y_3911_ = v___y_3920_;
goto v___jp_3903_;
}
else
{
v___y_3904_ = v___y_3914_;
v___y_3905_ = v___y_3916_;
v___y_3906_ = v___y_3915_;
v___y_3907_ = v___y_3917_;
v___y_3908_ = v_a_3922_;
v___y_3909_ = v___y_3918_;
v___y_3910_ = v___y_3919_;
v___y_3911_ = v___x_3722_;
goto v___jp_3903_;
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec_ref(v___x_3767_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_3924_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3921_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3921_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
v___jp_3932_:
{
if (v___y_3939_ == 0)
{
v___y_3769_ = v___y_3933_;
v___y_3770_ = v___y_3937_;
v___y_3771_ = v___y_3936_;
v___y_3772_ = v___y_3935_;
v___y_3773_ = v___y_3938_;
v___y_3774_ = v___y_3934_;
goto v___jp_3768_;
}
else
{
v___y_3914_ = v___y_3933_;
v___y_3915_ = v___y_3934_;
v___y_3916_ = v___y_3935_;
v___y_3917_ = v___y_3936_;
v___y_3918_ = v___y_3938_;
v___y_3919_ = v___y_3937_;
v___y_3920_ = v___y_3939_;
goto v___jp_3913_;
}
}
v___jp_3940_:
{
uint8_t v_useDecide_3947_; 
v_useDecide_3947_ = lean_ctor_get_uint8(v_config_3615_, sizeof(void*)*1);
if (v_useDecide_3947_ == 0)
{
v___y_3933_ = v___y_3941_;
v___y_3934_ = v___y_3946_;
v___y_3935_ = v___y_3944_;
v___y_3936_ = v___y_3943_;
v___y_3937_ = v_isHEq_3942_;
v___y_3938_ = v___y_3945_;
v___y_3939_ = v___x_3722_;
goto v___jp_3932_;
}
else
{
uint8_t v___x_3948_; 
v___x_3948_ = l_Lean_Expr_hasFVar(v___x_3767_);
if (v___x_3948_ == 0)
{
v___y_3914_ = v___y_3941_;
v___y_3915_ = v___y_3946_;
v___y_3916_ = v___y_3944_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v___y_3945_;
v___y_3919_ = v_isHEq_3942_;
v___y_3920_ = v_useDecide_3947_;
goto v___jp_3913_;
}
else
{
v___y_3933_ = v___y_3941_;
v___y_3934_ = v___y_3946_;
v___y_3935_ = v___y_3944_;
v___y_3936_ = v___y_3943_;
v___y_3937_ = v_isHEq_3942_;
v___y_3938_ = v___y_3945_;
v___y_3939_ = v___x_3722_;
goto v___jp_3932_;
}
}
}
v___jp_3949_:
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_Meta_isExprDefEq(v___y_3953_, v___y_3955_, v___y_3956_, v___y_3952_, v___y_3954_, v___y_3950_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; uint8_t v___x_3959_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref(v___x_3957_);
v___x_3959_ = lean_unbox(v_a_3958_);
lean_dec(v_a_3958_);
if (v___x_3959_ == 0)
{
v___y_3941_ = v___y_3951_;
v_isHEq_3942_ = v___x_3626_;
v___y_3943_ = v___y_3956_;
v___y_3944_ = v___y_3952_;
v___y_3945_ = v___y_3954_;
v___y_3946_ = v___y_3950_;
goto v___jp_3940_;
}
else
{
lean_object* v___x_3960_; 
lean_dec_ref(v___x_3767_);
lean_dec_ref(v_config_3615_);
lean_inc(v_mvarId_3616_);
v___x_3960_ = l_Lean_MVarId_getType(v_mvarId_3616_, v___y_3956_, v___y_3952_, v___y_3954_, v___y_3950_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref(v___x_3960_);
v___x_3962_ = l_Lean_LocalDecl_toExpr(v_val_3647_);
v___x_3963_ = l_Lean_Meta_mkEqOfHEq(v___x_3962_, v___x_3626_, v___y_3956_, v___y_3952_, v___y_3954_, v___y_3950_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref(v___x_3963_);
v___x_3965_ = l_Lean_Meta_mkNoConfusion(v_a_3961_, v_a_3964_, v___y_3956_, v___y_3952_, v___y_3954_, v___y_3950_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref(v___x_3965_);
v___x_3967_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3616_, v_a_3966_, v___y_3952_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec_ref(v___x_3967_);
v___x_3968_ = lean_box(v___x_3626_);
v___x_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
lean_ctor_set(v___x_3970_, 1, v___x_3651_);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
v_a_3633_ = v___x_3971_;
goto v___jp_3632_;
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
v_a_3972_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3967_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3967_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_3980_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3965_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3965_);
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
lean_dec(v_a_3961_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_3988_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3963_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3963_);
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
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_3996_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3960_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3960_);
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
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec_ref(v___x_3767_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4004_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3957_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3957_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
v___jp_4012_:
{
lean_object* v___x_4018_; 
lean_inc_ref(v___x_3767_);
v___x_4018_ = l_Lean_Meta_matchHEq_x3f(v___x_3767_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref(v___x_4018_);
if (lean_obj_tag(v_a_4019_) == 1)
{
lean_object* v_val_4020_; lean_object* v_snd_4021_; lean_object* v_snd_4022_; lean_object* v_fst_4023_; lean_object* v_fst_4024_; lean_object* v_fst_4025_; lean_object* v_snd_4026_; lean_object* v___x_4027_; 
v_val_4020_ = lean_ctor_get(v_a_4019_, 0);
lean_inc(v_val_4020_);
lean_dec_ref(v_a_4019_);
v_snd_4021_ = lean_ctor_get(v_val_4020_, 1);
lean_inc(v_snd_4021_);
v_snd_4022_ = lean_ctor_get(v_snd_4021_, 1);
lean_inc(v_snd_4022_);
v_fst_4023_ = lean_ctor_get(v_val_4020_, 0);
lean_inc(v_fst_4023_);
lean_dec(v_val_4020_);
v_fst_4024_ = lean_ctor_get(v_snd_4021_, 0);
lean_inc(v_fst_4024_);
lean_dec(v_snd_4021_);
v_fst_4025_ = lean_ctor_get(v_snd_4022_, 0);
lean_inc(v_fst_4025_);
v_snd_4026_ = lean_ctor_get(v_snd_4022_, 1);
lean_inc(v_snd_4026_);
lean_dec(v_snd_4022_);
v___x_4027_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4024_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref(v___x_4027_);
if (lean_obj_tag(v_a_4028_) == 1)
{
lean_object* v_val_4029_; lean_object* v___x_4030_; 
v_val_4029_ = lean_ctor_get(v_a_4028_, 0);
lean_inc(v_val_4029_);
lean_dec_ref(v_a_4028_);
v___x_4030_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4026_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref(v___x_4030_);
if (lean_obj_tag(v_a_4031_) == 1)
{
lean_object* v_toConstantVal_4032_; lean_object* v_val_4033_; lean_object* v_toConstantVal_4034_; lean_object* v_name_4035_; lean_object* v_name_4036_; uint8_t v___x_4037_; 
v_toConstantVal_4032_ = lean_ctor_get(v_val_4029_, 0);
lean_inc_ref(v_toConstantVal_4032_);
lean_dec(v_val_4029_);
v_val_4033_ = lean_ctor_get(v_a_4031_, 0);
lean_inc(v_val_4033_);
lean_dec_ref(v_a_4031_);
v_toConstantVal_4034_ = lean_ctor_get(v_val_4033_, 0);
lean_inc_ref(v_toConstantVal_4034_);
lean_dec(v_val_4033_);
v_name_4035_ = lean_ctor_get(v_toConstantVal_4032_, 0);
lean_inc(v_name_4035_);
lean_dec_ref(v_toConstantVal_4032_);
v_name_4036_ = lean_ctor_get(v_toConstantVal_4034_, 0);
lean_inc(v_name_4036_);
lean_dec_ref(v_toConstantVal_4034_);
v___x_4037_ = lean_name_eq(v_name_4035_, v_name_4036_);
lean_dec(v_name_4036_);
lean_dec(v_name_4035_);
if (v___x_4037_ == 0)
{
v___y_3950_ = v___y_4017_;
v___y_3951_ = v_isEq_4013_;
v___y_3952_ = v___y_4015_;
v___y_3953_ = v_fst_4023_;
v___y_3954_ = v___y_4016_;
v___y_3955_ = v_fst_4025_;
v___y_3956_ = v___y_4014_;
goto v___jp_3949_;
}
else
{
if (v___x_3722_ == 0)
{
lean_dec(v_fst_4025_);
lean_dec(v_fst_4023_);
v___y_3941_ = v_isEq_4013_;
v_isHEq_3942_ = v___x_3626_;
v___y_3943_ = v___y_4014_;
v___y_3944_ = v___y_4015_;
v___y_3945_ = v___y_4016_;
v___y_3946_ = v___y_4017_;
goto v___jp_3940_;
}
else
{
v___y_3950_ = v___y_4017_;
v___y_3951_ = v_isEq_4013_;
v___y_3952_ = v___y_4015_;
v___y_3953_ = v_fst_4023_;
v___y_3954_ = v___y_4016_;
v___y_3955_ = v_fst_4025_;
v___y_3956_ = v___y_4014_;
goto v___jp_3949_;
}
}
}
else
{
lean_dec(v_a_4031_);
lean_dec(v_val_4029_);
lean_dec(v_fst_4025_);
lean_dec(v_fst_4023_);
v___y_3941_ = v_isEq_4013_;
v_isHEq_3942_ = v___x_3626_;
v___y_3943_ = v___y_4014_;
v___y_3944_ = v___y_4015_;
v___y_3945_ = v___y_4016_;
v___y_3946_ = v___y_4017_;
goto v___jp_3940_;
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v_val_4029_);
lean_dec(v_fst_4025_);
lean_dec(v_fst_4023_);
lean_dec_ref(v___x_3767_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4038_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4030_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4030_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
else
{
lean_dec(v_a_4028_);
lean_dec(v_snd_4026_);
lean_dec(v_fst_4025_);
lean_dec(v_fst_4023_);
v___y_3941_ = v_isEq_4013_;
v_isHEq_3942_ = v___x_3626_;
v___y_3943_ = v___y_4014_;
v___y_3944_ = v___y_4015_;
v___y_3945_ = v___y_4016_;
v___y_3946_ = v___y_4017_;
goto v___jp_3940_;
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec(v_snd_4026_);
lean_dec(v_fst_4025_);
lean_dec(v_fst_4023_);
lean_dec_ref(v___x_3767_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4046_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4027_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4027_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
else
{
lean_dec(v_a_4019_);
v___y_3941_ = v_isEq_4013_;
v_isHEq_3942_ = v___x_3722_;
v___y_3943_ = v___y_4014_;
v___y_3944_ = v___y_4015_;
v___y_3945_ = v___y_4016_;
v___y_3946_ = v___y_4017_;
goto v___jp_3940_;
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec_ref(v___x_3767_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4054_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4018_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4018_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
v___jp_4062_:
{
lean_object* v___x_4067_; 
lean_inc_ref(v___x_3767_);
v___x_4067_ = l_Lean_Meta_matchEq_x3f(v___x_3767_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref(v___x_4067_);
if (lean_obj_tag(v_a_4068_) == 1)
{
lean_object* v_val_4069_; lean_object* v_snd_4070_; lean_object* v_fst_4071_; lean_object* v_snd_4072_; lean_object* v___x_4073_; 
v_val_4069_ = lean_ctor_get(v_a_4068_, 0);
lean_inc(v_val_4069_);
lean_dec_ref(v_a_4068_);
v_snd_4070_ = lean_ctor_get(v_val_4069_, 1);
lean_inc(v_snd_4070_);
lean_dec(v_val_4069_);
v_fst_4071_ = lean_ctor_get(v_snd_4070_, 0);
lean_inc(v_fst_4071_);
v_snd_4072_ = lean_ctor_get(v_snd_4070_, 1);
lean_inc(v_snd_4072_);
lean_dec(v_snd_4070_);
v___x_4073_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4071_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref(v___x_4073_);
if (lean_obj_tag(v_a_4074_) == 1)
{
lean_object* v_val_4075_; lean_object* v___x_4076_; 
v_val_4075_ = lean_ctor_get(v_a_4074_, 0);
lean_inc(v_val_4075_);
lean_dec_ref(v_a_4074_);
v___x_4076_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4072_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref(v___x_4076_);
if (lean_obj_tag(v_a_4077_) == 1)
{
lean_object* v_toConstantVal_4078_; lean_object* v_val_4079_; lean_object* v_toConstantVal_4080_; lean_object* v_name_4081_; lean_object* v_name_4082_; uint8_t v___x_4083_; 
v_toConstantVal_4078_ = lean_ctor_get(v_val_4075_, 0);
lean_inc_ref(v_toConstantVal_4078_);
lean_dec(v_val_4075_);
v_val_4079_ = lean_ctor_get(v_a_4077_, 0);
lean_inc(v_val_4079_);
lean_dec_ref(v_a_4077_);
v_toConstantVal_4080_ = lean_ctor_get(v_val_4079_, 0);
lean_inc_ref(v_toConstantVal_4080_);
lean_dec(v_val_4079_);
v_name_4081_ = lean_ctor_get(v_toConstantVal_4078_, 0);
lean_inc(v_name_4081_);
lean_dec_ref(v_toConstantVal_4078_);
v_name_4082_ = lean_ctor_get(v_toConstantVal_4080_, 0);
lean_inc(v_name_4082_);
lean_dec_ref(v_toConstantVal_4080_);
v___x_4083_ = lean_name_eq(v_name_4081_, v_name_4082_);
lean_dec(v_name_4082_);
lean_dec(v_name_4081_);
if (v___x_4083_ == 0)
{
lean_dec_ref(v___x_3767_);
lean_dec_ref(v_config_3615_);
v___y_3653_ = v___y_4065_;
v___y_3654_ = v___y_4063_;
v___y_3655_ = v___y_4066_;
v___y_3656_ = v___y_4064_;
goto v___jp_3652_;
}
else
{
if (v___x_3722_ == 0)
{
lean_del_object(v___x_3649_);
v_isEq_4013_ = v___x_3626_;
v___y_4014_ = v___y_4063_;
v___y_4015_ = v___y_4064_;
v___y_4016_ = v___y_4065_;
v___y_4017_ = v___y_4066_;
goto v___jp_4012_;
}
else
{
lean_dec_ref(v___x_3767_);
lean_dec_ref(v_config_3615_);
v___y_3653_ = v___y_4065_;
v___y_3654_ = v___y_4063_;
v___y_3655_ = v___y_4066_;
v___y_3656_ = v___y_4064_;
goto v___jp_3652_;
}
}
}
else
{
lean_dec(v_a_4077_);
lean_dec(v_val_4075_);
lean_del_object(v___x_3649_);
v_isEq_4013_ = v___x_3626_;
v___y_4014_ = v___y_4063_;
v___y_4015_ = v___y_4064_;
v___y_4016_ = v___y_4065_;
v___y_4017_ = v___y_4066_;
goto v___jp_4012_;
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v_val_4075_);
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4084_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4076_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4076_);
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
else
{
lean_dec(v_a_4074_);
lean_dec(v_snd_4072_);
lean_del_object(v___x_3649_);
v_isEq_4013_ = v___x_3626_;
v___y_4014_ = v___y_4063_;
v___y_4015_ = v___y_4064_;
v___y_4016_ = v___y_4065_;
v___y_4017_ = v___y_4066_;
goto v___jp_4012_;
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec(v_snd_4072_);
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4092_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4073_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4073_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_dec(v_a_4068_);
lean_del_object(v___x_3649_);
v_isEq_4013_ = v___x_3722_;
v___y_4014_ = v___y_4063_;
v___y_4015_ = v___y_4064_;
v___y_4016_ = v___y_4065_;
v___y_4017_ = v___y_4066_;
goto v___jp_4012_;
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4100_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4067_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4067_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
v___jp_4108_:
{
lean_object* v___x_4113_; 
lean_inc_ref(v___x_3767_);
v___x_4113_ = l_refutableHasNotBit_x3f(v___x_3767_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref(v___x_4113_);
if (lean_obj_tag(v_a_4114_) == 1)
{
lean_object* v_val_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec_ref(v_config_3615_);
v_val_4115_ = lean_ctor_get(v_a_4114_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_a_4114_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4117_ = v_a_4114_;
v_isShared_4118_ = v_isSharedCheck_4155_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_val_4115_);
lean_dec(v_a_4114_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4155_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4119_; 
lean_inc(v_mvarId_3616_);
v___x_4119_ = l_Lean_MVarId_getType(v_mvarId_3616_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref(v___x_4119_);
v___x_4121_ = l_Lean_LocalDecl_toExpr(v_val_3647_);
v___x_4122_ = l_Lean_Meta_mkAbsurd(v_a_4120_, v_val_4115_, v___x_4121_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4124_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref(v___x_4122_);
v___x_4124_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3616_, v_a_4123_, v___y_4110_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v___x_4125_; lean_object* v___x_4127_; 
lean_dec_ref(v___x_4124_);
v___x_4125_ = lean_box(v___x_3626_);
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 0, v___x_4125_);
v___x_4127_ = v___x_4117_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4125_);
v___x_4127_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
lean_ctor_set(v___x_4128_, 1, v___x_3651_);
v___x_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
v_a_3633_ = v___x_4129_;
goto v___jp_3632_;
}
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_del_object(v___x_4117_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
v_a_4131_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4124_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4124_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_del_object(v___x_4117_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_4139_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4122_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4122_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_del_object(v___x_4117_);
lean_dec(v_val_4115_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_4147_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4119_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4119_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
else
{
lean_object* v___x_4156_; 
lean_dec(v_a_4114_);
lean_inc_ref(v___x_3767_);
v___x_4156_ = l_Lean_Meta_matchNe_x3f(v___x_3767_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref(v___x_4156_);
if (lean_obj_tag(v_a_4157_) == 1)
{
lean_object* v_val_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4228_; 
v_val_4158_ = lean_ctor_get(v_a_4157_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_a_4157_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4160_ = v_a_4157_;
v_isShared_4161_ = v_isSharedCheck_4228_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_val_4158_);
lean_dec(v_a_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4228_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v_snd_4162_; lean_object* v_fst_4163_; lean_object* v_snd_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4227_; 
v_snd_4162_ = lean_ctor_get(v_val_4158_, 1);
lean_inc(v_snd_4162_);
lean_dec(v_val_4158_);
v_fst_4163_ = lean_ctor_get(v_snd_4162_, 0);
v_snd_4164_ = lean_ctor_get(v_snd_4162_, 1);
v_isSharedCheck_4227_ = !lean_is_exclusive(v_snd_4162_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4166_ = v_snd_4162_;
v_isShared_4167_ = v_isSharedCheck_4227_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_snd_4164_);
lean_inc(v_fst_4163_);
lean_dec(v_snd_4162_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4227_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4168_; 
lean_inc(v_fst_4163_);
v___x_4168_ = l_Lean_Meta_isExprDefEq(v_fst_4163_, v_snd_4164_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; uint8_t v___x_4170_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref(v___x_4168_);
v___x_4170_ = lean_unbox(v_a_4169_);
lean_dec(v_a_4169_);
if (v___x_4170_ == 0)
{
lean_del_object(v___x_4166_);
lean_dec(v_fst_4163_);
lean_del_object(v___x_4160_);
v___y_4063_ = v___y_4109_;
v___y_4064_ = v___y_4110_;
v___y_4065_ = v___y_4111_;
v___y_4066_ = v___y_4112_;
goto v___jp_4062_;
}
else
{
lean_object* v___x_4171_; 
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec_ref(v_config_3615_);
lean_inc(v_mvarId_3616_);
v___x_4171_ = l_Lean_MVarId_getType(v_mvarId_3616_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___x_4173_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref(v___x_4171_);
v___x_4173_ = l_Lean_Meta_mkEqRefl(v_fst_4163_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref(v___x_4173_);
v___x_4175_ = l_Lean_LocalDecl_toExpr(v_val_3647_);
v___x_4176_ = l_Lean_Meta_mkAbsurd(v_a_4172_, v_a_4174_, v___x_4175_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4178_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref(v___x_4176_);
v___x_4178_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3616_, v_a_4177_, v___y_4110_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4181_; 
lean_dec_ref(v___x_4178_);
v___x_4179_ = lean_box(v___x_3626_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v___x_4179_);
v___x_4181_ = v___x_4160_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
lean_object* v___x_4183_; 
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 1, v___x_3651_);
lean_ctor_set(v___x_4166_, 0, v___x_4181_);
v___x_4183_ = v___x_4166_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4185_, 1, v___x_3651_);
v___x_4183_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; 
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
v_a_3633_ = v___x_4184_;
goto v___jp_3632_;
}
}
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_del_object(v___x_4166_);
lean_del_object(v___x_4160_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
v_a_4187_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4178_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4178_);
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
lean_del_object(v___x_4166_);
lean_del_object(v___x_4160_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_4195_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4176_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4176_);
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
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec(v_a_4172_);
lean_del_object(v___x_4166_);
lean_del_object(v___x_4160_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_4203_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4173_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4173_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_del_object(v___x_4166_);
lean_dec(v_fst_4163_);
lean_del_object(v___x_4160_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_4211_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4171_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4171_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_del_object(v___x_4166_);
lean_dec(v_fst_4163_);
lean_del_object(v___x_4160_);
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4219_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4168_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4168_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4157_);
v___y_4063_ = v___y_4109_;
v___y_4064_ = v___y_4110_;
v___y_4065_ = v___y_4111_;
v___y_4066_ = v___y_4112_;
goto v___jp_4062_;
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4229_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4156_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4156_);
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
lean_dec_ref(v___x_3767_);
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_4237_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4113_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4113_);
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
}
else
{
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
v_a_3641_ = v___x_3693_;
goto v___jp_3640_;
}
v___jp_3652_:
{
lean_object* v___x_3657_; 
lean_inc(v_mvarId_3616_);
v___x_3657_ = l_Lean_MVarId_getType(v_mvarId_3616_, v___y_3654_, v___y_3656_, v___y_3653_, v___y_3655_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref(v___x_3657_);
v___x_3659_ = l_Lean_LocalDecl_toExpr(v_val_3647_);
v___x_3660_ = l_Lean_Meta_mkNoConfusion(v_a_3658_, v___x_3659_, v___y_3654_, v___y_3656_, v___y_3653_, v___y_3655_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3662_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v___x_3660_);
v___x_3662_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3616_, v_a_3661_, v___y_3656_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3665_; 
lean_dec_ref(v___x_3662_);
v___x_3663_ = lean_box(v___x_3626_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v___x_3663_);
v___x_3665_ = v___x_3649_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
lean_ctor_set(v___x_3666_, 1, v___x_3651_);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
v_a_3633_ = v___x_3667_;
goto v___jp_3632_;
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_del_object(v___x_3649_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
v_a_3669_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3662_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3662_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_del_object(v___x_3649_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_3677_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3660_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3660_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_del_object(v___x_3649_);
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_3685_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3657_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3657_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
v___jp_3694_:
{
lean_object* v_searchFuel_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_searchFuel_3699_ = lean_ctor_get(v_config_3615_, 0);
v___x_3700_ = l_Lean_LocalDecl_fvarId(v_val_3647_);
lean_dec(v_val_3647_);
lean_inc(v_searchFuel_3699_);
lean_inc(v_mvarId_3616_);
v___x_3701_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3616_, v___x_3700_, v_searchFuel_3699_, v___y_3697_, v___y_3695_, v___y_3698_, v___y_3696_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; uint8_t v___x_3703_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref(v___x_3701_);
v___x_3703_ = lean_unbox(v_a_3702_);
lean_dec(v_a_3702_);
if (v___x_3703_ == 0)
{
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
v_a_3641_ = v___x_3693_;
goto v___jp_3640_;
}
else
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v___x_3704_ = lean_box(v___x_3626_);
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
v___x_3706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
lean_ctor_set(v___x_3706_, 1, v___x_3651_);
v___x_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
v_a_3633_ = v___x_3707_;
goto v___jp_3632_;
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_3708_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3701_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3701_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
v___jp_3716_:
{
if (v___y_3721_ == 0)
{
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
v_a_3641_ = v___x_3693_;
goto v___jp_3640_;
}
else
{
v___y_3695_ = v___y_3717_;
v___y_3696_ = v___y_3718_;
v___y_3697_ = v___y_3719_;
v___y_3698_ = v___y_3720_;
goto v___jp_3694_;
}
}
v___jp_3723_:
{
if (v___y_3728_ == 0)
{
v___y_3695_ = v___y_3724_;
v___y_3696_ = v___y_3725_;
v___y_3697_ = v___y_3726_;
v___y_3698_ = v___y_3727_;
goto v___jp_3694_;
}
else
{
v___y_3717_ = v___y_3724_;
v___y_3718_ = v___y_3725_;
v___y_3719_ = v___y_3726_;
v___y_3720_ = v___y_3727_;
v___y_3721_ = v___x_3722_;
goto v___jp_3716_;
}
}
v___jp_3729_:
{
if (v___y_3735_ == 0)
{
v___y_3717_ = v___y_3730_;
v___y_3718_ = v___y_3731_;
v___y_3719_ = v___y_3732_;
v___y_3720_ = v___y_3734_;
v___y_3721_ = v___x_3722_;
goto v___jp_3716_;
}
else
{
v___y_3724_ = v___y_3730_;
v___y_3725_ = v___y_3731_;
v___y_3726_ = v___y_3732_;
v___y_3727_ = v___y_3734_;
v___y_3728_ = v___y_3733_;
goto v___jp_3723_;
}
}
v___jp_3736_:
{
uint8_t v_emptyType_3743_; 
v_emptyType_3743_ = lean_ctor_get_uint8(v_config_3615_, sizeof(void*)*1 + 1);
if (v_emptyType_3743_ == 0)
{
v___y_3730_ = v___y_3740_;
v___y_3731_ = v___y_3742_;
v___y_3732_ = v___y_3739_;
v___y_3733_ = v___y_3738_;
v___y_3734_ = v___y_3741_;
v___y_3735_ = v___x_3722_;
goto v___jp_3729_;
}
else
{
if (v___y_3737_ == 0)
{
v___y_3724_ = v___y_3740_;
v___y_3725_ = v___y_3742_;
v___y_3726_ = v___y_3739_;
v___y_3727_ = v___y_3741_;
v___y_3728_ = v___y_3738_;
goto v___jp_3723_;
}
else
{
v___y_3730_ = v___y_3740_;
v___y_3731_ = v___y_3742_;
v___y_3732_ = v___y_3739_;
v___y_3733_ = v___y_3738_;
v___y_3734_ = v___y_3741_;
v___y_3735_ = v___x_3722_;
goto v___jp_3729_;
}
}
}
v___jp_3744_:
{
if (v___y_3751_ == 0)
{
v___y_3737_ = v___y_3746_;
v___y_3738_ = v___y_3750_;
v___y_3739_ = v___y_3747_;
v___y_3740_ = v___y_3749_;
v___y_3741_ = v___y_3748_;
v___y_3742_ = v___y_3745_;
goto v___jp_3736_;
}
else
{
lean_object* v___x_3752_; 
lean_inc(v_val_3647_);
lean_inc(v_mvarId_3616_);
v___x_3752_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3616_, v_val_3647_, v___y_3747_, v___y_3749_, v___y_3748_, v___y_3745_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; uint8_t v___x_3754_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref(v___x_3752_);
v___x_3754_ = lean_unbox(v_a_3753_);
lean_dec(v_a_3753_);
if (v___x_3754_ == 0)
{
v___y_3737_ = v___y_3746_;
v___y_3738_ = v___y_3750_;
v___y_3739_ = v___y_3747_;
v___y_3740_ = v___y_3749_;
v___y_3741_ = v___y_3748_;
v___y_3742_ = v___y_3745_;
goto v___jp_3736_;
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
lean_dec(v_val_3647_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v___x_3755_ = lean_box(v___x_3626_);
v___x_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v___x_3651_);
v___x_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
v_a_3633_ = v___x_3758_;
goto v___jp_3632_;
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec(v_val_3647_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
lean_dec_ref(v_config_3615_);
v_a_3759_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3752_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3752_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
}
}
}
v___jp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3636_; 
v___x_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3634_, 0, v_a_3633_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3634_);
v___x_3636_ = v___x_3630_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_snd_3628_);
v___x_3636_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
return v___x_3637_;
}
}
v___jp_3640_:
{
lean_object* v___x_3642_; size_t v___x_3643_; size_t v___x_3644_; 
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3639_);
lean_ctor_set(v___x_3642_, 1, v_a_3641_);
v___x_3643_ = ((size_t)1ULL);
v___x_3644_ = lean_usize_add(v_i_3619_, v___x_3643_);
v_i_3619_ = v___x_3644_;
v_b_3620_ = v___x_3642_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_4318_, lean_object* v_mvarId_4319_, lean_object* v_as_4320_, lean_object* v_sz_4321_, lean_object* v_i_4322_, lean_object* v_b_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
size_t v_sz_boxed_4329_; size_t v_i_boxed_4330_; lean_object* v_res_4331_; 
v_sz_boxed_4329_ = lean_unbox_usize(v_sz_4321_);
lean_dec(v_sz_4321_);
v_i_boxed_4330_ = lean_unbox_usize(v_i_4322_);
lean_dec(v_i_4322_);
v_res_4331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_4318_, v_mvarId_4319_, v_as_4320_, v_sz_boxed_4329_, v_i_boxed_4330_, v_b_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec_ref(v_as_4320_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_4332_, lean_object* v_mvarId_4333_, lean_object* v_as_4334_, size_t v_sz_4335_, size_t v_i_4336_, lean_object* v_b_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
uint8_t v___x_4343_; 
v___x_4343_ = lean_usize_dec_lt(v_i_4336_, v_sz_4335_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; 
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v_b_4337_);
return v___x_4344_;
}
else
{
lean_object* v_snd_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_5033_; 
v_snd_4345_ = lean_ctor_get(v_b_4337_, 1);
v_isSharedCheck_5033_ = !lean_is_exclusive(v_b_4337_);
if (v_isSharedCheck_5033_ == 0)
{
lean_object* v_unused_5034_; 
v_unused_5034_ = lean_ctor_get(v_b_4337_, 0);
lean_dec(v_unused_5034_);
v___x_4347_ = v_b_4337_;
v_isShared_4348_ = v_isSharedCheck_5033_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_snd_4345_);
lean_dec(v_b_4337_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_5033_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v_a_4350_; lean_object* v___x_4356_; lean_object* v_a_4358_; lean_object* v_a_4363_; 
v___x_4356_ = lean_box(0);
v_a_4363_ = lean_array_uget(v_as_4334_, v_i_4336_);
if (lean_obj_tag(v_a_4363_) == 0)
{
lean_del_object(v___x_4347_);
v_a_4358_ = v_snd_4345_;
goto v___jp_4357_;
}
else
{
lean_object* v_val_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_5032_; 
v_val_4364_ = lean_ctor_get(v_a_4363_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v_a_4363_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_4366_ = v_a_4363_;
v_isShared_4367_ = v_isSharedCheck_5032_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_val_4364_);
lean_dec(v_a_4363_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_5032_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4368_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___x_4410_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; uint8_t v___y_4438_; uint8_t v___x_4439_; lean_object* v___y_4441_; uint8_t v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4447_; uint8_t v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; uint8_t v___y_4452_; uint8_t v___y_4454_; uint8_t v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; uint8_t v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; uint8_t v___y_4467_; uint8_t v___y_4468_; 
v___x_4368_ = lean_box(0);
v___x_4410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_4439_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4364_);
if (v___x_4439_ == 0)
{
lean_object* v___x_4484_; uint8_t v___y_4486_; uint8_t v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4495_; lean_object* v___y_4496_; uint8_t v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; uint8_t v___y_4501_; uint8_t v___y_4502_; lean_object* v___y_4505_; uint8_t v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; uint8_t v___y_4510_; lean_object* v_a_4511_; lean_object* v___y_4515_; uint8_t v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; uint8_t v___y_4520_; lean_object* v___y_4613_; uint8_t v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; uint8_t v___y_4618_; uint8_t v___y_4619_; lean_object* v___y_4621_; lean_object* v___y_4622_; uint8_t v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; uint8_t v___y_4627_; uint8_t v___y_4628_; lean_object* v___y_4631_; uint8_t v___y_4632_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v___y_4635_; uint8_t v___y_4636_; uint8_t v___y_4637_; lean_object* v___y_4650_; uint8_t v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; uint8_t v___y_4655_; uint8_t v___y_4656_; uint8_t v___y_4658_; uint8_t v_isHEq_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; uint8_t v___y_4673_; uint8_t v_isEq_4730_; lean_object* v___y_4731_; lean_object* v___y_4732_; lean_object* v___y_4733_; lean_object* v___y_4734_; lean_object* v___y_4780_; lean_object* v___y_4781_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4826_; lean_object* v___y_4827_; lean_object* v___y_4828_; lean_object* v___y_4829_; lean_object* v___x_4962_; 
v___x_4484_ = l_Lean_LocalDecl_type(v_val_4364_);
lean_inc_ref(v___x_4484_);
v___x_4962_ = l_Lean_Meta_matchNot_x3f(v___x_4484_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref(v___x_4962_);
if (lean_obj_tag(v_a_4963_) == 1)
{
lean_object* v_val_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_5023_; 
v_val_4964_ = lean_ctor_get(v_a_4963_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v_a_4963_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_4966_ = v_a_4963_;
v_isShared_4967_ = v_isSharedCheck_5023_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_val_4964_);
lean_dec(v_a_4963_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_5023_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4968_; 
v___x_4968_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4964_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4968_) == 0)
{
lean_object* v_a_4969_; 
v_a_4969_ = lean_ctor_get(v___x_4968_, 0);
lean_inc(v_a_4969_);
lean_dec_ref(v___x_4968_);
if (lean_obj_tag(v_a_4969_) == 1)
{
lean_object* v_val_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_5014_; 
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec_ref(v_config_4332_);
v_val_4970_ = lean_ctor_get(v_a_4969_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v_a_4969_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_4972_ = v_a_4969_;
v_isShared_4973_ = v_isSharedCheck_5014_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_val_4970_);
lean_dec(v_a_4969_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_5014_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; 
lean_inc(v_mvarId_4333_);
v___x_4974_ = l_Lean_MVarId_getType(v_mvarId_4333_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4975_);
lean_dec_ref(v___x_4974_);
v___x_4976_ = l_Lean_LocalDecl_toExpr(v_val_4364_);
v___x_4977_ = l_Lean_mkFVar(v_val_4970_);
v___x_4978_ = l_Lean_Expr_app___override(v___x_4976_, v___x_4977_);
v___x_4979_ = l_Lean_Meta_mkFalseElim(v_a_4975_, v___x_4978_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v___x_4981_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
lean_inc(v_a_4980_);
lean_dec_ref(v___x_4979_);
v___x_4981_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4333_, v_a_4980_, v___y_4339_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v___x_4982_; lean_object* v___x_4984_; 
lean_dec_ref(v___x_4981_);
v___x_4982_ = lean_box(v___x_4343_);
if (v_isShared_4973_ == 0)
{
lean_ctor_set(v___x_4972_, 0, v___x_4982_);
v___x_4984_ = v___x_4972_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4982_);
v___x_4984_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
lean_object* v___x_4985_; lean_object* v___x_4987_; 
v___x_4985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4984_);
lean_ctor_set(v___x_4985_, 1, v___x_4368_);
if (v_isShared_4967_ == 0)
{
lean_ctor_set_tag(v___x_4966_, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4985_);
v___x_4987_ = v___x_4966_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4985_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
v_a_4350_ = v___x_4987_;
goto v___jp_4349_;
}
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
lean_del_object(v___x_4972_);
lean_del_object(v___x_4966_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
v_a_4990_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4981_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4981_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_del_object(v___x_4972_);
lean_del_object(v___x_4966_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4998_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4979_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4979_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
else
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
lean_del_object(v___x_4972_);
lean_dec(v_val_4970_);
lean_del_object(v___x_4966_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_5006_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4974_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4974_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
}
else
{
lean_dec(v_a_4969_);
lean_del_object(v___x_4966_);
v___y_4826_ = v___y_4338_;
v___y_4827_ = v___y_4339_;
v___y_4828_ = v___y_4340_;
v___y_4829_ = v___y_4341_;
goto v___jp_4825_;
}
}
else
{
lean_object* v_a_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5022_; 
lean_del_object(v___x_4966_);
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_5015_ = lean_ctor_get(v___x_4968_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v___x_4968_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5017_ = v___x_4968_;
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_a_5015_);
lean_dec(v___x_4968_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5020_; 
if (v_isShared_5018_ == 0)
{
v___x_5020_ = v___x_5017_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5015_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
}
}
else
{
lean_dec(v_a_4963_);
v___y_4826_ = v___y_4338_;
v___y_4827_ = v___y_4339_;
v___y_4828_ = v___y_4340_;
v___y_4829_ = v___y_4341_;
goto v___jp_4825_;
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_5024_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_4962_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_4962_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
v___jp_4485_:
{
uint8_t v_genDiseq_4492_; 
v_genDiseq_4492_ = lean_ctor_get_uint8(v_config_4332_, sizeof(void*)*1 + 2);
if (v_genDiseq_4492_ == 0)
{
lean_dec_ref(v___x_4484_);
v___y_4462_ = v___y_4486_;
v___y_4463_ = v___y_4488_;
v___y_4464_ = v___y_4489_;
v___y_4465_ = v___y_4490_;
v___y_4466_ = v___y_4491_;
v___y_4467_ = v___y_4487_;
v___y_4468_ = v___x_4439_;
goto v___jp_4461_;
}
else
{
uint8_t v___x_4493_; 
v___x_4493_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4484_);
v___y_4462_ = v___y_4486_;
v___y_4463_ = v___y_4488_;
v___y_4464_ = v___y_4489_;
v___y_4465_ = v___y_4490_;
v___y_4466_ = v___y_4491_;
v___y_4467_ = v___y_4487_;
v___y_4468_ = v___x_4493_;
goto v___jp_4461_;
}
}
v___jp_4494_:
{
if (v___y_4502_ == 0)
{
lean_dec_ref(v___y_4495_);
v___y_4486_ = v___y_4497_;
v___y_4487_ = v___y_4501_;
v___y_4488_ = v___y_4499_;
v___y_4489_ = v___y_4500_;
v___y_4490_ = v___y_4496_;
v___y_4491_ = v___y_4498_;
goto v___jp_4485_;
}
else
{
lean_object* v___x_4503_; 
lean_dec_ref(v___x_4484_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v___x_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___y_4495_);
return v___x_4503_;
}
}
v___jp_4504_:
{
uint8_t v___x_4512_; 
v___x_4512_ = l_Lean_Exception_isInterrupt(v_a_4511_);
if (v___x_4512_ == 0)
{
uint8_t v___x_4513_; 
lean_inc_ref(v_a_4511_);
v___x_4513_ = l_Lean_Exception_isRuntime(v_a_4511_);
v___y_4495_ = v_a_4511_;
v___y_4496_ = v___y_4505_;
v___y_4497_ = v___y_4506_;
v___y_4498_ = v___y_4508_;
v___y_4499_ = v___y_4507_;
v___y_4500_ = v___y_4509_;
v___y_4501_ = v___y_4510_;
v___y_4502_ = v___x_4513_;
goto v___jp_4494_;
}
else
{
v___y_4495_ = v_a_4511_;
v___y_4496_ = v___y_4505_;
v___y_4497_ = v___y_4506_;
v___y_4498_ = v___y_4508_;
v___y_4499_ = v___y_4507_;
v___y_4500_ = v___y_4509_;
v___y_4501_ = v___y_4510_;
v___y_4502_ = v___x_4512_;
goto v___jp_4494_;
}
}
v___jp_4514_:
{
lean_object* v___x_4521_; 
lean_inc_ref(v___x_4484_);
v___x_4521_ = l_Lean_Meta_mkDecide(v___x_4484_, v___y_4518_, v___y_4519_, v___y_4515_, v___y_4517_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4523_; uint8_t v_foApprox_4524_; uint8_t v_ctxApprox_4525_; uint8_t v_quasiPatternApprox_4526_; uint8_t v_constApprox_4527_; uint8_t v_isDefEqStuckEx_4528_; uint8_t v_unificationHints_4529_; uint8_t v_proofIrrelevance_4530_; uint8_t v_assignSyntheticOpaque_4531_; uint8_t v_offsetCnstrs_4532_; uint8_t v_etaStruct_4533_; uint8_t v_univApprox_4534_; uint8_t v_iota_4535_; uint8_t v_beta_4536_; uint8_t v_proj_4537_; uint8_t v_zeta_4538_; uint8_t v_zetaDelta_4539_; uint8_t v_zetaUnused_4540_; uint8_t v_zetaHave_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4610_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref(v___x_4521_);
v___x_4523_ = l_Lean_Meta_Context_config(v___y_4518_);
v_foApprox_4524_ = lean_ctor_get_uint8(v___x_4523_, 0);
v_ctxApprox_4525_ = lean_ctor_get_uint8(v___x_4523_, 1);
v_quasiPatternApprox_4526_ = lean_ctor_get_uint8(v___x_4523_, 2);
v_constApprox_4527_ = lean_ctor_get_uint8(v___x_4523_, 3);
v_isDefEqStuckEx_4528_ = lean_ctor_get_uint8(v___x_4523_, 4);
v_unificationHints_4529_ = lean_ctor_get_uint8(v___x_4523_, 5);
v_proofIrrelevance_4530_ = lean_ctor_get_uint8(v___x_4523_, 6);
v_assignSyntheticOpaque_4531_ = lean_ctor_get_uint8(v___x_4523_, 7);
v_offsetCnstrs_4532_ = lean_ctor_get_uint8(v___x_4523_, 8);
v_etaStruct_4533_ = lean_ctor_get_uint8(v___x_4523_, 10);
v_univApprox_4534_ = lean_ctor_get_uint8(v___x_4523_, 11);
v_iota_4535_ = lean_ctor_get_uint8(v___x_4523_, 12);
v_beta_4536_ = lean_ctor_get_uint8(v___x_4523_, 13);
v_proj_4537_ = lean_ctor_get_uint8(v___x_4523_, 14);
v_zeta_4538_ = lean_ctor_get_uint8(v___x_4523_, 15);
v_zetaDelta_4539_ = lean_ctor_get_uint8(v___x_4523_, 16);
v_zetaUnused_4540_ = lean_ctor_get_uint8(v___x_4523_, 17);
v_zetaHave_4541_ = lean_ctor_get_uint8(v___x_4523_, 18);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4543_ = v___x_4523_;
v_isShared_4544_ = v_isSharedCheck_4610_;
goto v_resetjp_4542_;
}
else
{
lean_dec(v___x_4523_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4610_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
uint8_t v_trackZetaDelta_4545_; lean_object* v_zetaDeltaSet_4546_; lean_object* v_lctx_4547_; lean_object* v_localInstances_4548_; lean_object* v_defEqCtx_x3f_4549_; lean_object* v_synthPendingDepth_4550_; lean_object* v_canUnfold_x3f_4551_; uint8_t v_univApprox_4552_; uint8_t v_inTypeClassResolution_4553_; uint8_t v_cacheInferType_4554_; uint8_t v___x_4555_; lean_object* v_config_4557_; 
v_trackZetaDelta_4545_ = lean_ctor_get_uint8(v___y_4518_, sizeof(void*)*7);
v_zetaDeltaSet_4546_ = lean_ctor_get(v___y_4518_, 1);
v_lctx_4547_ = lean_ctor_get(v___y_4518_, 2);
v_localInstances_4548_ = lean_ctor_get(v___y_4518_, 3);
v_defEqCtx_x3f_4549_ = lean_ctor_get(v___y_4518_, 4);
v_synthPendingDepth_4550_ = lean_ctor_get(v___y_4518_, 5);
v_canUnfold_x3f_4551_ = lean_ctor_get(v___y_4518_, 6);
v_univApprox_4552_ = lean_ctor_get_uint8(v___y_4518_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4553_ = lean_ctor_get_uint8(v___y_4518_, sizeof(void*)*7 + 2);
v_cacheInferType_4554_ = lean_ctor_get_uint8(v___y_4518_, sizeof(void*)*7 + 3);
v___x_4555_ = 1;
if (v_isShared_4544_ == 0)
{
v_config_4557_ = v___x_4543_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 0, v_foApprox_4524_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 1, v_ctxApprox_4525_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 2, v_quasiPatternApprox_4526_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 3, v_constApprox_4527_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 4, v_isDefEqStuckEx_4528_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 5, v_unificationHints_4529_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 6, v_proofIrrelevance_4530_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 7, v_assignSyntheticOpaque_4531_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 8, v_offsetCnstrs_4532_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 10, v_etaStruct_4533_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 11, v_univApprox_4534_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 12, v_iota_4535_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 13, v_beta_4536_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 14, v_proj_4537_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 15, v_zeta_4538_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 16, v_zetaDelta_4539_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 17, v_zetaUnused_4540_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, 18, v_zetaHave_4541_);
v_config_4557_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
uint64_t v___x_4558_; uint64_t v___x_4559_; uint64_t v___x_4560_; uint64_t v___x_4561_; uint64_t v___x_4562_; uint64_t v_key_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
lean_ctor_set_uint8(v_config_4557_, 9, v___x_4555_);
v___x_4558_ = l_Lean_Meta_Context_configKey(v___y_4518_);
v___x_4559_ = 2ULL;
v___x_4560_ = lean_uint64_shift_right(v___x_4558_, v___x_4559_);
v___x_4561_ = lean_uint64_shift_left(v___x_4560_, v___x_4559_);
v___x_4562_ = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
v_key_4563_ = lean_uint64_lor(v___x_4561_, v___x_4562_);
v___x_4564_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4564_, 0, v_config_4557_);
lean_ctor_set_uint64(v___x_4564_, sizeof(void*)*1, v_key_4563_);
lean_inc(v_canUnfold_x3f_4551_);
lean_inc(v_synthPendingDepth_4550_);
lean_inc(v_defEqCtx_x3f_4549_);
lean_inc_ref(v_localInstances_4548_);
lean_inc_ref(v_lctx_4547_);
lean_inc(v_zetaDeltaSet_4546_);
v___x_4565_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
lean_ctor_set(v___x_4565_, 1, v_zetaDeltaSet_4546_);
lean_ctor_set(v___x_4565_, 2, v_lctx_4547_);
lean_ctor_set(v___x_4565_, 3, v_localInstances_4548_);
lean_ctor_set(v___x_4565_, 4, v_defEqCtx_x3f_4549_);
lean_ctor_set(v___x_4565_, 5, v_synthPendingDepth_4550_);
lean_ctor_set(v___x_4565_, 6, v_canUnfold_x3f_4551_);
lean_ctor_set_uint8(v___x_4565_, sizeof(void*)*7, v_trackZetaDelta_4545_);
lean_ctor_set_uint8(v___x_4565_, sizeof(void*)*7 + 1, v_univApprox_4552_);
lean_ctor_set_uint8(v___x_4565_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4553_);
lean_ctor_set_uint8(v___x_4565_, sizeof(void*)*7 + 3, v_cacheInferType_4554_);
lean_inc(v___y_4517_);
lean_inc_ref(v___y_4515_);
lean_inc(v___y_4519_);
lean_inc(v_a_4522_);
v___x_4566_ = lean_whnf(v_a_4522_, v___x_4565_, v___y_4519_, v___y_4515_, v___y_4517_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4567_);
lean_dec_ref(v___x_4566_);
v___x_4568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
v___x_4569_ = l_Lean_Expr_isConstOf(v_a_4567_, v___x_4568_);
lean_dec(v_a_4567_);
if (v___x_4569_ == 0)
{
lean_dec(v_a_4522_);
v___y_4486_ = v___y_4516_;
v___y_4487_ = v___y_4520_;
v___y_4488_ = v___y_4518_;
v___y_4489_ = v___y_4519_;
v___y_4490_ = v___y_4515_;
v___y_4491_ = v___y_4517_;
goto v___jp_4485_;
}
else
{
lean_object* v___x_4570_; 
lean_inc(v_a_4522_);
v___x_4570_ = l_Lean_Meta_mkEqRefl(v_a_4522_, v___y_4518_, v___y_4519_, v___y_4515_, v___y_4517_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4572_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4571_);
lean_dec_ref(v___x_4570_);
lean_inc(v_mvarId_4333_);
v___x_4572_ = l_Lean_MVarId_getType(v_mvarId_4333_, v___y_4518_, v___y_4519_, v___y_4515_, v___y_4517_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; lean_object* v_nargs_4574_; lean_object* v___x_4575_; lean_object* v_dummy_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4573_);
lean_dec_ref(v___x_4572_);
v_nargs_4574_ = l_Lean_Expr_getAppNumArgs(v_a_4522_);
v___x_4575_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_dummy_4576_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(v_nargs_4574_);
v___x_4577_ = lean_mk_array(v_nargs_4574_, v_dummy_4576_);
v___x_4578_ = lean_unsigned_to_nat(1u);
v___x_4579_ = lean_nat_sub(v_nargs_4574_, v___x_4578_);
lean_dec(v_nargs_4574_);
v___x_4580_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4522_, v___x_4577_, v___x_4579_);
v___x_4581_ = lean_array_push(v___x_4580_, v_a_4571_);
v___x_4582_ = l_Lean_mkAppN(v___x_4575_, v___x_4581_);
lean_dec_ref(v___x_4581_);
lean_inc(v_val_4364_);
v___x_4583_ = l_Lean_LocalDecl_toExpr(v_val_4364_);
v___x_4584_ = l_Lean_Meta_mkAbsurd(v_a_4573_, v___x_4583_, v___x_4582_, v___y_4518_, v___y_4519_, v___y_4515_, v___y_4517_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4604_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4587_ = v___x_4584_;
v_isShared_4588_ = v_isSharedCheck_4604_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4584_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4604_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4589_; 
lean_inc(v_mvarId_4333_);
v___x_4589_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4333_, v_a_4585_, v___y_4519_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4601_; 
lean_dec_ref(v___x_4484_);
lean_dec(v_val_4364_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4601_ == 0)
{
lean_object* v_unused_4602_; 
v_unused_4602_ = lean_ctor_get(v___x_4589_, 0);
lean_dec(v_unused_4602_);
v___x_4591_ = v___x_4589_;
v_isShared_4592_ = v_isSharedCheck_4601_;
goto v_resetjp_4590_;
}
else
{
lean_dec(v___x_4589_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4601_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4593_; lean_object* v___x_4595_; 
v___x_4593_ = lean_box(v___x_4343_);
if (v_isShared_4592_ == 0)
{
lean_ctor_set_tag(v___x_4591_, 1);
lean_ctor_set(v___x_4591_, 0, v___x_4593_);
v___x_4595_ = v___x_4591_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4593_);
v___x_4595_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
lean_object* v___x_4596_; lean_object* v___x_4598_; 
v___x_4596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
lean_ctor_set(v___x_4596_, 1, v___x_4368_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 0, v___x_4596_);
v___x_4598_ = v___x_4587_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
v_a_4350_ = v___x_4598_;
goto v___jp_4349_;
}
}
}
}
else
{
lean_object* v_a_4603_; 
lean_del_object(v___x_4587_);
v_a_4603_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_a_4603_);
lean_dec_ref(v___x_4589_);
v___y_4505_ = v___y_4515_;
v___y_4506_ = v___y_4516_;
v___y_4507_ = v___y_4518_;
v___y_4508_ = v___y_4517_;
v___y_4509_ = v___y_4519_;
v___y_4510_ = v___y_4520_;
v_a_4511_ = v_a_4603_;
goto v___jp_4504_;
}
}
}
else
{
lean_object* v_a_4605_; 
v_a_4605_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4605_);
lean_dec_ref(v___x_4584_);
v___y_4505_ = v___y_4515_;
v___y_4506_ = v___y_4516_;
v___y_4507_ = v___y_4518_;
v___y_4508_ = v___y_4517_;
v___y_4509_ = v___y_4519_;
v___y_4510_ = v___y_4520_;
v_a_4511_ = v_a_4605_;
goto v___jp_4504_;
}
}
else
{
lean_object* v_a_4606_; 
lean_dec(v_a_4571_);
lean_dec(v_a_4522_);
v_a_4606_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4606_);
lean_dec_ref(v___x_4572_);
v___y_4505_ = v___y_4515_;
v___y_4506_ = v___y_4516_;
v___y_4507_ = v___y_4518_;
v___y_4508_ = v___y_4517_;
v___y_4509_ = v___y_4519_;
v___y_4510_ = v___y_4520_;
v_a_4511_ = v_a_4606_;
goto v___jp_4504_;
}
}
else
{
lean_object* v_a_4607_; 
lean_dec(v_a_4522_);
v_a_4607_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4607_);
lean_dec_ref(v___x_4570_);
v___y_4505_ = v___y_4515_;
v___y_4506_ = v___y_4516_;
v___y_4507_ = v___y_4518_;
v___y_4508_ = v___y_4517_;
v___y_4509_ = v___y_4519_;
v___y_4510_ = v___y_4520_;
v_a_4511_ = v_a_4607_;
goto v___jp_4504_;
}
}
}
else
{
lean_object* v_a_4608_; 
lean_dec(v_a_4522_);
v_a_4608_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4608_);
lean_dec_ref(v___x_4566_);
v___y_4505_ = v___y_4515_;
v___y_4506_ = v___y_4516_;
v___y_4507_ = v___y_4518_;
v___y_4508_ = v___y_4517_;
v___y_4509_ = v___y_4519_;
v___y_4510_ = v___y_4520_;
v_a_4511_ = v_a_4608_;
goto v___jp_4504_;
}
}
}
}
else
{
lean_object* v_a_4611_; 
v_a_4611_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4611_);
lean_dec_ref(v___x_4521_);
v___y_4505_ = v___y_4515_;
v___y_4506_ = v___y_4516_;
v___y_4507_ = v___y_4518_;
v___y_4508_ = v___y_4517_;
v___y_4509_ = v___y_4519_;
v___y_4510_ = v___y_4520_;
v_a_4511_ = v_a_4611_;
goto v___jp_4504_;
}
}
v___jp_4612_:
{
if (v___y_4619_ == 0)
{
v___y_4486_ = v___y_4614_;
v___y_4487_ = v___y_4618_;
v___y_4488_ = v___y_4616_;
v___y_4489_ = v___y_4617_;
v___y_4490_ = v___y_4613_;
v___y_4491_ = v___y_4615_;
goto v___jp_4485_;
}
else
{
v___y_4515_ = v___y_4613_;
v___y_4516_ = v___y_4614_;
v___y_4517_ = v___y_4615_;
v___y_4518_ = v___y_4616_;
v___y_4519_ = v___y_4617_;
v___y_4520_ = v___y_4618_;
goto v___jp_4514_;
}
}
v___jp_4620_:
{
if (v___y_4628_ == 0)
{
lean_dec_ref(v___y_4621_);
v___y_4613_ = v___y_4622_;
v___y_4614_ = v___y_4623_;
v___y_4615_ = v___y_4625_;
v___y_4616_ = v___y_4624_;
v___y_4617_ = v___y_4626_;
v___y_4618_ = v___y_4627_;
v___y_4619_ = v___x_4439_;
goto v___jp_4612_;
}
else
{
uint8_t v___x_4629_; 
v___x_4629_ = l_Lean_Expr_hasFVar(v___y_4621_);
lean_dec_ref(v___y_4621_);
if (v___x_4629_ == 0)
{
v___y_4515_ = v___y_4622_;
v___y_4516_ = v___y_4623_;
v___y_4517_ = v___y_4625_;
v___y_4518_ = v___y_4624_;
v___y_4519_ = v___y_4626_;
v___y_4520_ = v___y_4627_;
goto v___jp_4514_;
}
else
{
v___y_4613_ = v___y_4622_;
v___y_4614_ = v___y_4623_;
v___y_4615_ = v___y_4625_;
v___y_4616_ = v___y_4624_;
v___y_4617_ = v___y_4626_;
v___y_4618_ = v___y_4627_;
v___y_4619_ = v___x_4439_;
goto v___jp_4612_;
}
}
}
v___jp_4630_:
{
lean_object* v___x_4638_; 
lean_inc_ref(v___x_4484_);
v___x_4638_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4484_, v___y_4635_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v_a_4639_; uint8_t v___x_4640_; 
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
lean_inc(v_a_4639_);
lean_dec_ref(v___x_4638_);
v___x_4640_ = l_Lean_Expr_hasMVar(v_a_4639_);
if (v___x_4640_ == 0)
{
v___y_4621_ = v_a_4639_;
v___y_4622_ = v___y_4631_;
v___y_4623_ = v___y_4632_;
v___y_4624_ = v___y_4633_;
v___y_4625_ = v___y_4634_;
v___y_4626_ = v___y_4635_;
v___y_4627_ = v___y_4636_;
v___y_4628_ = v___y_4637_;
goto v___jp_4620_;
}
else
{
v___y_4621_ = v_a_4639_;
v___y_4622_ = v___y_4631_;
v___y_4623_ = v___y_4632_;
v___y_4624_ = v___y_4633_;
v___y_4625_ = v___y_4634_;
v___y_4626_ = v___y_4635_;
v___y_4627_ = v___y_4636_;
v___y_4628_ = v___x_4439_;
goto v___jp_4620_;
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_dec_ref(v___x_4484_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4641_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4638_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4638_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
v___jp_4649_:
{
if (v___y_4656_ == 0)
{
v___y_4486_ = v___y_4651_;
v___y_4487_ = v___y_4655_;
v___y_4488_ = v___y_4653_;
v___y_4489_ = v___y_4654_;
v___y_4490_ = v___y_4650_;
v___y_4491_ = v___y_4652_;
goto v___jp_4485_;
}
else
{
v___y_4631_ = v___y_4650_;
v___y_4632_ = v___y_4651_;
v___y_4633_ = v___y_4653_;
v___y_4634_ = v___y_4652_;
v___y_4635_ = v___y_4654_;
v___y_4636_ = v___y_4655_;
v___y_4637_ = v___y_4656_;
goto v___jp_4630_;
}
}
v___jp_4657_:
{
uint8_t v_useDecide_4664_; 
v_useDecide_4664_ = lean_ctor_get_uint8(v_config_4332_, sizeof(void*)*1);
if (v_useDecide_4664_ == 0)
{
v___y_4650_ = v___y_4662_;
v___y_4651_ = v_isHEq_4659_;
v___y_4652_ = v___y_4663_;
v___y_4653_ = v___y_4660_;
v___y_4654_ = v___y_4661_;
v___y_4655_ = v___y_4658_;
v___y_4656_ = v___x_4439_;
goto v___jp_4649_;
}
else
{
uint8_t v___x_4665_; 
v___x_4665_ = l_Lean_Expr_hasFVar(v___x_4484_);
if (v___x_4665_ == 0)
{
v___y_4631_ = v___y_4662_;
v___y_4632_ = v_isHEq_4659_;
v___y_4633_ = v___y_4660_;
v___y_4634_ = v___y_4663_;
v___y_4635_ = v___y_4661_;
v___y_4636_ = v___y_4658_;
v___y_4637_ = v_useDecide_4664_;
goto v___jp_4630_;
}
else
{
v___y_4650_ = v___y_4662_;
v___y_4651_ = v_isHEq_4659_;
v___y_4652_ = v___y_4663_;
v___y_4653_ = v___y_4660_;
v___y_4654_ = v___y_4661_;
v___y_4655_ = v___y_4658_;
v___y_4656_ = v___x_4439_;
goto v___jp_4649_;
}
}
}
v___jp_4666_:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Lean_Meta_isExprDefEq(v___y_4669_, v___y_4668_, v___y_4667_, v___y_4671_, v___y_4672_, v___y_4670_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; uint8_t v___x_4676_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref(v___x_4674_);
v___x_4676_ = lean_unbox(v_a_4675_);
lean_dec(v_a_4675_);
if (v___x_4676_ == 0)
{
v___y_4658_ = v___y_4673_;
v_isHEq_4659_ = v___x_4343_;
v___y_4660_ = v___y_4667_;
v___y_4661_ = v___y_4671_;
v___y_4662_ = v___y_4672_;
v___y_4663_ = v___y_4670_;
goto v___jp_4657_;
}
else
{
lean_object* v___x_4677_; 
lean_dec_ref(v___x_4484_);
lean_dec_ref(v_config_4332_);
lean_inc(v_mvarId_4333_);
v___x_4677_ = l_Lean_MVarId_getType(v_mvarId_4333_, v___y_4667_, v___y_4671_, v___y_4672_, v___y_4670_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref(v___x_4677_);
v___x_4679_ = l_Lean_LocalDecl_toExpr(v_val_4364_);
v___x_4680_ = l_Lean_Meta_mkEqOfHEq(v___x_4679_, v___x_4343_, v___y_4667_, v___y_4671_, v___y_4672_, v___y_4670_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4682_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
lean_dec_ref(v___x_4680_);
v___x_4682_ = l_Lean_Meta_mkNoConfusion(v_a_4678_, v_a_4681_, v___y_4667_, v___y_4671_, v___y_4672_, v___y_4670_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4684_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4683_);
lean_dec_ref(v___x_4682_);
v___x_4684_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4333_, v_a_4683_, v___y_4671_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
lean_dec_ref(v___x_4684_);
v___x_4685_ = lean_box(v___x_4343_);
v___x_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
v___x_4687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4686_);
lean_ctor_set(v___x_4687_, 1, v___x_4368_);
v___x_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4687_);
v_a_4350_ = v___x_4688_;
goto v___jp_4349_;
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
v_a_4689_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4684_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4684_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
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
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4697_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4682_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4682_);
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
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec(v_a_4678_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4705_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4680_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4680_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4713_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4677_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4677_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_dec_ref(v___x_4484_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4721_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4674_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4674_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
v___jp_4729_:
{
lean_object* v___x_4735_; 
lean_inc_ref(v___x_4484_);
v___x_4735_ = l_Lean_Meta_matchHEq_x3f(v___x_4484_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref(v___x_4735_);
if (lean_obj_tag(v_a_4736_) == 1)
{
lean_object* v_val_4737_; lean_object* v_snd_4738_; lean_object* v_snd_4739_; lean_object* v_fst_4740_; lean_object* v_fst_4741_; lean_object* v_fst_4742_; lean_object* v_snd_4743_; lean_object* v___x_4744_; 
v_val_4737_ = lean_ctor_get(v_a_4736_, 0);
lean_inc(v_val_4737_);
lean_dec_ref(v_a_4736_);
v_snd_4738_ = lean_ctor_get(v_val_4737_, 1);
lean_inc(v_snd_4738_);
v_snd_4739_ = lean_ctor_get(v_snd_4738_, 1);
lean_inc(v_snd_4739_);
v_fst_4740_ = lean_ctor_get(v_val_4737_, 0);
lean_inc(v_fst_4740_);
lean_dec(v_val_4737_);
v_fst_4741_ = lean_ctor_get(v_snd_4738_, 0);
lean_inc(v_fst_4741_);
lean_dec(v_snd_4738_);
v_fst_4742_ = lean_ctor_get(v_snd_4739_, 0);
lean_inc(v_fst_4742_);
v_snd_4743_ = lean_ctor_get(v_snd_4739_, 1);
lean_inc(v_snd_4743_);
lean_dec(v_snd_4739_);
v___x_4744_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4741_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref(v___x_4744_);
if (lean_obj_tag(v_a_4745_) == 1)
{
lean_object* v_val_4746_; lean_object* v___x_4747_; 
v_val_4746_ = lean_ctor_get(v_a_4745_, 0);
lean_inc(v_val_4746_);
lean_dec_ref(v_a_4745_);
v___x_4747_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4743_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref(v___x_4747_);
if (lean_obj_tag(v_a_4748_) == 1)
{
lean_object* v_toConstantVal_4749_; lean_object* v_val_4750_; lean_object* v_toConstantVal_4751_; lean_object* v_name_4752_; lean_object* v_name_4753_; uint8_t v___x_4754_; 
v_toConstantVal_4749_ = lean_ctor_get(v_val_4746_, 0);
lean_inc_ref(v_toConstantVal_4749_);
lean_dec(v_val_4746_);
v_val_4750_ = lean_ctor_get(v_a_4748_, 0);
lean_inc(v_val_4750_);
lean_dec_ref(v_a_4748_);
v_toConstantVal_4751_ = lean_ctor_get(v_val_4750_, 0);
lean_inc_ref(v_toConstantVal_4751_);
lean_dec(v_val_4750_);
v_name_4752_ = lean_ctor_get(v_toConstantVal_4749_, 0);
lean_inc(v_name_4752_);
lean_dec_ref(v_toConstantVal_4749_);
v_name_4753_ = lean_ctor_get(v_toConstantVal_4751_, 0);
lean_inc(v_name_4753_);
lean_dec_ref(v_toConstantVal_4751_);
v___x_4754_ = lean_name_eq(v_name_4752_, v_name_4753_);
lean_dec(v_name_4753_);
lean_dec(v_name_4752_);
if (v___x_4754_ == 0)
{
v___y_4667_ = v___y_4731_;
v___y_4668_ = v_fst_4742_;
v___y_4669_ = v_fst_4740_;
v___y_4670_ = v___y_4734_;
v___y_4671_ = v___y_4732_;
v___y_4672_ = v___y_4733_;
v___y_4673_ = v_isEq_4730_;
goto v___jp_4666_;
}
else
{
if (v___x_4439_ == 0)
{
lean_dec(v_fst_4742_);
lean_dec(v_fst_4740_);
v___y_4658_ = v_isEq_4730_;
v_isHEq_4659_ = v___x_4343_;
v___y_4660_ = v___y_4731_;
v___y_4661_ = v___y_4732_;
v___y_4662_ = v___y_4733_;
v___y_4663_ = v___y_4734_;
goto v___jp_4657_;
}
else
{
v___y_4667_ = v___y_4731_;
v___y_4668_ = v_fst_4742_;
v___y_4669_ = v_fst_4740_;
v___y_4670_ = v___y_4734_;
v___y_4671_ = v___y_4732_;
v___y_4672_ = v___y_4733_;
v___y_4673_ = v_isEq_4730_;
goto v___jp_4666_;
}
}
}
else
{
lean_dec(v_a_4748_);
lean_dec(v_val_4746_);
lean_dec(v_fst_4742_);
lean_dec(v_fst_4740_);
v___y_4658_ = v_isEq_4730_;
v_isHEq_4659_ = v___x_4343_;
v___y_4660_ = v___y_4731_;
v___y_4661_ = v___y_4732_;
v___y_4662_ = v___y_4733_;
v___y_4663_ = v___y_4734_;
goto v___jp_4657_;
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
lean_dec(v_val_4746_);
lean_dec(v_fst_4742_);
lean_dec(v_fst_4740_);
lean_dec_ref(v___x_4484_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4755_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4747_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4747_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
else
{
lean_dec(v_a_4745_);
lean_dec(v_snd_4743_);
lean_dec(v_fst_4742_);
lean_dec(v_fst_4740_);
v___y_4658_ = v_isEq_4730_;
v_isHEq_4659_ = v___x_4343_;
v___y_4660_ = v___y_4731_;
v___y_4661_ = v___y_4732_;
v___y_4662_ = v___y_4733_;
v___y_4663_ = v___y_4734_;
goto v___jp_4657_;
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_dec(v_snd_4743_);
lean_dec(v_fst_4742_);
lean_dec(v_fst_4740_);
lean_dec_ref(v___x_4484_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4763_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4744_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4744_);
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
else
{
lean_dec(v_a_4736_);
v___y_4658_ = v_isEq_4730_;
v_isHEq_4659_ = v___x_4439_;
v___y_4660_ = v___y_4731_;
v___y_4661_ = v___y_4732_;
v___y_4662_ = v___y_4733_;
v___y_4663_ = v___y_4734_;
goto v___jp_4657_;
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_dec_ref(v___x_4484_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4771_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4735_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4735_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
v___jp_4779_:
{
lean_object* v___x_4784_; 
lean_inc_ref(v___x_4484_);
v___x_4784_ = l_Lean_Meta_matchEq_x3f(v___x_4484_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
lean_inc(v_a_4785_);
lean_dec_ref(v___x_4784_);
if (lean_obj_tag(v_a_4785_) == 1)
{
lean_object* v_val_4786_; lean_object* v_snd_4787_; lean_object* v_fst_4788_; lean_object* v_snd_4789_; lean_object* v___x_4790_; 
v_val_4786_ = lean_ctor_get(v_a_4785_, 0);
lean_inc(v_val_4786_);
lean_dec_ref(v_a_4785_);
v_snd_4787_ = lean_ctor_get(v_val_4786_, 1);
lean_inc(v_snd_4787_);
lean_dec(v_val_4786_);
v_fst_4788_ = lean_ctor_get(v_snd_4787_, 0);
lean_inc(v_fst_4788_);
v_snd_4789_ = lean_ctor_get(v_snd_4787_, 1);
lean_inc(v_snd_4789_);
lean_dec(v_snd_4787_);
v___x_4790_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4788_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v_a_4791_; 
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
lean_inc(v_a_4791_);
lean_dec_ref(v___x_4790_);
if (lean_obj_tag(v_a_4791_) == 1)
{
lean_object* v_val_4792_; lean_object* v___x_4793_; 
v_val_4792_ = lean_ctor_get(v_a_4791_, 0);
lean_inc(v_val_4792_);
lean_dec_ref(v_a_4791_);
v___x_4793_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4789_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref(v___x_4793_);
if (lean_obj_tag(v_a_4794_) == 1)
{
lean_object* v_toConstantVal_4795_; lean_object* v_val_4796_; lean_object* v_toConstantVal_4797_; lean_object* v_name_4798_; lean_object* v_name_4799_; uint8_t v___x_4800_; 
v_toConstantVal_4795_ = lean_ctor_get(v_val_4792_, 0);
lean_inc_ref(v_toConstantVal_4795_);
lean_dec(v_val_4792_);
v_val_4796_ = lean_ctor_get(v_a_4794_, 0);
lean_inc(v_val_4796_);
lean_dec_ref(v_a_4794_);
v_toConstantVal_4797_ = lean_ctor_get(v_val_4796_, 0);
lean_inc_ref(v_toConstantVal_4797_);
lean_dec(v_val_4796_);
v_name_4798_ = lean_ctor_get(v_toConstantVal_4795_, 0);
lean_inc(v_name_4798_);
lean_dec_ref(v_toConstantVal_4795_);
v_name_4799_ = lean_ctor_get(v_toConstantVal_4797_, 0);
lean_inc(v_name_4799_);
lean_dec_ref(v_toConstantVal_4797_);
v___x_4800_ = lean_name_eq(v_name_4798_, v_name_4799_);
lean_dec(v_name_4799_);
lean_dec(v_name_4798_);
if (v___x_4800_ == 0)
{
lean_dec_ref(v___x_4484_);
lean_dec_ref(v_config_4332_);
v___y_4370_ = v___y_4782_;
v___y_4371_ = v___y_4783_;
v___y_4372_ = v___y_4781_;
v___y_4373_ = v___y_4780_;
goto v___jp_4369_;
}
else
{
if (v___x_4439_ == 0)
{
lean_del_object(v___x_4366_);
v_isEq_4730_ = v___x_4343_;
v___y_4731_ = v___y_4780_;
v___y_4732_ = v___y_4781_;
v___y_4733_ = v___y_4782_;
v___y_4734_ = v___y_4783_;
goto v___jp_4729_;
}
else
{
lean_dec_ref(v___x_4484_);
lean_dec_ref(v_config_4332_);
v___y_4370_ = v___y_4782_;
v___y_4371_ = v___y_4783_;
v___y_4372_ = v___y_4781_;
v___y_4373_ = v___y_4780_;
goto v___jp_4369_;
}
}
}
else
{
lean_dec(v_a_4794_);
lean_dec(v_val_4792_);
lean_del_object(v___x_4366_);
v_isEq_4730_ = v___x_4343_;
v___y_4731_ = v___y_4780_;
v___y_4732_ = v___y_4781_;
v___y_4733_ = v___y_4782_;
v___y_4734_ = v___y_4783_;
goto v___jp_4729_;
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_dec(v_val_4792_);
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4801_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4793_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4793_);
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
else
{
lean_dec(v_a_4791_);
lean_dec(v_snd_4789_);
lean_del_object(v___x_4366_);
v_isEq_4730_ = v___x_4343_;
v___y_4731_ = v___y_4780_;
v___y_4732_ = v___y_4781_;
v___y_4733_ = v___y_4782_;
v___y_4734_ = v___y_4783_;
goto v___jp_4729_;
}
}
else
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
lean_dec(v_snd_4789_);
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4809_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4790_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4790_);
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
lean_dec(v_a_4785_);
lean_del_object(v___x_4366_);
v_isEq_4730_ = v___x_4439_;
v___y_4731_ = v___y_4780_;
v___y_4732_ = v___y_4781_;
v___y_4733_ = v___y_4782_;
v___y_4734_ = v___y_4783_;
goto v___jp_4729_;
}
}
else
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4824_; 
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4817_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v___x_4784_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4784_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4822_; 
if (v_isShared_4820_ == 0)
{
v___x_4822_ = v___x_4819_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
v___jp_4825_:
{
lean_object* v___x_4830_; 
lean_inc_ref(v___x_4484_);
v___x_4830_ = l_refutableHasNotBit_x3f(v___x_4484_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref(v___x_4830_);
if (lean_obj_tag(v_a_4831_) == 1)
{
lean_object* v_val_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4872_; 
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec_ref(v_config_4332_);
v_val_4832_ = lean_ctor_get(v_a_4831_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v_a_4831_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4834_ = v_a_4831_;
v_isShared_4835_ = v_isSharedCheck_4872_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_val_4832_);
lean_dec(v_a_4831_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4872_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4836_; 
lean_inc(v_mvarId_4333_);
v___x_4836_ = l_Lean_MVarId_getType(v_mvarId_4333_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v_a_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v_a_4837_ = lean_ctor_get(v___x_4836_, 0);
lean_inc(v_a_4837_);
lean_dec_ref(v___x_4836_);
v___x_4838_ = l_Lean_LocalDecl_toExpr(v_val_4364_);
v___x_4839_ = l_Lean_Meta_mkAbsurd(v_a_4837_, v_val_4832_, v___x_4838_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_object* v_a_4840_; lean_object* v___x_4841_; 
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_a_4840_);
lean_dec_ref(v___x_4839_);
v___x_4841_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4333_, v_a_4840_, v___y_4827_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v___x_4842_; lean_object* v___x_4844_; 
lean_dec_ref(v___x_4841_);
v___x_4842_ = lean_box(v___x_4343_);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 0, v___x_4842_);
v___x_4844_ = v___x_4834_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4842_);
v___x_4844_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
lean_ctor_set(v___x_4845_, 1, v___x_4368_);
v___x_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
v_a_4350_ = v___x_4846_;
goto v___jp_4349_;
}
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
lean_del_object(v___x_4834_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
v_a_4848_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4841_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4841_);
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
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_del_object(v___x_4834_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4856_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4839_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4839_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4871_; 
lean_del_object(v___x_4834_);
lean_dec(v_val_4832_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4864_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4836_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4836_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4869_; 
if (v_isShared_4867_ == 0)
{
v___x_4869_ = v___x_4866_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
}
}
else
{
lean_object* v___x_4873_; 
lean_dec(v_a_4831_);
lean_inc_ref(v___x_4484_);
v___x_4873_ = l_Lean_Meta_matchNe_x3f(v___x_4484_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref(v___x_4873_);
if (lean_obj_tag(v_a_4874_) == 1)
{
lean_object* v_val_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4945_; 
v_val_4875_ = lean_ctor_get(v_a_4874_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v_a_4874_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4877_ = v_a_4874_;
v_isShared_4878_ = v_isSharedCheck_4945_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_val_4875_);
lean_dec(v_a_4874_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4945_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v_snd_4879_; lean_object* v_fst_4880_; lean_object* v_snd_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4944_; 
v_snd_4879_ = lean_ctor_get(v_val_4875_, 1);
lean_inc(v_snd_4879_);
lean_dec(v_val_4875_);
v_fst_4880_ = lean_ctor_get(v_snd_4879_, 0);
v_snd_4881_ = lean_ctor_get(v_snd_4879_, 1);
v_isSharedCheck_4944_ = !lean_is_exclusive(v_snd_4879_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4883_ = v_snd_4879_;
v_isShared_4884_ = v_isSharedCheck_4944_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_snd_4881_);
lean_inc(v_fst_4880_);
lean_dec(v_snd_4879_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4944_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; 
lean_inc(v_fst_4880_);
v___x_4885_ = l_Lean_Meta_isExprDefEq(v_fst_4880_, v_snd_4881_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; uint8_t v___x_4887_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref(v___x_4885_);
v___x_4887_ = lean_unbox(v_a_4886_);
lean_dec(v_a_4886_);
if (v___x_4887_ == 0)
{
lean_del_object(v___x_4883_);
lean_dec(v_fst_4880_);
lean_del_object(v___x_4877_);
v___y_4780_ = v___y_4826_;
v___y_4781_ = v___y_4827_;
v___y_4782_ = v___y_4828_;
v___y_4783_ = v___y_4829_;
goto v___jp_4779_;
}
else
{
lean_object* v___x_4888_; 
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec_ref(v_config_4332_);
lean_inc(v_mvarId_4333_);
v___x_4888_ = l_Lean_MVarId_getType(v_mvarId_4333_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4890_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_a_4889_);
lean_dec_ref(v___x_4888_);
v___x_4890_ = l_Lean_Meta_mkEqRefl(v_fst_4880_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref(v___x_4890_);
v___x_4892_ = l_Lean_LocalDecl_toExpr(v_val_4364_);
v___x_4893_ = l_Lean_Meta_mkAbsurd(v_a_4889_, v_a_4891_, v___x_4892_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v___x_4895_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4894_);
lean_dec_ref(v___x_4893_);
v___x_4895_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4333_, v_a_4894_, v___y_4827_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v___x_4896_; lean_object* v___x_4898_; 
lean_dec_ref(v___x_4895_);
v___x_4896_ = lean_box(v___x_4343_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 0, v___x_4896_);
v___x_4898_ = v___x_4877_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4896_);
v___x_4898_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
lean_object* v___x_4900_; 
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 1, v___x_4368_);
lean_ctor_set(v___x_4883_, 0, v___x_4898_);
v___x_4900_ = v___x_4883_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4898_);
lean_ctor_set(v_reuseFailAlloc_4902_, 1, v___x_4368_);
v___x_4900_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
lean_object* v___x_4901_; 
v___x_4901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4900_);
v_a_4350_ = v___x_4901_;
goto v___jp_4349_;
}
}
}
else
{
lean_object* v_a_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4911_; 
lean_del_object(v___x_4883_);
lean_del_object(v___x_4877_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
v_a_4904_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4911_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4906_ = v___x_4895_;
v_isShared_4907_ = v_isSharedCheck_4911_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_a_4904_);
lean_dec(v___x_4895_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4911_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4909_; 
if (v_isShared_4907_ == 0)
{
v___x_4909_ = v___x_4906_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_a_4904_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
return v___x_4909_;
}
}
}
}
else
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4919_; 
lean_del_object(v___x_4883_);
lean_del_object(v___x_4877_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4912_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4914_ = v___x_4893_;
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4893_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4917_; 
if (v_isShared_4915_ == 0)
{
v___x_4917_ = v___x_4914_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4912_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4927_; 
lean_dec(v_a_4889_);
lean_del_object(v___x_4883_);
lean_del_object(v___x_4877_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4920_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4922_ = v___x_4890_;
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4890_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___x_4925_; 
if (v_isShared_4923_ == 0)
{
v___x_4925_ = v___x_4922_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
else
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
lean_del_object(v___x_4883_);
lean_dec(v_fst_4880_);
lean_del_object(v___x_4877_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4928_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4888_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4888_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
lean_del_object(v___x_4883_);
lean_dec(v_fst_4880_);
lean_del_object(v___x_4877_);
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4936_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4885_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4885_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4874_);
v___y_4780_ = v___y_4826_;
v___y_4781_ = v___y_4827_;
v___y_4782_ = v___y_4828_;
v___y_4783_ = v___y_4829_;
goto v___jp_4779_;
}
}
else
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4953_; 
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4946_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4873_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4873_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4951_; 
if (v_isShared_4949_ == 0)
{
v___x_4951_ = v___x_4948_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
lean_dec_ref(v___x_4484_);
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4954_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4830_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4830_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
}
else
{
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
v_a_4358_ = v___x_4410_;
goto v___jp_4357_;
}
v___jp_4369_:
{
lean_object* v___x_4374_; 
lean_inc(v_mvarId_4333_);
v___x_4374_ = l_Lean_MVarId_getType(v_mvarId_4333_, v___y_4373_, v___y_4372_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref(v___x_4374_);
v___x_4376_ = l_Lean_LocalDecl_toExpr(v_val_4364_);
v___x_4377_ = l_Lean_Meta_mkNoConfusion(v_a_4375_, v___x_4376_, v___y_4373_, v___y_4372_, v___y_4370_, v___y_4371_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref(v___x_4377_);
v___x_4379_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_4333_, v_a_4378_, v___y_4372_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v___x_4380_; lean_object* v___x_4382_; 
lean_dec_ref(v___x_4379_);
v___x_4380_ = lean_box(v___x_4343_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 0, v___x_4380_);
v___x_4382_ = v___x_4366_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4380_);
v___x_4382_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
lean_ctor_set(v___x_4383_, 1, v___x_4368_);
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
v_a_4350_ = v___x_4384_;
goto v___jp_4349_;
}
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
lean_del_object(v___x_4366_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
v_a_4386_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4379_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4379_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
lean_del_object(v___x_4366_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4394_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4377_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4377_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_del_object(v___x_4366_);
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
v_a_4402_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4374_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4374_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
v___jp_4411_:
{
lean_object* v_searchFuel_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v_searchFuel_4416_ = lean_ctor_get(v_config_4332_, 0);
v___x_4417_ = l_Lean_LocalDecl_fvarId(v_val_4364_);
lean_dec(v_val_4364_);
lean_inc(v_searchFuel_4416_);
lean_inc(v_mvarId_4333_);
v___x_4418_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_4333_, v___x_4417_, v_searchFuel_4416_, v___y_4414_, v___y_4413_, v___y_4415_, v___y_4412_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; uint8_t v___x_4420_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4419_);
lean_dec_ref(v___x_4418_);
v___x_4420_ = lean_unbox(v_a_4419_);
lean_dec(v_a_4419_);
if (v___x_4420_ == 0)
{
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
v_a_4358_ = v___x_4410_;
goto v___jp_4357_;
}
else
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v___x_4421_ = lean_box(v___x_4343_);
v___x_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
v___x_4423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4422_);
lean_ctor_set(v___x_4423_, 1, v___x_4368_);
v___x_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4423_);
v_a_4350_ = v___x_4424_;
goto v___jp_4349_;
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4425_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4418_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4418_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
v___jp_4433_:
{
if (v___y_4438_ == 0)
{
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
v_a_4358_ = v___x_4410_;
goto v___jp_4357_;
}
else
{
v___y_4412_ = v___y_4434_;
v___y_4413_ = v___y_4435_;
v___y_4414_ = v___y_4436_;
v___y_4415_ = v___y_4437_;
goto v___jp_4411_;
}
}
v___jp_4440_:
{
if (v___y_4442_ == 0)
{
v___y_4412_ = v___y_4441_;
v___y_4413_ = v___y_4443_;
v___y_4414_ = v___y_4444_;
v___y_4415_ = v___y_4445_;
goto v___jp_4411_;
}
else
{
v___y_4434_ = v___y_4441_;
v___y_4435_ = v___y_4443_;
v___y_4436_ = v___y_4444_;
v___y_4437_ = v___y_4445_;
v___y_4438_ = v___x_4439_;
goto v___jp_4433_;
}
}
v___jp_4446_:
{
if (v___y_4452_ == 0)
{
v___y_4434_ = v___y_4447_;
v___y_4435_ = v___y_4449_;
v___y_4436_ = v___y_4450_;
v___y_4437_ = v___y_4451_;
v___y_4438_ = v___x_4439_;
goto v___jp_4433_;
}
else
{
v___y_4441_ = v___y_4447_;
v___y_4442_ = v___y_4448_;
v___y_4443_ = v___y_4449_;
v___y_4444_ = v___y_4450_;
v___y_4445_ = v___y_4451_;
goto v___jp_4440_;
}
}
v___jp_4453_:
{
uint8_t v_emptyType_4460_; 
v_emptyType_4460_ = lean_ctor_get_uint8(v_config_4332_, sizeof(void*)*1 + 1);
if (v_emptyType_4460_ == 0)
{
v___y_4447_ = v___y_4459_;
v___y_4448_ = v___y_4454_;
v___y_4449_ = v___y_4457_;
v___y_4450_ = v___y_4456_;
v___y_4451_ = v___y_4458_;
v___y_4452_ = v___x_4439_;
goto v___jp_4446_;
}
else
{
if (v___y_4455_ == 0)
{
v___y_4441_ = v___y_4459_;
v___y_4442_ = v___y_4454_;
v___y_4443_ = v___y_4457_;
v___y_4444_ = v___y_4456_;
v___y_4445_ = v___y_4458_;
goto v___jp_4440_;
}
else
{
v___y_4447_ = v___y_4459_;
v___y_4448_ = v___y_4454_;
v___y_4449_ = v___y_4457_;
v___y_4450_ = v___y_4456_;
v___y_4451_ = v___y_4458_;
v___y_4452_ = v___x_4439_;
goto v___jp_4446_;
}
}
}
v___jp_4461_:
{
if (v___y_4468_ == 0)
{
v___y_4454_ = v___y_4462_;
v___y_4455_ = v___y_4467_;
v___y_4456_ = v___y_4463_;
v___y_4457_ = v___y_4464_;
v___y_4458_ = v___y_4465_;
v___y_4459_ = v___y_4466_;
goto v___jp_4453_;
}
else
{
lean_object* v___x_4469_; 
lean_inc(v_val_4364_);
lean_inc(v_mvarId_4333_);
v___x_4469_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_4333_, v_val_4364_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; uint8_t v___x_4471_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc(v_a_4470_);
lean_dec_ref(v___x_4469_);
v___x_4471_ = lean_unbox(v_a_4470_);
lean_dec(v_a_4470_);
if (v___x_4471_ == 0)
{
v___y_4454_ = v___y_4462_;
v___y_4455_ = v___y_4467_;
v___y_4456_ = v___y_4463_;
v___y_4457_ = v___y_4464_;
v___y_4458_ = v___y_4465_;
v___y_4459_ = v___y_4466_;
goto v___jp_4453_;
}
else
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_dec(v_val_4364_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v___x_4472_ = lean_box(v___x_4343_);
v___x_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
v___x_4474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4473_);
lean_ctor_set(v___x_4474_, 1, v___x_4368_);
v___x_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
v_a_4350_ = v___x_4475_;
goto v___jp_4349_;
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec(v_val_4364_);
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec(v_mvarId_4333_);
lean_dec_ref(v_config_4332_);
v_a_4476_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4469_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4469_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
}
}
}
v___jp_4349_:
{
lean_object* v___x_4351_; lean_object* v___x_4353_; 
v___x_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4351_, 0, v_a_4350_);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 0, v___x_4351_);
v___x_4353_ = v___x_4347_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4351_);
lean_ctor_set(v_reuseFailAlloc_4355_, 1, v_snd_4345_);
v___x_4353_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
lean_object* v___x_4354_; 
v___x_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4353_);
return v___x_4354_;
}
}
v___jp_4357_:
{
lean_object* v___x_4359_; size_t v___x_4360_; size_t v___x_4361_; lean_object* v___x_4362_; 
v___x_4359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4356_);
lean_ctor_set(v___x_4359_, 1, v_a_4358_);
v___x_4360_ = ((size_t)1ULL);
v___x_4361_ = lean_usize_add(v_i_4336_, v___x_4360_);
v___x_4362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_4332_, v_mvarId_4333_, v_as_4334_, v_sz_4335_, v___x_4361_, v___x_4359_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
return v___x_4362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_5035_, lean_object* v_mvarId_5036_, lean_object* v_as_5037_, lean_object* v_sz_5038_, lean_object* v_i_5039_, lean_object* v_b_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
size_t v_sz_boxed_5046_; size_t v_i_boxed_5047_; lean_object* v_res_5048_; 
v_sz_boxed_5046_ = lean_unbox_usize(v_sz_5038_);
lean_dec(v_sz_5038_);
v_i_boxed_5047_ = lean_unbox_usize(v_i_5039_);
lean_dec(v_i_5039_);
v_res_5048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_5035_, v_mvarId_5036_, v_as_5037_, v_sz_boxed_5046_, v_i_boxed_5047_, v_b_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec_ref(v_as_5037_);
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_5049_, lean_object* v_config_5050_, lean_object* v_mvarId_5051_, lean_object* v_n_5052_, lean_object* v_b_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_){
_start:
{
if (lean_obj_tag(v_n_5052_) == 0)
{
lean_object* v_cs_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5093_; 
v_cs_5059_ = lean_ctor_get(v_n_5052_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v_n_5052_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5061_ = v_n_5052_;
v_isShared_5062_ = v_isSharedCheck_5093_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_cs_5059_);
lean_dec(v_n_5052_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5093_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; size_t v_sz_5065_; size_t v___x_5066_; lean_object* v___x_5067_; 
v___x_5063_ = lean_box(0);
v___x_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5063_);
lean_ctor_set(v___x_5064_, 1, v_b_5053_);
v_sz_5065_ = lean_array_size(v_cs_5059_);
v___x_5066_ = ((size_t)0ULL);
v___x_5067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_5049_, v_config_5050_, v_mvarId_5051_, v_cs_5059_, v_sz_5065_, v___x_5066_, v___x_5064_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
lean_dec_ref(v_cs_5059_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5084_; 
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5070_ = v___x_5067_;
v_isShared_5071_ = v_isSharedCheck_5084_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5067_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5084_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v_fst_5072_; 
v_fst_5072_ = lean_ctor_get(v_a_5068_, 0);
if (lean_obj_tag(v_fst_5072_) == 0)
{
lean_object* v_snd_5073_; lean_object* v___x_5075_; 
v_snd_5073_ = lean_ctor_get(v_a_5068_, 1);
lean_inc(v_snd_5073_);
lean_dec(v_a_5068_);
if (v_isShared_5062_ == 0)
{
lean_ctor_set_tag(v___x_5061_, 1);
lean_ctor_set(v___x_5061_, 0, v_snd_5073_);
v___x_5075_ = v___x_5061_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_snd_5073_);
v___x_5075_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
lean_object* v___x_5077_; 
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 0, v___x_5075_);
v___x_5077_ = v___x_5070_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v___x_5075_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
else
{
lean_object* v_val_5080_; lean_object* v___x_5082_; 
lean_inc_ref(v_fst_5072_);
lean_dec(v_a_5068_);
lean_del_object(v___x_5061_);
v_val_5080_ = lean_ctor_get(v_fst_5072_, 0);
lean_inc(v_val_5080_);
lean_dec_ref(v_fst_5072_);
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 0, v_val_5080_);
v___x_5082_ = v___x_5070_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_val_5080_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_del_object(v___x_5061_);
v_a_5085_ = lean_ctor_get(v___x_5067_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5067_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5067_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
}
else
{
lean_object* v_vs_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5128_; 
v_vs_5094_ = lean_ctor_get(v_n_5052_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v_n_5052_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5096_ = v_n_5052_;
v_isShared_5097_ = v_isSharedCheck_5128_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_vs_5094_);
lean_dec(v_n_5052_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5128_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; size_t v_sz_5100_; size_t v___x_5101_; lean_object* v___x_5102_; 
v___x_5098_ = lean_box(0);
v___x_5099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5098_);
lean_ctor_set(v___x_5099_, 1, v_b_5053_);
v_sz_5100_ = lean_array_size(v_vs_5094_);
v___x_5101_ = ((size_t)0ULL);
v___x_5102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_5050_, v_mvarId_5051_, v_vs_5094_, v_sz_5100_, v___x_5101_, v___x_5099_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
lean_dec_ref(v_vs_5094_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5119_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5105_ = v___x_5102_;
v_isShared_5106_ = v_isSharedCheck_5119_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5102_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5119_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v_fst_5107_; 
v_fst_5107_ = lean_ctor_get(v_a_5103_, 0);
if (lean_obj_tag(v_fst_5107_) == 0)
{
lean_object* v_snd_5108_; lean_object* v___x_5110_; 
v_snd_5108_ = lean_ctor_get(v_a_5103_, 1);
lean_inc(v_snd_5108_);
lean_dec(v_a_5103_);
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 0, v_snd_5108_);
v___x_5110_ = v___x_5096_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_snd_5108_);
v___x_5110_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
lean_object* v___x_5112_; 
if (v_isShared_5106_ == 0)
{
lean_ctor_set(v___x_5105_, 0, v___x_5110_);
v___x_5112_ = v___x_5105_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5110_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
else
{
lean_object* v_val_5115_; lean_object* v___x_5117_; 
lean_inc_ref(v_fst_5107_);
lean_dec(v_a_5103_);
lean_del_object(v___x_5096_);
v_val_5115_ = lean_ctor_get(v_fst_5107_, 0);
lean_inc(v_val_5115_);
lean_dec_ref(v_fst_5107_);
if (v_isShared_5106_ == 0)
{
lean_ctor_set(v___x_5105_, 0, v_val_5115_);
v___x_5117_ = v___x_5105_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_val_5115_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
else
{
lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5127_; 
lean_del_object(v___x_5096_);
v_a_5120_ = lean_ctor_get(v___x_5102_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5122_ = v___x_5102_;
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5102_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5125_; 
if (v_isShared_5123_ == 0)
{
v___x_5125_ = v___x_5122_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5120_);
v___x_5125_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
return v___x_5125_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_5129_, lean_object* v_config_5130_, lean_object* v_mvarId_5131_, lean_object* v_as_5132_, size_t v_sz_5133_, size_t v_i_5134_, lean_object* v_b_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
uint8_t v___x_5141_; 
v___x_5141_ = lean_usize_dec_lt(v_i_5134_, v_sz_5133_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; 
lean_dec(v_mvarId_5131_);
lean_dec_ref(v_config_5130_);
v___x_5142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5142_, 0, v_b_5135_);
return v___x_5142_;
}
else
{
lean_object* v_snd_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5177_; 
v_snd_5143_ = lean_ctor_get(v_b_5135_, 1);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_b_5135_);
if (v_isSharedCheck_5177_ == 0)
{
lean_object* v_unused_5178_; 
v_unused_5178_ = lean_ctor_get(v_b_5135_, 0);
lean_dec(v_unused_5178_);
v___x_5145_ = v_b_5135_;
v_isShared_5146_ = v_isSharedCheck_5177_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_snd_5143_);
lean_dec(v_b_5135_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5177_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v_a_5147_; lean_object* v___x_5148_; 
v_a_5147_ = lean_array_uget_borrowed(v_as_5132_, v_i_5134_);
lean_inc(v_snd_5143_);
lean_inc(v_a_5147_);
lean_inc(v_mvarId_5131_);
lean_inc_ref(v_config_5130_);
v___x_5148_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_5129_, v_config_5130_, v_mvarId_5131_, v_a_5147_, v_snd_5143_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5168_; 
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5151_ = v___x_5148_;
v_isShared_5152_ = v_isSharedCheck_5168_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5148_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5168_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
if (lean_obj_tag(v_a_5149_) == 0)
{
lean_object* v___x_5153_; lean_object* v___x_5155_; 
lean_dec(v_mvarId_5131_);
lean_dec_ref(v_config_5130_);
v___x_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5153_, 0, v_a_5149_);
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 0, v___x_5153_);
v___x_5155_ = v___x_5145_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5153_);
lean_ctor_set(v_reuseFailAlloc_5159_, 1, v_snd_5143_);
v___x_5155_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
lean_object* v___x_5157_; 
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 0, v___x_5155_);
v___x_5157_ = v___x_5151_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v___x_5155_);
v___x_5157_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
return v___x_5157_;
}
}
}
else
{
lean_object* v_a_5160_; lean_object* v___x_5161_; lean_object* v___x_5163_; 
lean_del_object(v___x_5151_);
lean_dec(v_snd_5143_);
v_a_5160_ = lean_ctor_get(v_a_5149_, 0);
lean_inc(v_a_5160_);
lean_dec_ref(v_a_5149_);
v___x_5161_ = lean_box(0);
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 1, v_a_5160_);
lean_ctor_set(v___x_5145_, 0, v___x_5161_);
v___x_5163_ = v___x_5145_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5161_);
lean_ctor_set(v_reuseFailAlloc_5167_, 1, v_a_5160_);
v___x_5163_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
size_t v___x_5164_; size_t v___x_5165_; 
v___x_5164_ = ((size_t)1ULL);
v___x_5165_ = lean_usize_add(v_i_5134_, v___x_5164_);
v_i_5134_ = v___x_5165_;
v_b_5135_ = v___x_5163_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
lean_del_object(v___x_5145_);
lean_dec(v_snd_5143_);
lean_dec(v_mvarId_5131_);
lean_dec_ref(v_config_5130_);
v_a_5169_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5171_ = v___x_5148_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v___x_5148_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5179_, lean_object* v_config_5180_, lean_object* v_mvarId_5181_, lean_object* v_as_5182_, lean_object* v_sz_5183_, lean_object* v_i_5184_, lean_object* v_b_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
size_t v_sz_boxed_5191_; size_t v_i_boxed_5192_; lean_object* v_res_5193_; 
v_sz_boxed_5191_ = lean_unbox_usize(v_sz_5183_);
lean_dec(v_sz_5183_);
v_i_boxed_5192_ = lean_unbox_usize(v_i_5184_);
lean_dec(v_i_5184_);
v_res_5193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_5179_, v_config_5180_, v_mvarId_5181_, v_as_5182_, v_sz_boxed_5191_, v_i_boxed_5192_, v_b_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec_ref(v_as_5182_);
lean_dec_ref(v_init_5179_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_5194_, lean_object* v_config_5195_, lean_object* v_mvarId_5196_, lean_object* v_n_5197_, lean_object* v_b_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_5194_, v_config_5195_, v_mvarId_5196_, v_n_5197_, v_b_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_init_5194_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_5205_, lean_object* v_mvarId_5206_, lean_object* v_t_5207_, lean_object* v_init_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_){
_start:
{
lean_object* v_root_5214_; lean_object* v_tail_5215_; lean_object* v___x_5216_; 
v_root_5214_ = lean_ctor_get(v_t_5207_, 0);
lean_inc_ref(v_root_5214_);
v_tail_5215_ = lean_ctor_get(v_t_5207_, 1);
lean_inc_ref(v_tail_5215_);
lean_dec_ref(v_t_5207_);
lean_inc(v_mvarId_5206_);
lean_inc_ref(v_config_5205_);
lean_inc_ref(v_init_5208_);
v___x_5216_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_5208_, v_config_5205_, v_mvarId_5206_, v_root_5214_, v_init_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
lean_dec_ref(v_init_5208_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5253_; 
v_a_5217_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5219_ = v___x_5216_;
v_isShared_5220_ = v_isSharedCheck_5253_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_a_5217_);
lean_dec(v___x_5216_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5253_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
if (lean_obj_tag(v_a_5217_) == 0)
{
lean_object* v_a_5221_; lean_object* v___x_5223_; 
lean_dec_ref(v_tail_5215_);
lean_dec(v_mvarId_5206_);
lean_dec_ref(v_config_5205_);
v_a_5221_ = lean_ctor_get(v_a_5217_, 0);
lean_inc(v_a_5221_);
lean_dec_ref(v_a_5217_);
if (v_isShared_5220_ == 0)
{
lean_ctor_set(v___x_5219_, 0, v_a_5221_);
v___x_5223_ = v___x_5219_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5221_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; size_t v_sz_5228_; size_t v___x_5229_; lean_object* v___x_5230_; 
lean_del_object(v___x_5219_);
v_a_5225_ = lean_ctor_get(v_a_5217_, 0);
lean_inc(v_a_5225_);
lean_dec_ref(v_a_5217_);
v___x_5226_ = lean_box(0);
v___x_5227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5226_);
lean_ctor_set(v___x_5227_, 1, v_a_5225_);
v_sz_5228_ = lean_array_size(v_tail_5215_);
v___x_5229_ = ((size_t)0ULL);
v___x_5230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_5205_, v_mvarId_5206_, v_tail_5215_, v_sz_5228_, v___x_5229_, v___x_5227_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
lean_dec_ref(v_tail_5215_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5244_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5233_ = v___x_5230_;
v_isShared_5234_ = v_isSharedCheck_5244_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5230_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5244_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v_fst_5235_; 
v_fst_5235_ = lean_ctor_get(v_a_5231_, 0);
if (lean_obj_tag(v_fst_5235_) == 0)
{
lean_object* v_snd_5236_; lean_object* v___x_5238_; 
v_snd_5236_ = lean_ctor_get(v_a_5231_, 1);
lean_inc(v_snd_5236_);
lean_dec(v_a_5231_);
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 0, v_snd_5236_);
v___x_5238_ = v___x_5233_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_snd_5236_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
else
{
lean_object* v_val_5240_; lean_object* v___x_5242_; 
lean_inc_ref(v_fst_5235_);
lean_dec(v_a_5231_);
v_val_5240_ = lean_ctor_get(v_fst_5235_, 0);
lean_inc(v_val_5240_);
lean_dec_ref(v_fst_5235_);
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 0, v_val_5240_);
v___x_5242_ = v___x_5233_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_val_5240_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
}
}
else
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5252_; 
v_a_5245_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5230_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5230_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
}
}
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5261_; 
lean_dec_ref(v_tail_5215_);
lean_dec(v_mvarId_5206_);
lean_dec_ref(v_config_5205_);
v_a_5254_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5256_ = v___x_5216_;
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5216_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_5262_, lean_object* v_mvarId_5263_, lean_object* v_t_5264_, lean_object* v_init_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_5262_, v_mvarId_5263_, v_t_5264_, v_init_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_5272_, lean_object* v___x_5273_, lean_object* v_config_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v___x_5280_; 
lean_inc(v_mvarId_5272_);
v___x_5280_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_5272_, v___x_5273_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_);
if (lean_obj_tag(v___x_5280_) == 0)
{
lean_object* v___x_5281_; 
lean_dec_ref(v___x_5280_);
lean_inc(v_mvarId_5272_);
v___x_5281_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_5272_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_);
if (lean_obj_tag(v___x_5281_) == 0)
{
lean_object* v_a_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5315_; 
v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5281_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5284_ = v___x_5281_;
v_isShared_5285_ = v_isSharedCheck_5315_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_a_5282_);
lean_dec(v___x_5281_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5315_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
uint8_t v___x_5286_; 
v___x_5286_ = lean_unbox(v_a_5282_);
if (v___x_5286_ == 0)
{
lean_object* v_lctx_5287_; lean_object* v_decls_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; 
lean_del_object(v___x_5284_);
v_lctx_5287_ = lean_ctor_get(v___y_5275_, 2);
v_decls_5288_ = lean_ctor_get(v_lctx_5287_, 1);
lean_inc_ref(v_decls_5288_);
v___x_5289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_5290_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_5274_, v_mvarId_5272_, v_decls_5288_, v___x_5289_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_);
lean_dec_ref(v___y_5275_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5303_; 
v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5293_ = v___x_5290_;
v_isShared_5294_ = v_isSharedCheck_5303_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___x_5290_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5303_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v_fst_5295_; 
v_fst_5295_ = lean_ctor_get(v_a_5291_, 0);
lean_inc(v_fst_5295_);
lean_dec(v_a_5291_);
if (lean_obj_tag(v_fst_5295_) == 0)
{
lean_object* v___x_5297_; 
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 0, v_a_5282_);
v___x_5297_ = v___x_5293_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_a_5282_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
else
{
lean_object* v_val_5299_; lean_object* v___x_5301_; 
lean_dec(v_a_5282_);
v_val_5299_ = lean_ctor_get(v_fst_5295_, 0);
lean_inc(v_val_5299_);
lean_dec_ref(v_fst_5295_);
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 0, v_val_5299_);
v___x_5301_ = v___x_5293_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_val_5299_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
}
else
{
lean_object* v_a_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5311_; 
lean_dec(v_a_5282_);
v_a_5304_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5306_ = v___x_5290_;
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_a_5304_);
lean_dec(v___x_5290_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5309_; 
if (v_isShared_5307_ == 0)
{
v___x_5309_ = v___x_5306_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5304_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
return v___x_5309_;
}
}
}
}
else
{
lean_object* v___x_5313_; 
lean_dec_ref(v___y_5275_);
lean_dec_ref(v_config_5274_);
lean_dec(v_mvarId_5272_);
if (v_isShared_5285_ == 0)
{
v___x_5313_ = v___x_5284_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5282_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
}
}
else
{
lean_dec_ref(v___y_5275_);
lean_dec_ref(v_config_5274_);
lean_dec(v_mvarId_5272_);
return v___x_5281_;
}
}
else
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
lean_dec_ref(v___y_5275_);
lean_dec_ref(v_config_5274_);
lean_dec(v_mvarId_5272_);
v_a_5316_ = lean_ctor_get(v___x_5280_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5318_ = v___x_5280_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5280_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_5324_, lean_object* v___x_5325_, lean_object* v_config_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_5324_, v___x_5325_, v_config_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_5335_, lean_object* v_config_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_){
_start:
{
lean_object* v___x_5342_; lean_object* v___f_5343_; lean_object* v___x_5344_; 
v___x_5342_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_5335_);
v___f_5343_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5343_, 0, v_mvarId_5335_);
lean_closure_set(v___f_5343_, 1, v___x_5342_);
lean_closure_set(v___f_5343_, 2, v_config_5336_);
v___x_5344_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_5335_, v___f_5343_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_);
return v___x_5344_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_5345_, lean_object* v_config_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_){
_start:
{
lean_object* v_res_5352_; 
v_res_5352_ = l_Lean_MVarId_contradictionCore(v_mvarId_5345_, v_config_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_);
lean_dec(v_a_5350_);
lean_dec_ref(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec_ref(v_a_5347_);
return v_res_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_5353_, lean_object* v_config_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_){
_start:
{
lean_object* v___x_5360_; 
lean_inc(v_mvarId_5353_);
v___x_5360_ = l_Lean_MVarId_contradictionCore(v_mvarId_5353_, v_config_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5373_; 
v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5363_ = v___x_5360_;
v_isShared_5364_ = v_isSharedCheck_5373_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5360_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5373_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
uint8_t v___x_5365_; 
v___x_5365_ = lean_unbox(v_a_5361_);
lean_dec(v_a_5361_);
if (v___x_5365_ == 0)
{
lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; 
lean_del_object(v___x_5363_);
v___x_5366_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_5367_ = lean_box(0);
v___x_5368_ = l_Lean_Meta_throwTacticEx___redArg(v___x_5366_, v_mvarId_5353_, v___x_5367_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
return v___x_5368_;
}
else
{
lean_object* v___x_5369_; lean_object* v___x_5371_; 
lean_dec(v_mvarId_5353_);
v___x_5369_ = lean_box(0);
if (v_isShared_5364_ == 0)
{
lean_ctor_set(v___x_5363_, 0, v___x_5369_);
v___x_5371_ = v___x_5363_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
else
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
lean_dec(v_mvarId_5353_);
v_a_5374_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5360_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5360_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5374_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_5382_, lean_object* v_config_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_){
_start:
{
lean_object* v_res_5389_; 
v_res_5389_ = l_Lean_MVarId_contradiction(v_mvarId_5382_, v_config_5383_, v_a_5384_, v_a_5385_, v_a_5386_, v_a_5387_);
lean_dec(v_a_5387_);
lean_dec_ref(v_a_5386_);
lean_dec(v_a_5385_);
lean_dec_ref(v_a_5384_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5452_; uint8_t v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v___x_5452_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_5453_ = 0;
v___x_5454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_5455_ = l_Lean_registerTraceClass(v___x_5452_, v___x_5453_, v___x_5454_);
return v___x_5455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_5456_){
_start:
{
lean_object* v_res_5457_; 
v_res_5457_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_5457_;
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
