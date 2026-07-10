// Lean compiler output
// Module: Lean.Elab.Tactic.ElabTerm
// Imports: public import Lean.Meta.Tactic.Constructor public import Lean.Meta.Tactic.Replace public import Lean.Meta.Tactic.Rename public import Lean.Elab.Tactic.Basic public import Lean.Elab.SyntheticMVars
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLetRecAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Elab_Tactic_popMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pushGoal___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarKind_isNatural(uint8_t);
lean_object* l_Lean_Elab_Tactic_getMainTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getLambdaBody(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM;
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
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 30, 230, 20, 64, 162, 204, 1)}};
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 17, 142, 189, 192, 166, 31, 124)}};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "reuse stopped: guard failed at "};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "attempting to close the goal using"};
static const lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "\nthis is often due occurs-check failure"};
static const lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExact___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(181, 27, 253, 38, 166, 91, 92, 173)}};
static const lean_object* l_Lean_Elab_Tactic_evalExact___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalExact"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 234, 120, 244, 69, 129, 106, 222)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_refineCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`refine` tactic failed, value"};
static const lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_refineCore___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_refineCore___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_refineCore___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "\ndepends on the main goal metavariable `"};
static const lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_refineCore___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_refineCore___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_refineCore___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_refineCore___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRefine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* l_Lean_Elab_Tactic_evalRefine___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* l_Lean_Elab_Tactic_evalRefine___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 66, 166, 159, 104, 233, 32, 227)}};
static const lean_object* l_Lean_Elab_Tactic_evalRefine___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalRefine"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 145, 22, 71, 20, 173, 227, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(189) << 1) | 1)),((lean_object*)(((size_t)(27) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(192) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0_value),((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(189) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(189) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4_value),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "refine'"};
static const lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 47, 162, 14, 79, 14, 110, 97)}};
static const lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRefine_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 29, 86, 242, 162, 231, 137, 148)}};
static const lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRefine_x27___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalRefine'"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 77, 214, 78, 10, 226, 57, 225)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(194) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(197) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0_value),((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(194) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(194) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"};
static const lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalSpecialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "specialize"};
static const lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalSpecialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 64, 50, 7, 167, 240, 212, 2)}};
static const lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalSpecialize___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalSpecialize"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 32, 237, 136, 248, 73, 56, 16)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(199) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(212) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0_value),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(199) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(199) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4_value),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabTermForApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_Tactic_elabTermForApply___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabTermForApply___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unexpected term `"};
static const lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "`; expected single reference to variable"};
static const lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_getFVarIds___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_getFVarIds___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Lean_Elab_Tactic_evalApply___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalApply___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_Lean_Elab_Tactic_evalApply___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalApply___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalApply"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 174, 163, 187, 9, 67, 156, 69)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(303) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(306) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(303) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(303) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_evalConstructor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalConstructor___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "constructor"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 188, 57, 91, 27, 124, 155, 13)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalConstructor"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(27, 148, 222, 77, 61, 137, 212, 52)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(308) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(312) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0_value),((lean_object*)(((size_t)(49) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1_value),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(308) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(308) << 1) | 1)),((lean_object*)(((size_t)(68) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4_value),((lean_object*)(((size_t)(68) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_evalWithReducible___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_evalWithReducible___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "evalWithReducible"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 233, 43, 192, 30, 109, 64, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(314) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(315) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(314) << 1) | 1)),((lean_object*)(((size_t)(55) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(314) << 1) | 1)),((lean_object*)(((size_t)(72) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3_value),((lean_object*)(((size_t)(55) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4_value),((lean_object*)(((size_t)(72) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "withReducibleAndInstances"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 231, 54, 217, 251, 49, 216, 49)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "evalWithReducibleAndInstances"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 161, 97, 73, 21, 6, 2, 115)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(317) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(318) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1_value),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(317) << 1) | 1)),((lean_object*)(((size_t)(67) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(317) << 1) | 1)),((lean_object*)(((size_t)(96) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3_value),((lean_object*)(((size_t)(67) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4_value),((lean_object*)(((size_t)(96) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_evalWithImplicit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_evalWithImplicit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withImplicit"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 55, 151, 94, 210, 189, 147, 133)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalWithImplicit"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 18, 145, 67, 71, 155, 218, 120)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withUnfoldingAll"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 182, 19, 172, 53, 51, 56, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalWithUnfoldingAll"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 149, 127, 27, 154, 31, 88, 150)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(320) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(321) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1_value),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(320) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(320) << 1) | 1)),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3_value),((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4_value),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "withUnfoldingNone"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 40, 27, 134, 15, 218, 231, 86)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "evalWithUnfoldingNone"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(163, 180, 80, 132, 38, 173, 2, 159)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRename___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to find a hypothesis with type"};
static const lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalRename___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rename"};
static const lean_object* l_Lean_Elab_Tactic_evalRename___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 242, 239, 56, 25, 190, 128, 68)}};
static const lean_object* l_Lean_Elab_Tactic_evalRename___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalRename___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_evalRename___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalRename___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_evalRename___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalRename___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalRename"};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 112, 92, 205, 132, 47, 133, 163)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(344) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(359) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0_value),((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(344) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(344) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4_value),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(lean_object* v_k_1_, uint8_t v_mayPostpone_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_10_; 
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_10_ = lean_apply_7(v_k_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, lean_box(0));
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; uint8_t v___x_12_; uint8_t v___x_13_; lean_object* v___x_14_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_a_11_);
lean_dec_ref_known(v___x_10_, 1);
v___x_12_ = l_Lean_Elab_Term_PostponeBehavior_ofBool(v_mayPostpone_2_);
v___x_13_ = 0;
v___x_14_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_12_, v___x_13_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_21_ == 0)
{
lean_object* v_unused_22_; 
v_unused_22_ = lean_ctor_get(v___x_14_, 0);
lean_dec(v_unused_22_);
v___x_16_ = v___x_14_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_dec(v___x_14_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v_a_11_);
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_a_11_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
lean_dec(v_a_11_);
v_a_23_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_14_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_14_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
else
{
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg___boxed(lean_object* v_k_31_, lean_object* v_mayPostpone_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
uint8_t v_mayPostpone_boxed_40_; lean_object* v_res_41_; 
v_mayPostpone_boxed_40_ = lean_unbox(v_mayPostpone_32_);
v_res_41_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_31_, v_mayPostpone_boxed_40_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go(lean_object* v_00_u03b1_42_, lean_object* v_k_43_, uint8_t v_mayPostpone_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_43_, v_mayPostpone_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___boxed(lean_object* v_00_u03b1_53_, lean_object* v_k_54_, lean_object* v_mayPostpone_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
uint8_t v_mayPostpone_boxed_63_; lean_object* v_res_64_; 
v_mayPostpone_boxed_63_ = lean_unbox(v_mayPostpone_55_);
v_res_64_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go(v_00_u03b1_53_, v_k_54_, v_mayPostpone_boxed_63_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(lean_object* v_a_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_inc(v___y_67_);
lean_inc_ref(v___y_66_);
v___x_75_ = lean_apply_2(v_a_65_, v___y_66_, v___y_67_);
v___x_76_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_75_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg___boxed(lean_object* v_a_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(v_a_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0(lean_object* v_00_u03b1_88_, lean_object* v_a_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(v_a_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___boxed(lean_object* v_00_u03b1_100_, lean_object* v_a_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0(v_00_u03b1_100_, v_a_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_111_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(uint8_t v_cond_112_, lean_object* v_x_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = lean_bool_not(v_cond_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed(lean_object* v_cond_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_cond_boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v_cond_boxed_117_ = lean_unbox(v_cond_115_);
v_res_118_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_boxed_117_, v_x_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(uint8_t v_cond_128_, lean_object* v_act_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_options_139_; lean_object* v_declName_x3f_140_; lean_object* v_macroStack_141_; uint8_t v_mayPostpone_142_; uint8_t v_errToSorry_143_; lean_object* v_autoBoundImplicitContext_144_; lean_object* v_autoBoundImplicitForbidden_145_; lean_object* v_sectionVars_146_; lean_object* v_sectionFVars_147_; uint8_t v_implicitLambda_148_; uint8_t v_heedElabAsElim_149_; uint8_t v_isNoncomputableSection_150_; uint8_t v_isMetaSection_151_; uint8_t v_ignoreTCFailures_152_; uint8_t v_inPattern_153_; lean_object* v_tacSnap_x3f_154_; uint8_t v_saveRecAppSyntax_155_; uint8_t v_holesAsSyntheticOpaque_156_; uint8_t v_checkDeprecated_157_; lean_object* v_fixedTermElabs_158_; lean_object* v___y_160_; uint8_t v___y_164_; 
v_options_139_ = lean_ctor_get(v___y_136_, 2);
v_declName_x3f_140_ = lean_ctor_get(v___y_132_, 0);
v_macroStack_141_ = lean_ctor_get(v___y_132_, 1);
v_mayPostpone_142_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8);
v_errToSorry_143_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_144_ = lean_ctor_get(v___y_132_, 2);
v_autoBoundImplicitForbidden_145_ = lean_ctor_get(v___y_132_, 3);
v_sectionVars_146_ = lean_ctor_get(v___y_132_, 4);
v_sectionFVars_147_ = lean_ctor_get(v___y_132_, 5);
v_implicitLambda_148_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 2);
v_heedElabAsElim_149_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_150_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 4);
v_isMetaSection_151_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_152_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 6);
v_inPattern_153_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_154_ = lean_ctor_get(v___y_132_, 6);
v_saveRecAppSyntax_155_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_156_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 9);
v_checkDeprecated_157_ = lean_ctor_get_uint8(v___y_132_, sizeof(void*)*8 + 10);
v_fixedTermElabs_158_ = lean_ctor_get(v___y_132_, 7);
if (lean_obj_tag(v_tacSnap_x3f_154_) == 0)
{
v___y_160_ = v_tacSnap_x3f_154_;
goto v___jp_159_;
}
else
{
lean_object* v_val_168_; lean_object* v_old_x3f_169_; 
v_val_168_ = lean_ctor_get(v_tacSnap_x3f_154_, 0);
v_old_x3f_169_ = lean_ctor_get(v_val_168_, 0);
if (lean_obj_tag(v_old_x3f_169_) == 1)
{
if (v_cond_128_ == 0)
{
goto v___jp_166_;
}
else
{
lean_object* v_val_170_; lean_object* v_map_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_val_170_ = lean_ctor_get(v_old_x3f_169_, 0);
v_map_171_ = lean_ctor_get(v_options_139_, 0);
v___x_172_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3));
v___x_173_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_171_, v___x_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
goto v___jp_166_;
}
else
{
lean_object* v_val_174_; 
v_val_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_174_);
lean_dec_ref_known(v___x_173_, 1);
if (lean_obj_tag(v_val_174_) == 1)
{
uint8_t v_v_175_; 
v_v_175_ = lean_ctor_get_uint8(v_val_174_, 0);
lean_dec_ref_known(v_val_174_, 0);
if (v_v_175_ == 0)
{
goto v___jp_166_;
}
else
{
lean_object* v_stx_176_; lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_stx_176_ = lean_ctor_get(v_val_170_, 0);
v___x_177_ = lean_box(v_cond_128_);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_178_, 0, v___x_177_);
v___x_179_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4));
v___x_180_ = lean_box(0);
v___x_181_ = 0;
lean_inc(v_stx_176_);
v___x_182_ = l_Lean_Syntax_formatStx(v_stx_176_, v___x_180_, v___x_181_);
v___x_183_ = l_Std_Format_defWidth;
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = l_Std_Format_pretty(v___x_182_, v___x_183_, v___x_184_, v___x_184_);
v___x_186_ = lean_string_append(v___x_179_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = lean_dbg_trace(v___x_186_, v___f_178_);
v___x_188_ = lean_unbox(v___x_187_);
lean_dec(v___x_187_);
v___y_164_ = v___x_188_;
goto v___jp_163_;
}
}
else
{
lean_dec(v_val_174_);
goto v___jp_166_;
}
}
}
}
else
{
uint8_t v___x_189_; 
v___x_189_ = lean_bool_not(v_cond_128_);
v___y_164_ = v___x_189_;
goto v___jp_163_;
}
}
v___jp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_inc_ref(v_fixedTermElabs_158_);
lean_inc(v_sectionFVars_147_);
lean_inc(v_sectionVars_146_);
lean_inc_ref(v_autoBoundImplicitForbidden_145_);
lean_inc(v_autoBoundImplicitContext_144_);
lean_inc(v_macroStack_141_);
lean_inc(v_declName_x3f_140_);
v___x_161_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_161_, 0, v_declName_x3f_140_);
lean_ctor_set(v___x_161_, 1, v_macroStack_141_);
lean_ctor_set(v___x_161_, 2, v_autoBoundImplicitContext_144_);
lean_ctor_set(v___x_161_, 3, v_autoBoundImplicitForbidden_145_);
lean_ctor_set(v___x_161_, 4, v_sectionVars_146_);
lean_ctor_set(v___x_161_, 5, v_sectionFVars_147_);
lean_ctor_set(v___x_161_, 6, v___y_160_);
lean_ctor_set(v___x_161_, 7, v_fixedTermElabs_158_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8, v_mayPostpone_142_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 1, v_errToSorry_143_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 2, v_implicitLambda_148_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 3, v_heedElabAsElim_149_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 4, v_isNoncomputableSection_150_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 5, v_isMetaSection_151_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 6, v_ignoreTCFailures_152_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 7, v_inPattern_153_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_155_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_156_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*8 + 10, v_checkDeprecated_157_);
lean_inc(v___y_137_);
lean_inc_ref(v___y_136_);
lean_inc(v___y_135_);
lean_inc_ref(v___y_134_);
lean_inc(v___y_133_);
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
v___x_162_ = lean_apply_9(v_act_129_, v___y_130_, v___y_131_, v___x_161_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, lean_box(0));
return v___x_162_;
}
v___jp_163_:
{
if (v___y_164_ == 0)
{
lean_object* v___x_165_; 
v___x_165_ = lean_box(0);
v___y_160_ = v___x_165_;
goto v___jp_159_;
}
else
{
lean_inc(v_tacSnap_x3f_154_);
v___y_160_ = v_tacSnap_x3f_154_;
goto v___jp_159_;
}
}
v___jp_166_:
{
uint8_t v___x_167_; 
v___x_167_ = lean_bool_not(v_cond_128_);
v___y_164_ = v___x_167_;
goto v___jp_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___boxed(lean_object* v_cond_190_, lean_object* v_act_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
uint8_t v_cond_boxed_201_; lean_object* v_res_202_; 
v_cond_boxed_201_ = lean_unbox(v_cond_190_);
v_res_202_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_boxed_201_, v_act_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(lean_object* v_00_u03b1_203_, uint8_t v_cond_204_, lean_object* v_act_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_204_, v_act_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___boxed(lean_object* v_00_u03b1_216_, lean_object* v_cond_217_, lean_object* v_act_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
uint8_t v_cond_boxed_228_; lean_object* v_res_229_; 
v_cond_boxed_228_ = lean_unbox(v_cond_217_);
v_res_229_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(v_00_u03b1_216_, v_cond_boxed_228_, v_act_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(lean_object* v_k_230_, uint8_t v_mayPostpone_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_230_, v_mayPostpone_231_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed(lean_object* v_k_242_, lean_object* v_mayPostpone_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
uint8_t v_mayPostpone_boxed_253_; lean_object* v_res_254_; 
v_mayPostpone_boxed_253_ = lean_unbox(v_mayPostpone_243_);
v_res_254_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(v_k_242_, v_mayPostpone_boxed_253_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(lean_object* v___f_255_, lean_object* v_k_256_, uint8_t v_mayPostpone_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
uint8_t v_recover_267_; 
v_recover_267_ = lean_ctor_get_uint8(v___y_258_, sizeof(void*)*1);
if (v_recover_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec_ref(v_k_256_);
v___x_268_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(v___f_255_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; 
lean_dec_ref(v___f_255_);
v___x_269_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_256_, v_mayPostpone_257_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed(lean_object* v___f_270_, lean_object* v_k_271_, lean_object* v_mayPostpone_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
uint8_t v_mayPostpone_boxed_282_; lean_object* v_res_283_; 
v_mayPostpone_boxed_282_ = lean_unbox(v_mayPostpone_272_);
v_res_283_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(v___f_270_, v_k_271_, v_mayPostpone_boxed_282_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object* v_k_284_, uint8_t v_mayPostpone_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___f_298_; uint8_t v___x_299_; lean_object* v___x_300_; 
v___x_295_ = lean_box(v_mayPostpone_285_);
lean_inc_ref(v_k_284_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_296_, 0, v_k_284_);
lean_closure_set(v___f_296_, 1, v___x_295_);
v___x_297_ = lean_box(v_mayPostpone_285_);
v___f_298_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_298_, 0, v___f_296_);
lean_closure_set(v___f_298_, 1, v_k_284_);
lean_closure_set(v___f_298_, 2, v___x_297_);
v___x_299_ = 1;
v___x_300_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v___x_299_, v___f_298_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___boxed(lean_object* v_k_301_, lean_object* v_mayPostpone_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
uint8_t v_mayPostpone_boxed_312_; lean_object* v_res_313_; 
v_mayPostpone_boxed_312_ = lean_unbox(v_mayPostpone_302_);
v_res_313_ = l_Lean_Elab_Tactic_runTermElab___redArg(v_k_301_, v_mayPostpone_boxed_312_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object* v_00_u03b1_314_, lean_object* v_k_315_, uint8_t v_mayPostpone_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Elab_Tactic_runTermElab___redArg(v_k_315_, v_mayPostpone_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object* v_00_u03b1_327_, lean_object* v_k_328_, lean_object* v_mayPostpone_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
uint8_t v_mayPostpone_boxed_339_; lean_object* v_res_340_; 
v_mayPostpone_boxed_339_ = lean_unbox(v_mayPostpone_329_);
v_res_340_ = l_Lean_Elab_Tactic_runTermElab(v_00_u03b1_327_, v_k_328_, v_mayPostpone_boxed_339_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(lean_object* v_e_341_, lean_object* v___y_342_){
_start:
{
uint8_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = l_Lean_Expr_hasMVar(v_e_341_);
v___x_345_ = lean_bool_not(v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v_mctx_347_; lean_object* v___x_348_; lean_object* v_fst_349_; lean_object* v_snd_350_; lean_object* v___x_351_; lean_object* v_cache_352_; lean_object* v_zetaDeltaFVarIds_353_; lean_object* v_postponed_354_; lean_object* v_diag_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_364_; 
v___x_346_ = lean_st_ref_get(v___y_342_);
v_mctx_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_mctx_347_);
lean_dec(v___x_346_);
v___x_348_ = l_Lean_instantiateMVarsCore(v_mctx_347_, v_e_341_);
v_fst_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_fst_349_);
v_snd_350_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_snd_350_);
lean_dec_ref(v___x_348_);
v___x_351_ = lean_st_ref_take(v___y_342_);
v_cache_352_ = lean_ctor_get(v___x_351_, 1);
v_zetaDeltaFVarIds_353_ = lean_ctor_get(v___x_351_, 2);
v_postponed_354_ = lean_ctor_get(v___x_351_, 3);
v_diag_355_ = lean_ctor_get(v___x_351_, 4);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_351_, 0);
lean_dec(v_unused_365_);
v___x_357_ = v___x_351_;
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_diag_355_);
lean_inc(v_postponed_354_);
lean_inc(v_zetaDeltaFVarIds_353_);
lean_inc(v_cache_352_);
lean_dec(v___x_351_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v_snd_350_);
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_snd_350_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_cache_352_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_zetaDeltaFVarIds_353_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v_postponed_354_);
lean_ctor_set(v_reuseFailAlloc_363_, 4, v_diag_355_);
v___x_360_ = v_reuseFailAlloc_363_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_st_ref_set(v___y_342_, v___x_360_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v_fst_349_);
return v___x_362_;
}
}
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_e_341_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg___boxed(lean_object* v_e_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_e_367_, v___y_368_);
lean_dec(v___y_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(lean_object* v_e_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_e_371_, v___y_377_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___boxed(lean_object* v_e_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(v_e_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object* v_stx_393_, lean_object* v_expectedType_x3f_394_, uint8_t v_mayPostpone_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_fileName_409_; lean_object* v_fileMap_410_; lean_object* v_options_411_; lean_object* v_currRecDepth_412_; lean_object* v_maxRecDepth_413_; lean_object* v_ref_414_; lean_object* v_currNamespace_415_; lean_object* v_openDecls_416_; lean_object* v_initHeartbeats_417_; lean_object* v_maxHeartbeats_418_; lean_object* v_quotContext_419_; lean_object* v_currMacroScope_420_; uint8_t v_diag_421_; lean_object* v_cancelTk_x3f_422_; uint8_t v_suppressElabErrors_423_; lean_object* v_inheritedTraceOptions_424_; lean_object* v_ref_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_405_ = 1;
v___x_406_ = lean_box(v___x_405_);
v___x_407_ = lean_box(v___x_405_);
lean_inc(v_stx_393_);
v___x_408_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_408_, 0, v_stx_393_);
lean_closure_set(v___x_408_, 1, v_expectedType_x3f_394_);
lean_closure_set(v___x_408_, 2, v___x_406_);
lean_closure_set(v___x_408_, 3, v___x_407_);
v_fileName_409_ = lean_ctor_get(v_a_402_, 0);
v_fileMap_410_ = lean_ctor_get(v_a_402_, 1);
v_options_411_ = lean_ctor_get(v_a_402_, 2);
v_currRecDepth_412_ = lean_ctor_get(v_a_402_, 3);
v_maxRecDepth_413_ = lean_ctor_get(v_a_402_, 4);
v_ref_414_ = lean_ctor_get(v_a_402_, 5);
v_currNamespace_415_ = lean_ctor_get(v_a_402_, 6);
v_openDecls_416_ = lean_ctor_get(v_a_402_, 7);
v_initHeartbeats_417_ = lean_ctor_get(v_a_402_, 8);
v_maxHeartbeats_418_ = lean_ctor_get(v_a_402_, 9);
v_quotContext_419_ = lean_ctor_get(v_a_402_, 10);
v_currMacroScope_420_ = lean_ctor_get(v_a_402_, 11);
v_diag_421_ = lean_ctor_get_uint8(v_a_402_, sizeof(void*)*14);
v_cancelTk_x3f_422_ = lean_ctor_get(v_a_402_, 12);
v_suppressElabErrors_423_ = lean_ctor_get_uint8(v_a_402_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_424_ = lean_ctor_get(v_a_402_, 13);
v_ref_425_ = l_Lean_replaceRef(v_stx_393_, v_ref_414_);
lean_dec(v_stx_393_);
lean_inc_ref(v_inheritedTraceOptions_424_);
lean_inc(v_cancelTk_x3f_422_);
lean_inc(v_currMacroScope_420_);
lean_inc(v_quotContext_419_);
lean_inc(v_maxHeartbeats_418_);
lean_inc(v_initHeartbeats_417_);
lean_inc(v_openDecls_416_);
lean_inc(v_currNamespace_415_);
lean_inc(v_maxRecDepth_413_);
lean_inc(v_currRecDepth_412_);
lean_inc_ref(v_options_411_);
lean_inc_ref(v_fileMap_410_);
lean_inc_ref(v_fileName_409_);
v___x_426_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_426_, 0, v_fileName_409_);
lean_ctor_set(v___x_426_, 1, v_fileMap_410_);
lean_ctor_set(v___x_426_, 2, v_options_411_);
lean_ctor_set(v___x_426_, 3, v_currRecDepth_412_);
lean_ctor_set(v___x_426_, 4, v_maxRecDepth_413_);
lean_ctor_set(v___x_426_, 5, v_ref_425_);
lean_ctor_set(v___x_426_, 6, v_currNamespace_415_);
lean_ctor_set(v___x_426_, 7, v_openDecls_416_);
lean_ctor_set(v___x_426_, 8, v_initHeartbeats_417_);
lean_ctor_set(v___x_426_, 9, v_maxHeartbeats_418_);
lean_ctor_set(v___x_426_, 10, v_quotContext_419_);
lean_ctor_set(v___x_426_, 11, v_currMacroScope_420_);
lean_ctor_set(v___x_426_, 12, v_cancelTk_x3f_422_);
lean_ctor_set(v___x_426_, 13, v_inheritedTraceOptions_424_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*14, v_diag_421_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*14 + 1, v_suppressElabErrors_423_);
v___x_427_ = l_Lean_Elab_Tactic_runTermElab___redArg(v___x_408_, v_mayPostpone_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v___x_426_, v_a_403_);
lean_dec_ref_known(v___x_426_, 14);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_428_, v_a_401_);
return v___x_429_;
}
else
{
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object* v_stx_430_, lean_object* v_expectedType_x3f_431_, lean_object* v_mayPostpone_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
uint8_t v_mayPostpone_boxed_442_; lean_object* v_res_443_; 
v_mayPostpone_boxed_442_ = lean_unbox(v_mayPostpone_432_);
v_res_443_ = l_Lean_Elab_Tactic_elabTerm(v_stx_430_, v_expectedType_x3f_431_, v_mayPostpone_boxed_442_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object* v_stx_444_, lean_object* v_expectedType_x3f_445_, uint8_t v_mayPostpone_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_456_; 
lean_inc(v_expectedType_x3f_445_);
v___x_456_ = l_Lean_Elab_Tactic_elabTerm(v_stx_444_, v_expectedType_x3f_445_, v_mayPostpone_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
if (lean_obj_tag(v___x_456_) == 0)
{
if (lean_obj_tag(v_expectedType_x3f_445_) == 0)
{
return v___x_456_;
}
else
{
lean_object* v_a_457_; lean_object* v_val_458_; lean_object* v___x_459_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc_n(v_a_457_, 2);
lean_dec_ref_known(v___x_456_, 1);
v_val_458_ = lean_ctor_get(v_expectedType_x3f_445_, 0);
lean_inc(v_val_458_);
lean_dec_ref_known(v_expectedType_x3f_445_, 1);
lean_inc(v_a_454_);
lean_inc_ref(v_a_453_);
lean_inc(v_a_452_);
lean_inc_ref(v_a_451_);
v___x_459_ = lean_infer_type(v_a_457_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_540_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_540_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_540_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_540_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
uint8_t v_a_465_; lean_object* v___x_487_; uint8_t v_foApprox_488_; uint8_t v_ctxApprox_489_; uint8_t v_quasiPatternApprox_490_; uint8_t v_constApprox_491_; uint8_t v_isDefEqStuckEx_492_; uint8_t v_unificationHints_493_; uint8_t v_proofIrrelevance_494_; uint8_t v_offsetCnstrs_495_; uint8_t v_transparency_496_; uint8_t v_etaStruct_497_; uint8_t v_univApprox_498_; uint8_t v_iota_499_; uint8_t v_beta_500_; uint8_t v_proj_501_; uint8_t v_zeta_502_; uint8_t v_zetaDelta_503_; uint8_t v_zetaUnused_504_; uint8_t v_zetaHave_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_539_; 
v___x_487_ = l_Lean_Meta_Context_config(v_a_451_);
v_foApprox_488_ = lean_ctor_get_uint8(v___x_487_, 0);
v_ctxApprox_489_ = lean_ctor_get_uint8(v___x_487_, 1);
v_quasiPatternApprox_490_ = lean_ctor_get_uint8(v___x_487_, 2);
v_constApprox_491_ = lean_ctor_get_uint8(v___x_487_, 3);
v_isDefEqStuckEx_492_ = lean_ctor_get_uint8(v___x_487_, 4);
v_unificationHints_493_ = lean_ctor_get_uint8(v___x_487_, 5);
v_proofIrrelevance_494_ = lean_ctor_get_uint8(v___x_487_, 6);
v_offsetCnstrs_495_ = lean_ctor_get_uint8(v___x_487_, 8);
v_transparency_496_ = lean_ctor_get_uint8(v___x_487_, 9);
v_etaStruct_497_ = lean_ctor_get_uint8(v___x_487_, 10);
v_univApprox_498_ = lean_ctor_get_uint8(v___x_487_, 11);
v_iota_499_ = lean_ctor_get_uint8(v___x_487_, 12);
v_beta_500_ = lean_ctor_get_uint8(v___x_487_, 13);
v_proj_501_ = lean_ctor_get_uint8(v___x_487_, 14);
v_zeta_502_ = lean_ctor_get_uint8(v___x_487_, 15);
v_zetaDelta_503_ = lean_ctor_get_uint8(v___x_487_, 16);
v_zetaUnused_504_ = lean_ctor_get_uint8(v___x_487_, 17);
v_zetaHave_505_ = lean_ctor_get_uint8(v___x_487_, 18);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_539_ == 0)
{
v___x_507_ = v___x_487_;
v_isShared_508_ = v_isSharedCheck_539_;
goto v_resetjp_506_;
}
else
{
lean_dec(v___x_487_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_539_;
goto v_resetjp_506_;
}
v___jp_464_:
{
if (v_a_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_del_object(v___x_462_);
v___x_466_ = lean_box(0);
lean_inc(v_a_457_);
v___x_467_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_466_, v_val_458_, v_a_460_, v_a_457_, v___x_466_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v___x_467_, 0);
lean_dec(v_unused_475_);
v___x_469_ = v___x_467_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_dec(v___x_467_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v_a_457_);
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_457_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_a_457_);
v_a_476_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_467_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_467_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v___x_485_; 
lean_dec(v_a_460_);
lean_dec(v_val_458_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v_a_457_);
v___x_485_ = v___x_462_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_457_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
v_resetjp_506_:
{
uint8_t v_trackZetaDelta_509_; lean_object* v_zetaDeltaSet_510_; lean_object* v_lctx_511_; lean_object* v_localInstances_512_; lean_object* v_defEqCtx_x3f_513_; lean_object* v_synthPendingDepth_514_; lean_object* v_canUnfold_x3f_515_; uint8_t v_univApprox_516_; uint8_t v_inTypeClassResolution_517_; uint8_t v_cacheInferType_518_; uint8_t v___x_519_; lean_object* v___x_521_; 
v_trackZetaDelta_509_ = lean_ctor_get_uint8(v_a_451_, sizeof(void*)*7);
v_zetaDeltaSet_510_ = lean_ctor_get(v_a_451_, 1);
v_lctx_511_ = lean_ctor_get(v_a_451_, 2);
v_localInstances_512_ = lean_ctor_get(v_a_451_, 3);
v_defEqCtx_x3f_513_ = lean_ctor_get(v_a_451_, 4);
v_synthPendingDepth_514_ = lean_ctor_get(v_a_451_, 5);
v_canUnfold_x3f_515_ = lean_ctor_get(v_a_451_, 6);
v_univApprox_516_ = lean_ctor_get_uint8(v_a_451_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_517_ = lean_ctor_get_uint8(v_a_451_, sizeof(void*)*7 + 2);
v_cacheInferType_518_ = lean_ctor_get_uint8(v_a_451_, sizeof(void*)*7 + 3);
v___x_519_ = 1;
if (v_isShared_508_ == 0)
{
v___x_521_ = v___x_507_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 0, v_foApprox_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 1, v_ctxApprox_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 2, v_quasiPatternApprox_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 3, v_constApprox_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 4, v_isDefEqStuckEx_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 5, v_unificationHints_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 6, v_proofIrrelevance_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 8, v_offsetCnstrs_495_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 9, v_transparency_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 10, v_etaStruct_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 11, v_univApprox_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 12, v_iota_499_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 13, v_beta_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 14, v_proj_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 15, v_zeta_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 16, v_zetaDelta_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 17, v_zetaUnused_504_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, 18, v_zetaHave_505_);
v___x_521_ = v_reuseFailAlloc_538_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
uint64_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
lean_ctor_set_uint8(v___x_521_, 7, v___x_519_);
v___x_522_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set_uint64(v___x_523_, sizeof(void*)*1, v___x_522_);
lean_inc(v_canUnfold_x3f_515_);
lean_inc(v_synthPendingDepth_514_);
lean_inc(v_defEqCtx_x3f_513_);
lean_inc_ref(v_localInstances_512_);
lean_inc_ref(v_lctx_511_);
lean_inc(v_zetaDeltaSet_510_);
v___x_524_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v_zetaDeltaSet_510_);
lean_ctor_set(v___x_524_, 2, v_lctx_511_);
lean_ctor_set(v___x_524_, 3, v_localInstances_512_);
lean_ctor_set(v___x_524_, 4, v_defEqCtx_x3f_513_);
lean_ctor_set(v___x_524_, 5, v_synthPendingDepth_514_);
lean_ctor_set(v___x_524_, 6, v_canUnfold_x3f_515_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*7, v_trackZetaDelta_509_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*7 + 1, v_univApprox_516_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*7 + 2, v_inTypeClassResolution_517_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*7 + 3, v_cacheInferType_518_);
lean_inc(v_val_458_);
lean_inc(v_a_460_);
v___x_525_ = l_Lean_Meta_isExprDefEq(v_a_460_, v_val_458_, v___x_524_, v_a_452_, v_a_453_, v_a_454_);
lean_dec_ref_known(v___x_524_, 7);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; uint8_t v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = lean_unbox(v_a_526_);
lean_dec(v_a_526_);
v_a_465_ = v___x_527_;
goto v___jp_464_;
}
else
{
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_528_; uint8_t v___x_529_; 
v_a_528_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_525_, 1);
v___x_529_ = lean_unbox(v_a_528_);
lean_dec(v_a_528_);
v_a_465_ = v___x_529_;
goto v___jp_464_;
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_del_object(v___x_462_);
lean_dec(v_a_460_);
lean_dec(v_val_458_);
lean_dec(v_a_457_);
v_a_530_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_525_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_525_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_val_458_);
lean_dec(v_a_457_);
return v___x_459_;
}
}
}
else
{
lean_dec(v_expectedType_x3f_445_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object* v_stx_541_, lean_object* v_expectedType_x3f_542_, lean_object* v_mayPostpone_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
uint8_t v_mayPostpone_boxed_553_; lean_object* v_res_554_; 
v_mayPostpone_boxed_553_ = lean_unbox(v_mayPostpone_543_);
v_res_554_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v_stx_541_, v_expectedType_x3f_542_, v_mayPostpone_boxed_553_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_554_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_box(0);
v___x_556_ = l_Lean_Elab_abortTacticExceptionId;
v___x_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___x_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___boxed(lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(lean_object* v_00_u03b1_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(lean_object* v_00_u03b1_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(v_00_u03b1_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object* v_mvarIds_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_box(0);
v___x_596_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_mvarIds_585_, v___x_595_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_607_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_607_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_607_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint8_t v___x_601_; 
v___x_601_ = lean_unbox(v_a_597_);
lean_dec(v_a_597_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_602_);
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
else
{
lean_object* v___x_606_; 
lean_del_object(v___x_599_);
v___x_606_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_606_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_596_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_596_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object* v_mvarIds_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_mvarIds_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec_ref(v_mvarIds_616_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(lean_object* v___x_627_, lean_object* v_mvarCounterSaved_628_, lean_object* v_as_629_, size_t v_i_630_, size_t v_stop_631_, lean_object* v_b_632_){
_start:
{
lean_object* v___y_634_; uint8_t v___x_638_; 
v___x_638_ = lean_usize_dec_eq(v_i_630_, v_stop_631_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_index_641_; uint8_t v___x_642_; 
v___x_639_ = lean_array_uget_borrowed(v_as_629_, v_i_630_);
lean_inc(v___x_639_);
v___x_640_ = l_Lean_MetavarContext_getDecl(v___x_627_, v___x_639_);
v_index_641_ = lean_ctor_get(v___x_640_, 6);
lean_inc(v_index_641_);
lean_dec_ref(v___x_640_);
v___x_642_ = lean_nat_dec_le(v_mvarCounterSaved_628_, v_index_641_);
lean_dec(v_index_641_);
if (v___x_642_ == 0)
{
v___y_634_ = v_b_632_;
goto v___jp_633_;
}
else
{
lean_object* v___x_643_; 
lean_inc(v___x_639_);
v___x_643_ = lean_array_push(v_b_632_, v___x_639_);
v___y_634_ = v___x_643_;
goto v___jp_633_;
}
}
else
{
return v_b_632_;
}
v___jp_633_:
{
size_t v___x_635_; size_t v___x_636_; 
v___x_635_ = ((size_t)1ULL);
v___x_636_ = lean_usize_add(v_i_630_, v___x_635_);
v_i_630_ = v___x_636_;
v_b_632_ = v___y_634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(lean_object* v___x_644_, lean_object* v_mvarCounterSaved_645_, lean_object* v_as_646_, lean_object* v_i_647_, lean_object* v_stop_648_, lean_object* v_b_649_){
_start:
{
size_t v_i_boxed_650_; size_t v_stop_boxed_651_; lean_object* v_res_652_; 
v_i_boxed_650_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_stop_boxed_651_ = lean_unbox_usize(v_stop_648_);
lean_dec(v_stop_648_);
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v___x_644_, v_mvarCounterSaved_645_, v_as_646_, v_i_boxed_650_, v_stop_boxed_651_, v_b_649_);
lean_dec_ref(v_as_646_);
lean_dec(v_mvarCounterSaved_645_);
lean_dec_ref(v___x_644_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object* v_mvarIds_655_, lean_object* v_mvarCounterSaved_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_659_ = lean_st_ref_get(v_a_657_);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_array_get_size(v_mvarIds_655_);
v___x_662_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_663_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec(v___x_659_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
return v___x_664_;
}
else
{
lean_object* v_mctx_665_; uint8_t v___x_666_; 
v_mctx_665_ = lean_ctor_get(v___x_659_, 0);
lean_inc_ref(v_mctx_665_);
lean_dec(v___x_659_);
v___x_666_ = lean_nat_dec_le(v___x_661_, v___x_661_);
if (v___x_666_ == 0)
{
if (v___x_663_ == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v_mctx_665_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_662_);
return v___x_667_;
}
else
{
size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = ((size_t)0ULL);
v___x_669_ = lean_usize_of_nat(v___x_661_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_665_, v_mvarCounterSaved_656_, v_mvarIds_655_, v___x_668_, v___x_669_, v___x_662_);
lean_dec_ref(v_mctx_665_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
else
{
size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_672_ = ((size_t)0ULL);
v___x_673_ = lean_usize_of_nat(v___x_661_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_665_, v_mvarCounterSaved_656_, v_mvarIds_655_, v___x_672_, v___x_673_, v___x_662_);
lean_dec_ref(v_mctx_665_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(lean_object* v_mvarIds_676_, lean_object* v_mvarCounterSaved_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_676_, v_mvarCounterSaved_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec(v_mvarCounterSaved_677_);
lean_dec_ref(v_mvarIds_676_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object* v_mvarIds_681_, lean_object* v_mvarCounterSaved_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_681_, v_mvarCounterSaved_682_, v_a_684_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object* v_mvarIds_689_, lean_object* v_mvarCounterSaved_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Elab_Tactic_filterOldMVars(v_mvarIds_689_, v_mvarCounterSaved_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_mvarCounterSaved_690_);
lean_dec_ref(v_mvarIds_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(lean_object* v_x_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; 
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v___x_707_ = lean_apply_9(v_x_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, lean_box(0));
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed(lean_object* v_x_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(v_x_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(lean_object* v_mvarId_719_, lean_object* v_x_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___f_730_; lean_object* v___x_731_; 
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
v___f_730_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_730_, 0, v_x_720_);
lean_closure_set(v___f_730_, 1, v___y_721_);
lean_closure_set(v___f_730_, 2, v___y_722_);
lean_closure_set(v___f_730_, 3, v___y_723_);
lean_closure_set(v___f_730_, 4, v___y_724_);
v___x_731_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_719_, v___f_730_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_731_) == 0)
{
return v___x_731_;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___boxed(lean_object* v_mvarId_740_, lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_740_, v_x_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(lean_object* v_00_u03b1_752_, lean_object* v_mvarId_753_, lean_object* v_x_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_753_, v_x_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___boxed(lean_object* v_00_u03b1_765_, lean_object* v_mvarId_766_, lean_object* v_x_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(v_00_u03b1_765_, v_mvarId_766_, v_x_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_777_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0));
v___x_780_ = l_Lean_stringToMessageData(v___x_779_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2));
v___x_783_ = l_Lean_stringToMessageData(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(lean_object* v_a_784_, lean_object* v_x_785_, lean_object* v_tacName_786_, uint8_t v_checkNewUnassigned_787_, lean_object* v_mvarCounter_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; 
lean_inc(v_a_784_);
v___x_798_ = l_Lean_MVarId_getType(v_a_784_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
lean_inc(v_a_784_);
v___x_800_ = l_Lean_MVarId_getTag(v_a_784_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
lean_inc(v___y_796_);
lean_inc_ref(v___y_795_);
lean_inc(v___y_794_);
lean_inc_ref(v___y_793_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
v___x_802_ = lean_apply_11(v_x_785_, v_a_799_, v_a_801_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, lean_box(0));
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
if (v_checkNewUnassigned_787_ == 0)
{
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
v___y_805_ = v___y_793_;
v___y_806_ = v___y_794_;
v___y_807_ = v___y_795_;
v___y_808_ = v___y_796_;
goto v___jp_804_;
}
else
{
lean_object* v___x_835_; 
lean_inc(v_a_803_);
v___x_835_ = l_Lean_Meta_getMVars(v_a_803_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_837_; lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
v___x_837_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_836_, v_mvarCounter_788_, v___y_794_);
lean_dec(v_a_836_);
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
v___x_839_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_838_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v_a_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_dec_ref_known(v___x_839_, 1);
v___y_805_ = v___y_793_;
v___y_806_ = v___y_794_;
v___y_807_ = v___y_795_;
v___y_808_ = v___y_796_;
goto v___jp_804_;
}
else
{
lean_dec(v_a_803_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v_tacName_786_);
lean_dec(v_a_784_);
return v___x_839_;
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_a_803_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v_tacName_786_);
lean_dec(v_a_784_);
v_a_840_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_835_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_835_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
v___jp_804_:
{
lean_object* v___x_809_; 
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
lean_inc_ref(v___y_805_);
lean_inc(v_a_803_);
lean_inc(v_a_784_);
v___x_809_ = lean_checked_assign(v_a_784_, v_a_803_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_826_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_826_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_826_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_826_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
uint8_t v___x_814_; 
v___x_814_ = lean_unbox(v_a_810_);
lean_dec(v_a_810_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_del_object(v___x_812_);
v___x_815_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1);
v___x_816_ = l_Lean_indentExpr(v_a_803_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
v___x_821_ = l_Lean_Meta_throwTacticEx___redArg(v_tacName_786_, v_a_784_, v___x_820_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v_a_803_);
lean_dec(v_tacName_786_);
lean_dec(v_a_784_);
v___x_822_ = lean_box(0);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_822_);
v___x_824_ = v___x_812_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v_a_803_);
lean_dec(v_tacName_786_);
lean_dec(v_a_784_);
v_a_827_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_809_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_809_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v_tacName_786_);
lean_dec(v_a_784_);
v_a_848_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_802_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_802_);
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
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_a_799_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v_tacName_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_a_784_);
v_a_856_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_800_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_800_);
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
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v_tacName_786_);
lean_dec_ref(v_x_785_);
lean_dec(v_a_784_);
v_a_864_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_798_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_798_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(lean_object* v_a_872_, lean_object* v_x_873_, lean_object* v_tacName_874_, lean_object* v_checkNewUnassigned_875_, lean_object* v_mvarCounter_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_886_; lean_object* v_res_887_; 
v_checkNewUnassigned_boxed_886_ = lean_unbox(v_checkNewUnassigned_875_);
v_res_887_ = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(v_a_872_, v_x_873_, v_tacName_874_, v_checkNewUnassigned_boxed_886_, v_mvarCounter_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v_mvarCounter_876_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object* v_tacName_888_, lean_object* v_x_889_, uint8_t v_checkNewUnassigned_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_st_ref_get(v_a_896_);
v___x_901_ = l_Lean_Elab_Tactic_popMainGoal___redArg(v_a_892_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_mctx_902_; lean_object* v_a_903_; lean_object* v_mvarCounter_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___x_907_; 
v_mctx_902_ = lean_ctor_get(v___x_900_, 0);
lean_inc_ref(v_mctx_902_);
lean_dec(v___x_900_);
v_a_903_ = lean_ctor_get(v___x_901_, 0);
lean_inc_n(v_a_903_, 3);
lean_dec_ref_known(v___x_901_, 1);
v_mvarCounter_904_ = lean_ctor_get(v_mctx_902_, 3);
lean_inc(v_mvarCounter_904_);
lean_dec_ref(v_mctx_902_);
v___x_905_ = lean_box(v_checkNewUnassigned_890_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed), 14, 5);
lean_closure_set(v___f_906_, 0, v_a_903_);
lean_closure_set(v___f_906_, 1, v_x_889_);
lean_closure_set(v___f_906_, 2, v_tacName_888_);
lean_closure_set(v___f_906_, 3, v___x_905_);
lean_closure_set(v___f_906_, 4, v_mvarCounter_904_);
v___x_907_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_a_903_, v___f_906_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_dec(v_a_903_);
return v___x_907_;
}
else
{
lean_object* v_a_908_; uint8_t v___y_910_; uint8_t v___x_920_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
v___x_920_ = l_Lean_Exception_isInterrupt(v_a_908_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; 
lean_inc(v_a_908_);
v___x_921_ = l_Lean_Exception_isRuntime(v_a_908_);
v___y_910_ = v___x_921_;
goto v___jp_909_;
}
else
{
v___y_910_ = v___x_920_;
goto v___jp_909_;
}
v___jp_909_:
{
if (v___y_910_ == 0)
{
lean_object* v___x_911_; 
lean_dec_ref_known(v___x_907_, 1);
v___x_911_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_903_, v_a_892_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___x_911_, 0);
lean_dec(v_unused_919_);
v___x_913_ = v___x_911_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_dec(v___x_911_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 1);
lean_ctor_set(v___x_913_, 0, v_a_908_);
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_908_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
lean_dec(v_a_908_);
return v___x_911_;
}
}
else
{
lean_dec(v_a_908_);
lean_dec(v_a_903_);
return v___x_907_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v___x_900_);
lean_dec_ref(v_x_889_);
lean_dec(v_tacName_888_);
v_a_922_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_901_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_901_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object* v_tacName_930_, lean_object* v_x_931_, lean_object* v_checkNewUnassigned_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_942_; lean_object* v_res_943_; 
v_checkNewUnassigned_boxed_942_ = lean_unbox(v_checkNewUnassigned_932_);
v_res_943_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacName_930_, v_x_931_, v_checkNewUnassigned_boxed_942_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_box(0);
v___x_945_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___boxed(lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(lean_object* v_00_u03b1_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___boxed(lean_object* v_00_u03b1_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(v_00_u03b1_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0(lean_object* v___x_974_, lean_object* v_type_975_, lean_object* v_x_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; uint8_t v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_type_975_);
v___x_987_ = 0;
v___x_988_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_974_, v___x_986_, v___x_987_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0___boxed(lean_object* v___x_989_, lean_object* v_type_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Elab_Tactic_evalExact___lam__0(v___x_989_, v_type_990_, v_x_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v_x_991_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object* v_stx_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
lean_inc(v_stx_1013_);
v___x_1024_ = l_Lean_Syntax_isOfKind(v_stx_1013_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec(v_stx_1013_);
v___x_1025_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = l_Lean_Syntax_getArg(v_stx_1013_, v___x_1026_);
lean_dec(v_stx_1013_);
v___f_1028_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__5));
v___x_1030_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v___x_1029_, v___f_1028_, v___x_1024_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___boxed(lean_object* v_stx_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Elab_Tactic_evalExact(v_stx_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1(){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1049_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
v___x_1051_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1052_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___boxed), 10, 0);
v___x_1053_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1049_, v___x_1050_, v___x_1051_, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___boxed(lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6));
v___x_1084_ = l_Lean_addBuiltinDeclarationRanges(v___x_1082_, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___boxed(lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
return v_res_1086_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(lean_object* v_mctx_1087_, lean_object* v_mvarId_u2081_1088_, lean_object* v_mvarId_u2082_1089_){
_start:
{
lean_object* v_decl_u2081_1090_; lean_object* v_index_1091_; lean_object* v_decl_u2082_1092_; lean_object* v_index_1093_; uint8_t v___x_1094_; uint8_t v___x_1095_; 
lean_inc(v_mvarId_u2081_1088_);
v_decl_u2081_1090_ = l_Lean_MetavarContext_getDecl(v_mctx_1087_, v_mvarId_u2081_1088_);
v_index_1091_ = lean_ctor_get(v_decl_u2081_1090_, 6);
lean_inc(v_index_1091_);
lean_dec_ref(v_decl_u2081_1090_);
lean_inc(v_mvarId_u2082_1089_);
v_decl_u2082_1092_ = l_Lean_MetavarContext_getDecl(v_mctx_1087_, v_mvarId_u2082_1089_);
v_index_1093_ = lean_ctor_get(v_decl_u2082_1092_, 6);
lean_inc(v_index_1093_);
lean_dec_ref(v_decl_u2082_1092_);
v___x_1094_ = lean_nat_dec_eq(v_index_1091_, v_index_1093_);
v___x_1095_ = lean_bool_not(v___x_1094_);
if (v___x_1095_ == 0)
{
uint8_t v___x_1096_; 
lean_dec(v_index_1093_);
lean_dec(v_index_1091_);
v___x_1096_ = l_Lean_Name_quickLt(v_mvarId_u2081_1088_, v_mvarId_u2082_1089_);
lean_dec(v_mvarId_u2082_1089_);
lean_dec(v_mvarId_u2081_1088_);
return v___x_1096_;
}
else
{
uint8_t v___x_1097_; 
lean_dec(v_mvarId_u2082_1089_);
lean_dec(v_mvarId_u2081_1088_);
v___x_1097_ = lean_nat_dec_lt(v_index_1091_, v_index_1093_);
lean_dec(v_index_1093_);
lean_dec(v_index_1091_);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(lean_object* v_mctx_1098_, lean_object* v_mvarId_u2081_1099_, lean_object* v_mvarId_u2082_1100_){
_start:
{
uint8_t v_res_1101_; lean_object* v_r_1102_; 
v_res_1101_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(v_mctx_1098_, v_mvarId_u2081_1099_, v_mvarId_u2082_1100_);
lean_dec_ref(v_mctx_1098_);
v_r_1102_ = lean_box(v_res_1101_);
return v_r_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(lean_object* v_mvarIds_1103_, lean_object* v_toPure_1104_, lean_object* v_mctx_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_array_get_size(v_mvarIds_1103_);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_nat_dec_eq(v___x_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___f_1109_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___y_1118_; uint8_t v___x_1120_; 
v___f_1109_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1109_, 0, v_mctx_1105_);
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_sub(v___x_1106_, v___x_1115_);
v___x_1120_ = lean_nat_dec_le(v___x_1107_, v___x_1116_);
if (v___x_1120_ == 0)
{
lean_inc(v___x_1116_);
v___y_1118_ = v___x_1116_;
goto v___jp_1117_;
}
else
{
v___y_1118_ = v___x_1107_;
goto v___jp_1117_;
}
v___jp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_1109_, v___x_1106_, v_mvarIds_1103_, v___y_1111_, v___y_1112_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1112_);
v___x_1114_ = lean_apply_2(v_toPure_1104_, lean_box(0), v___x_1113_);
return v___x_1114_;
}
v___jp_1117_:
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_nat_dec_le(v___y_1118_, v___x_1116_);
if (v___x_1119_ == 0)
{
lean_dec(v___x_1116_);
lean_inc(v___y_1118_);
v___y_1111_ = v___y_1118_;
v___y_1112_ = v___y_1118_;
goto v___jp_1110_;
}
else
{
v___y_1111_ = v___y_1118_;
v___y_1112_ = v___x_1116_;
goto v___jp_1110_;
}
}
}
else
{
lean_object* v___x_1121_; 
lean_dec_ref(v_mctx_1105_);
v___x_1121_ = lean_apply_2(v_toPure_1104_, lean_box(0), v_mvarIds_1103_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_mvarIds_1124_){
_start:
{
lean_object* v_toApplicative_1125_; lean_object* v_toBind_1126_; lean_object* v_getMCtx_1127_; lean_object* v_toPure_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; 
v_toApplicative_1125_ = lean_ctor_get(v_inst_1123_, 0);
lean_inc_ref(v_toApplicative_1125_);
v_toBind_1126_ = lean_ctor_get(v_inst_1123_, 1);
lean_inc(v_toBind_1126_);
lean_dec_ref(v_inst_1123_);
v_getMCtx_1127_ = lean_ctor_get(v_inst_1122_, 0);
lean_inc(v_getMCtx_1127_);
lean_dec_ref(v_inst_1122_);
v_toPure_1128_ = lean_ctor_get(v_toApplicative_1125_, 1);
lean_inc(v_toPure_1128_);
lean_dec_ref(v_toApplicative_1125_);
v___f_1129_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1129_, 0, v_mvarIds_1124_);
lean_closure_set(v___f_1129_, 1, v_toPure_1128_);
v___x_1130_ = lean_apply_4(v_toBind_1126_, lean_box(0), lean_box(0), v_getMCtx_1127_, v___f_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object* v_m_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_mvarIds_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1132_, v_inst_1133_, v_mvarIds_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_mvarIds_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1136_, v_inst_1137_, v_mvarIds_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object* v_m_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_mvarIds_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1141_, v_inst_1142_, v_mvarIds_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v_mctx_1151_; lean_object* v___x_1152_; 
v___x_1150_ = lean_st_ref_get(v___y_1146_);
v_mctx_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc_ref(v_mctx_1151_);
lean_dec(v___x_1150_);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_mctx_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed(lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1(lean_object* v_val_1159_, lean_object* v_toPure_1160_, lean_object* v_newMVarIds_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_val_1159_);
lean_ctor_set(v___x_1162_, 1, v_newMVarIds_1161_);
v___x_1163_ = lean_apply_2(v_toPure_1160_, lean_box(0), v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2(lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v_inst_1166_, lean_object* v_toBind_1167_, lean_object* v___f_1168_, lean_object* v_newMVarIds_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v___x_1164_, v___x_1165_, v_newMVarIds_1169_);
v___x_1171_ = lean_apply_2(v_inst_1166_, lean_box(0), v___x_1170_);
v___x_1172_ = lean_apply_4(v_toBind_1167_, lean_box(0), lean_box(0), v___x_1171_, v___f_1168_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3(lean_object* v_mvarCounter_1173_, lean_object* v_inst_1174_, lean_object* v_toBind_1175_, lean_object* v___f_1176_, lean_object* v_newMVarIds_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_filterOldMVars___boxed), 7, 2);
lean_closure_set(v___x_1178_, 0, v_newMVarIds_1177_);
lean_closure_set(v___x_1178_, 1, v_mvarCounter_1173_);
v___x_1179_ = lean_apply_2(v_inst_1174_, lean_box(0), v___x_1178_);
v___x_1180_ = lean_apply_4(v_toBind_1175_, lean_box(0), lean_box(0), v___x_1179_, v___f_1176_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4(lean_object* v_toPure_1181_, lean_object* v___x_1182_, lean_object* v___x_1183_, lean_object* v_inst_1184_, lean_object* v_toBind_1185_, lean_object* v_mvarCounter_1186_, lean_object* v_val_1187_){
_start:
{
lean_object* v___f_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_inc_ref(v_val_1187_);
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1188_, 0, v_val_1187_);
lean_closure_set(v___f_1188_, 1, v_toPure_1181_);
lean_inc_n(v_toBind_1185_, 2);
lean_inc_n(v_inst_1184_, 2);
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1189_, 0, v___x_1182_);
lean_closure_set(v___f_1189_, 1, v___x_1183_);
lean_closure_set(v___f_1189_, 2, v_inst_1184_);
lean_closure_set(v___f_1189_, 3, v_toBind_1185_);
lean_closure_set(v___f_1189_, 4, v___f_1188_);
v___f_1190_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1190_, 0, v_mvarCounter_1186_);
lean_closure_set(v___f_1190_, 1, v_inst_1184_);
lean_closure_set(v___f_1190_, 2, v_toBind_1185_);
lean_closure_set(v___f_1190_, 3, v___f_1189_);
v___x_1191_ = lean_alloc_closure((void*)(l_Lean_Meta_getMVarsNoDelayed___boxed), 6, 1);
lean_closure_set(v___x_1191_, 0, v_val_1187_);
v___x_1192_ = lean_apply_2(v_inst_1184_, lean_box(0), v___x_1191_);
v___x_1193_ = lean_apply_4(v_toBind_1185_, lean_box(0), lean_box(0), v___x_1192_, v___f_1190_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5(lean_object* v_toPure_1194_, lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v_inst_1197_, lean_object* v_toBind_1198_, lean_object* v_k_1199_, lean_object* v_____do__lift_1200_){
_start:
{
lean_object* v_mvarCounter_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; 
v_mvarCounter_1201_ = lean_ctor_get(v_____do__lift_1200_, 3);
lean_inc(v_mvarCounter_1201_);
lean_dec_ref(v_____do__lift_1200_);
lean_inc(v_toBind_1198_);
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1202_, 0, v_toPure_1194_);
lean_closure_set(v___f_1202_, 1, v___x_1195_);
lean_closure_set(v___f_1202_, 2, v___x_1196_);
lean_closure_set(v___f_1202_, 3, v_inst_1197_);
lean_closure_set(v___f_1202_, 4, v_toBind_1198_);
lean_closure_set(v___f_1202_, 5, v_mvarCounter_1201_);
v___x_1203_ = lean_apply_4(v_toBind_1198_, lean_box(0), lean_box(0), v_k_1199_, v___f_1202_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0(void){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_instMonadEIO(lean_box(0));
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0);
v___x_1206_ = l_StateRefT_x27_instMonad___redArg(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg(lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_k_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v_toApplicative_1217_; lean_object* v_toFunctor_1218_; lean_object* v_toSeq_1219_; lean_object* v_toSeqLeft_1220_; lean_object* v_toSeqRight_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___f_1224_; lean_object* v___f_1225_; lean_object* v___x_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_toApplicative_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1267_; 
v___x_1215_ = l_Lean_Meta_instMonadMCtxMetaM;
v___x_1216_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1);
v_toApplicative_1217_ = lean_ctor_get(v___x_1216_, 0);
v_toFunctor_1218_ = lean_ctor_get(v_toApplicative_1217_, 0);
v_toSeq_1219_ = lean_ctor_get(v_toApplicative_1217_, 2);
v_toSeqLeft_1220_ = lean_ctor_get(v_toApplicative_1217_, 3);
v_toSeqRight_1221_ = lean_ctor_get(v_toApplicative_1217_, 4);
v___f_1222_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2));
v___f_1223_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1218_, 2);
v___f_1224_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1224_, 0, v_toFunctor_1218_);
v___f_1225_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1225_, 0, v_toFunctor_1218_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___f_1224_);
lean_ctor_set(v___x_1226_, 1, v___f_1225_);
lean_inc(v_toSeqRight_1221_);
v___f_1227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1227_, 0, v_toSeqRight_1221_);
lean_inc(v_toSeqLeft_1220_);
v___f_1228_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1228_, 0, v_toSeqLeft_1220_);
lean_inc(v_toSeq_1219_);
v___f_1229_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1229_, 0, v_toSeq_1219_);
v___x_1230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1226_);
lean_ctor_set(v___x_1230_, 1, v___f_1222_);
lean_ctor_set(v___x_1230_, 2, v___f_1229_);
lean_ctor_set(v___x_1230_, 3, v___f_1228_);
lean_ctor_set(v___x_1230_, 4, v___f_1227_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v___f_1223_);
v___x_1232_ = l_StateRefT_x27_instMonad___redArg(v___x_1231_);
v_toApplicative_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v___x_1232_, 1);
lean_dec(v_unused_1268_);
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1267_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_toApplicative_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1267_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_toFunctor_1237_; lean_object* v_toSeq_1238_; lean_object* v_toSeqLeft_1239_; lean_object* v_toSeqRight_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1265_; 
v_toFunctor_1237_ = lean_ctor_get(v_toApplicative_1233_, 0);
v_toSeq_1238_ = lean_ctor_get(v_toApplicative_1233_, 2);
v_toSeqLeft_1239_ = lean_ctor_get(v_toApplicative_1233_, 3);
v_toSeqRight_1240_ = lean_ctor_get(v_toApplicative_1233_, 4);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_toApplicative_1233_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v_toApplicative_1233_, 1);
lean_dec(v_unused_1266_);
v___x_1242_ = v_toApplicative_1233_;
v_isShared_1243_ = v_isSharedCheck_1265_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_toSeqRight_1240_);
lean_inc(v_toSeqLeft_1239_);
lean_inc(v_toSeq_1238_);
lean_inc(v_toFunctor_1237_);
lean_dec(v_toApplicative_1233_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1265_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; lean_object* v___f_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; lean_object* v___x_1253_; 
v___f_1244_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4));
v___f_1245_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_1237_);
v___f_1246_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1246_, 0, v_toFunctor_1237_);
v___f_1247_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1247_, 0, v_toFunctor_1237_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___f_1246_);
lean_ctor_set(v___x_1248_, 1, v___f_1247_);
v___f_1249_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1249_, 0, v_toSeqRight_1240_);
v___f_1250_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1250_, 0, v_toSeqLeft_1239_);
v___f_1251_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1251_, 0, v_toSeq_1238_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v___f_1249_);
lean_ctor_set(v___x_1242_, 3, v___f_1250_);
lean_ctor_set(v___x_1242_, 2, v___f_1251_);
lean_ctor_set(v___x_1242_, 1, v___f_1244_);
lean_ctor_set(v___x_1242_, 0, v___x_1248_);
v___x_1253_ = v___x_1242_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___f_1244_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v___f_1251_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v___f_1250_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v___f_1249_);
v___x_1253_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___f_1245_);
lean_ctor_set(v___x_1235_, 0, v___x_1253_);
v___x_1255_ = v___x_1235_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___f_1245_);
v___x_1255_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v_toApplicative_1256_; lean_object* v_toBind_1257_; lean_object* v_toPure_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; 
v_toApplicative_1256_ = lean_ctor_get(v_inst_1212_, 0);
lean_inc_ref(v_toApplicative_1256_);
v_toBind_1257_ = lean_ctor_get(v_inst_1212_, 1);
lean_inc_n(v_toBind_1257_, 2);
lean_dec_ref(v_inst_1212_);
v_toPure_1258_ = lean_ctor_get(v_toApplicative_1256_, 1);
lean_inc(v_toPure_1258_);
lean_dec_ref(v_toApplicative_1256_);
v___f_1259_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6));
lean_inc(v_inst_1213_);
v___x_1260_ = lean_apply_2(v_inst_1213_, lean_box(0), v___f_1259_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5), 7, 6);
lean_closure_set(v___f_1261_, 0, v_toPure_1258_);
lean_closure_set(v___f_1261_, 1, v___x_1215_);
lean_closure_set(v___f_1261_, 2, v___x_1255_);
lean_closure_set(v___f_1261_, 3, v_inst_1213_);
lean_closure_set(v___f_1261_, 4, v_toBind_1257_);
lean_closure_set(v___f_1261_, 5, v_k_1214_);
v___x_1262_ = lean_apply_4(v_toBind_1257_, lean_box(0), lean_box(0), v___x_1260_, v___f_1261_);
return v___x_1262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars(lean_object* v_m_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_k_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg(v_inst_1270_, v_inst_1271_, v_k_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(lean_object* v_as_1274_, size_t v_i_1275_, size_t v_stop_1276_, lean_object* v_b_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_a_1286_; uint8_t v___x_1290_; 
v___x_1290_ = lean_usize_dec_eq(v_i_1275_, v_stop_1276_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; uint8_t v_a_1293_; lean_object* v___x_1295_; 
v___x_1291_ = lean_array_uget_borrowed(v_as_1274_, v_i_1275_);
lean_inc(v___x_1291_);
v___x_1295_ = l_Lean_Elab_Term_isLetRecAuxMVar(v___x_1291_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; uint8_t v___x_1297_; uint8_t v___x_1298_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v___x_1297_ = lean_unbox(v_a_1296_);
lean_dec(v_a_1296_);
v___x_1298_ = lean_bool_not(v___x_1297_);
v_a_1293_ = v___x_1298_;
goto v___jp_1292_;
}
else
{
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1299_; uint8_t v___x_1300_; 
v_a_1299_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1295_, 1);
v___x_1300_ = lean_unbox(v_a_1299_);
lean_dec(v_a_1299_);
v_a_1293_ = v___x_1300_;
goto v___jp_1292_;
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref(v_b_1277_);
v_a_1301_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1295_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1295_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
v___jp_1292_:
{
if (v_a_1293_ == 0)
{
v_a_1286_ = v_b_1277_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1294_; 
lean_inc(v___x_1291_);
v___x_1294_ = lean_array_push(v_b_1277_, v___x_1291_);
v_a_1286_ = v___x_1294_;
goto v___jp_1285_;
}
}
}
else
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_b_1277_);
return v___x_1309_;
}
v___jp_1285_:
{
size_t v___x_1287_; size_t v___x_1288_; 
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = lean_usize_add(v_i_1275_, v___x_1287_);
v_i_1275_ = v___x_1288_;
v_b_1277_ = v_a_1286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg___boxed(lean_object* v_as_1310_, lean_object* v_i_1311_, lean_object* v_stop_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
size_t v_i_boxed_1321_; size_t v_stop_boxed_1322_; lean_object* v_res_1323_; 
v_i_boxed_1321_ = lean_unbox_usize(v_i_1311_);
lean_dec(v_i_1311_);
v_stop_boxed_1322_ = lean_unbox_usize(v_stop_1312_);
lean_dec(v_stop_1312_);
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1310_, v_i_boxed_1321_, v_stop_boxed_1322_, v_b_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec_ref(v_as_1310_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(lean_object* v_as_1324_, size_t v_i_1325_, size_t v_stop_1326_, lean_object* v_b_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_eq(v_i_1325_, v_stop_1326_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_array_uget_borrowed(v_as_1324_, v_i_1325_);
lean_inc(v___x_1334_);
v___x_1335_ = l_Lean_MVarId_getKind(v___x_1334_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_a_1338_; uint8_t v___x_1342_; uint8_t v___x_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1342_ = lean_unbox(v_a_1336_);
lean_dec(v_a_1336_);
v___x_1343_ = l_Lean_MetavarKind_isNatural(v___x_1342_);
if (v___x_1343_ == 0)
{
v_a_1338_ = v_b_1327_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1344_; 
lean_inc(v___x_1334_);
v___x_1344_ = lean_array_push(v_b_1327_, v___x_1334_);
v_a_1338_ = v___x_1344_;
goto v___jp_1337_;
}
v___jp_1337_:
{
size_t v___x_1339_; size_t v___x_1340_; 
v___x_1339_ = ((size_t)1ULL);
v___x_1340_ = lean_usize_add(v_i_1325_, v___x_1339_);
v_i_1325_ = v___x_1340_;
v_b_1327_ = v_a_1338_;
goto _start;
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_b_1327_);
v_a_1345_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1335_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1335_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_b_1327_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg___boxed(lean_object* v_as_1354_, lean_object* v_i_1355_, lean_object* v_stop_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
size_t v_i_boxed_1363_; size_t v_stop_boxed_1364_; lean_object* v_res_1365_; 
v_i_boxed_1363_ = lean_unbox_usize(v_i_1355_);
lean_dec(v_i_1355_);
v_stop_boxed_1364_ = lean_unbox_usize(v_stop_1356_);
lean_dec(v_stop_1356_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1354_, v_i_boxed_1363_, v_stop_boxed_1364_, v_b_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v_as_1354_);
return v_res_1365_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___x_1366_, lean_object* v_mvarId_u2081_1367_, lean_object* v_mvarId_u2082_1368_){
_start:
{
lean_object* v_decl_u2081_1369_; lean_object* v_index_1370_; lean_object* v_decl_u2082_1371_; lean_object* v_index_1372_; uint8_t v___x_1373_; uint8_t v___x_1374_; 
lean_inc(v_mvarId_u2081_1367_);
v_decl_u2081_1369_ = l_Lean_MetavarContext_getDecl(v___x_1366_, v_mvarId_u2081_1367_);
v_index_1370_ = lean_ctor_get(v_decl_u2081_1369_, 6);
lean_inc(v_index_1370_);
lean_dec_ref(v_decl_u2081_1369_);
lean_inc(v_mvarId_u2082_1368_);
v_decl_u2082_1371_ = l_Lean_MetavarContext_getDecl(v___x_1366_, v_mvarId_u2082_1368_);
v_index_1372_ = lean_ctor_get(v_decl_u2082_1371_, 6);
lean_inc(v_index_1372_);
lean_dec_ref(v_decl_u2082_1371_);
v___x_1373_ = lean_nat_dec_eq(v_index_1370_, v_index_1372_);
v___x_1374_ = lean_bool_not(v___x_1373_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; 
lean_dec(v_index_1372_);
lean_dec(v_index_1370_);
v___x_1375_ = l_Lean_Name_quickLt(v_mvarId_u2081_1367_, v_mvarId_u2082_1368_);
lean_dec(v_mvarId_u2082_1368_);
lean_dec(v_mvarId_u2081_1367_);
return v___x_1375_;
}
else
{
uint8_t v___x_1376_; 
lean_dec(v_mvarId_u2082_1368_);
lean_dec(v_mvarId_u2081_1367_);
v___x_1376_ = lean_nat_dec_lt(v_index_1370_, v_index_1372_);
lean_dec(v_index_1372_);
lean_dec(v_index_1370_);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_1377_, lean_object* v_mvarId_u2081_1378_, lean_object* v_mvarId_u2082_1379_){
_start:
{
uint8_t v_res_1380_; lean_object* v_r_1381_; 
v_res_1380_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1377_, v_mvarId_u2081_1378_, v_mvarId_u2082_1379_);
lean_dec_ref(v___x_1377_);
v_r_1381_ = lean_box(v_res_1380_);
return v_r_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___x_1382_, lean_object* v_hi_1383_, lean_object* v_pivot_1384_, lean_object* v_as_1385_, lean_object* v_i_1386_, lean_object* v_k_1387_){
_start:
{
uint8_t v___y_1389_; uint8_t v___x_1398_; 
v___x_1398_ = lean_nat_dec_lt(v_k_1387_, v_hi_1383_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec(v_k_1387_);
lean_dec(v_pivot_1384_);
v___x_1399_ = lean_array_fswap(v_as_1385_, v_i_1386_, v_hi_1383_);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_i_1386_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; lean_object* v_decl_u2081_1402_; lean_object* v_index_1403_; lean_object* v_decl_u2082_1404_; lean_object* v_index_1405_; uint8_t v___x_1406_; uint8_t v___x_1407_; 
v___x_1401_ = lean_array_fget_borrowed(v_as_1385_, v_k_1387_);
lean_inc(v___x_1401_);
v_decl_u2081_1402_ = l_Lean_MetavarContext_getDecl(v___x_1382_, v___x_1401_);
v_index_1403_ = lean_ctor_get(v_decl_u2081_1402_, 6);
lean_inc(v_index_1403_);
lean_dec_ref(v_decl_u2081_1402_);
lean_inc(v_pivot_1384_);
v_decl_u2082_1404_ = l_Lean_MetavarContext_getDecl(v___x_1382_, v_pivot_1384_);
v_index_1405_ = lean_ctor_get(v_decl_u2082_1404_, 6);
lean_inc(v_index_1405_);
lean_dec_ref(v_decl_u2082_1404_);
v___x_1406_ = lean_nat_dec_eq(v_index_1403_, v_index_1405_);
v___x_1407_ = lean_bool_not(v___x_1406_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; 
lean_dec(v_index_1405_);
lean_dec(v_index_1403_);
v___x_1408_ = l_Lean_Name_quickLt(v___x_1401_, v_pivot_1384_);
v___y_1389_ = v___x_1408_;
goto v___jp_1388_;
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_nat_dec_lt(v_index_1403_, v_index_1405_);
lean_dec(v_index_1405_);
lean_dec(v_index_1403_);
v___y_1389_ = v___x_1409_;
goto v___jp_1388_;
}
}
v___jp_1388_:
{
if (v___y_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_unsigned_to_nat(1u);
v___x_1391_ = lean_nat_add(v_k_1387_, v___x_1390_);
lean_dec(v_k_1387_);
v_k_1387_ = v___x_1391_;
goto _start;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1393_ = lean_array_fswap(v_as_1385_, v_i_1386_, v_k_1387_);
v___x_1394_ = lean_unsigned_to_nat(1u);
v___x_1395_ = lean_nat_add(v_i_1386_, v___x_1394_);
lean_dec(v_i_1386_);
v___x_1396_ = lean_nat_add(v_k_1387_, v___x_1394_);
lean_dec(v_k_1387_);
v_as_1385_ = v___x_1393_;
v_i_1386_ = v___x_1395_;
v_k_1387_ = v___x_1396_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___x_1410_, lean_object* v_hi_1411_, lean_object* v_pivot_1412_, lean_object* v_as_1413_, lean_object* v_i_1414_, lean_object* v_k_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1410_, v_hi_1411_, v_pivot_1412_, v_as_1413_, v_i_1414_, v_k_1415_);
lean_dec(v_hi_1411_);
lean_dec_ref(v___x_1410_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(lean_object* v___x_1417_, lean_object* v_n_1418_, lean_object* v_as_1419_, lean_object* v_lo_1420_, lean_object* v_hi_1421_){
_start:
{
lean_object* v___y_1423_; uint8_t v___x_1433_; 
v___x_1433_ = lean_nat_dec_lt(v_lo_1420_, v_hi_1421_);
if (v___x_1433_ == 0)
{
lean_dec(v_lo_1420_);
return v_as_1419_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v_mid_1436_; lean_object* v___y_1438_; lean_object* v___y_1444_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1434_ = lean_nat_add(v_lo_1420_, v_hi_1421_);
v___x_1435_ = lean_unsigned_to_nat(1u);
v_mid_1436_ = lean_nat_shiftr(v___x_1434_, v___x_1435_);
lean_dec(v___x_1434_);
v___x_1449_ = lean_array_fget_borrowed(v_as_1419_, v_mid_1436_);
v___x_1450_ = lean_array_fget_borrowed(v_as_1419_, v_lo_1420_);
lean_inc(v___x_1450_);
lean_inc(v___x_1449_);
v___x_1451_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1417_, v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
v___y_1444_ = v_as_1419_;
goto v___jp_1443_;
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_array_fswap(v_as_1419_, v_lo_1420_, v_mid_1436_);
v___y_1444_ = v___x_1452_;
goto v___jp_1443_;
}
v___jp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_array_fget_borrowed(v___y_1438_, v_mid_1436_);
v___x_1440_ = lean_array_fget_borrowed(v___y_1438_, v_hi_1421_);
lean_inc(v___x_1440_);
lean_inc(v___x_1439_);
v___x_1441_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1417_, v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_dec(v_mid_1436_);
v___y_1423_ = v___y_1438_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_array_fswap(v___y_1438_, v_mid_1436_, v_hi_1421_);
lean_dec(v_mid_1436_);
v___y_1423_ = v___x_1442_;
goto v___jp_1422_;
}
}
v___jp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = lean_array_fget_borrowed(v___y_1444_, v_hi_1421_);
v___x_1446_ = lean_array_fget_borrowed(v___y_1444_, v_lo_1420_);
lean_inc(v___x_1446_);
lean_inc(v___x_1445_);
v___x_1447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1417_, v___x_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
v___y_1438_ = v___y_1444_;
goto v___jp_1437_;
}
else
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_array_fswap(v___y_1444_, v_lo_1420_, v_hi_1421_);
v___y_1438_ = v___x_1448_;
goto v___jp_1437_;
}
}
}
v___jp_1422_:
{
lean_object* v_pivot_1424_; lean_object* v___x_1425_; lean_object* v_fst_1426_; lean_object* v_snd_1427_; uint8_t v___x_1428_; 
v_pivot_1424_ = lean_array_fget(v___y_1423_, v_hi_1421_);
lean_inc_n(v_lo_1420_, 2);
v___x_1425_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1417_, v_hi_1421_, v_pivot_1424_, v___y_1423_, v_lo_1420_, v_lo_1420_);
v_fst_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_fst_1426_);
v_snd_1427_ = lean_ctor_get(v___x_1425_, 1);
lean_inc(v_snd_1427_);
lean_dec_ref(v___x_1425_);
v___x_1428_ = lean_nat_dec_le(v_hi_1421_, v_fst_1426_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1417_, v_n_1418_, v_snd_1427_, v_lo_1420_, v_fst_1426_);
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = lean_nat_add(v_fst_1426_, v___x_1430_);
lean_dec(v_fst_1426_);
v_as_1419_ = v___x_1429_;
v_lo_1420_ = v___x_1431_;
goto _start;
}
else
{
lean_dec(v_fst_1426_);
lean_dec(v_lo_1420_);
return v_snd_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_1453_, lean_object* v_n_1454_, lean_object* v_as_1455_, lean_object* v_lo_1456_, lean_object* v_hi_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1453_, v_n_1454_, v_as_1455_, v_lo_1456_, v_hi_1457_);
lean_dec(v_hi_1457_);
lean_dec(v_n_1454_);
lean_dec_ref(v___x_1453_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(lean_object* v_mvarIds_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; lean_object* v_mctx_1463_; lean_object* v___x_1464_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1462_ = lean_st_ref_get(v___y_1460_);
v_mctx_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc_ref(v_mctx_1463_);
lean_dec(v___x_1462_);
v___x_1464_ = lean_array_get_size(v_mvarIds_1459_);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = lean_nat_dec_eq(v___x_1464_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___y_1475_; uint8_t v___x_1477_; 
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_sub(v___x_1464_, v___x_1472_);
v___x_1477_ = lean_nat_dec_le(v___x_1470_, v___x_1473_);
if (v___x_1477_ == 0)
{
lean_inc(v___x_1473_);
v___y_1475_ = v___x_1473_;
goto v___jp_1474_;
}
else
{
v___y_1475_ = v___x_1470_;
goto v___jp_1474_;
}
v___jp_1474_:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_nat_dec_le(v___y_1475_, v___x_1473_);
if (v___x_1476_ == 0)
{
lean_dec(v___x_1473_);
lean_inc(v___y_1475_);
v___y_1466_ = v___y_1475_;
v___y_1467_ = v___y_1475_;
goto v___jp_1465_;
}
else
{
v___y_1466_ = v___y_1475_;
v___y_1467_ = v___x_1473_;
goto v___jp_1465_;
}
}
}
else
{
lean_object* v___x_1478_; 
lean_dec_ref(v_mctx_1463_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_mvarIds_1459_);
return v___x_1478_;
}
v___jp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v_mctx_1463_, v___x_1464_, v_mvarIds_1459_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v_mctx_1463_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(lean_object* v_mvarIds_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1479_, v___y_1480_);
lean_dec(v___y_1480_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(lean_object* v_k_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; lean_object* v_mctx_1494_; lean_object* v_mvarCounter_1495_; lean_object* v___x_1496_; 
v___x_1493_ = lean_st_ref_get(v___y_1489_);
v_mctx_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc_ref(v_mctx_1494_);
lean_dec(v___x_1493_);
v_mvarCounter_1495_ = lean_ctor_get(v_mctx_1494_, 3);
lean_inc(v_mvarCounter_1495_);
lean_dec_ref(v_mctx_1494_);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
lean_inc(v___y_1489_);
lean_inc_ref(v___y_1488_);
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
v___x_1496_ = lean_apply_9(v_k_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, lean_box(0));
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc_n(v_a_1497_, 2);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = l_Lean_Meta_getMVarsNoDelayed(v_a_1497_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1500_; lean_object* v_a_1501_; lean_object* v___x_1502_; lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1511_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v___x_1500_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1499_, v_mvarCounter_1495_, v___y_1489_);
lean_dec(v_mvarCounter_1495_);
lean_dec(v_a_1499_);
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref(v___x_1500_);
v___x_1502_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_a_1501_, v___y_1489_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_a_1497_);
lean_ctor_set(v___x_1507_, 1, v_a_1503_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1507_);
v___x_1509_ = v___x_1505_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v_a_1497_);
lean_dec(v_mvarCounter_1495_);
v_a_1512_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1498_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1498_);
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
lean_dec(v_mvarCounter_1495_);
v_a_1520_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1496_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1496_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(lean_object* v_k_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object* v_k_1539_, lean_object* v_parentTag_1540_, lean_object* v_tagSuffix_1541_, uint8_t v_allowNaturalHoles_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1539_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v_fst_1554_; lean_object* v_snd_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1648_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v_fst_1554_ = lean_ctor_get(v_a_1553_, 0);
v_snd_1555_ = lean_ctor_get(v_a_1553_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_a_1553_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1557_ = v_a_1553_;
v_isShared_1558_ = v_isSharedCheck_1648_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
lean_dec(v_a_1553_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1648_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1591_; lean_object* v_a_1592_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___x_1614_; lean_object* v_a_1616_; lean_object* v___y_1628_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1638_ = lean_array_get_size(v_snd_1555_);
v___x_1639_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1640_ = lean_nat_dec_lt(v___x_1614_, v___x_1638_);
if (v___x_1640_ == 0)
{
lean_dec(v_snd_1555_);
v_a_1616_ = v___x_1639_;
goto v___jp_1615_;
}
else
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_le(v___x_1638_, v___x_1638_);
if (v___x_1641_ == 0)
{
if (v___x_1640_ == 0)
{
lean_dec(v_snd_1555_);
v_a_1616_ = v___x_1639_;
goto v___jp_1615_;
}
else
{
size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = ((size_t)0ULL);
v___x_1643_ = lean_usize_of_nat(v___x_1638_);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_1555_, v___x_1642_, v___x_1643_, v___x_1639_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
lean_dec(v_snd_1555_);
v___y_1628_ = v___x_1644_;
goto v___jp_1627_;
}
}
else
{
size_t v___x_1645_; size_t v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = ((size_t)0ULL);
v___x_1646_ = lean_usize_of_nat(v___x_1638_);
v___x_1647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_1555_, v___x_1645_, v___x_1646_, v___x_1639_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
lean_dec(v_snd_1555_);
v___y_1628_ = v___x_1647_;
goto v___jp_1627_;
}
}
v___jp_1559_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_array_to_list(v___y_1560_);
v___x_1570_ = l_Lean_Elab_Tactic_tagUntaggedGoals(v_parentTag_1540_, v_tagSuffix_1541_, v___x_1569_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1580_; 
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v___x_1570_, 0);
lean_dec(v_unused_1581_);
v___x_1572_ = v___x_1570_;
v_isShared_1573_ = v_isSharedCheck_1580_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v___x_1570_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1580_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 1, v___x_1569_);
v___x_1575_ = v___x_1557_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_fst_1554_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___x_1569_);
v___x_1575_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1577_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
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
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v___x_1569_);
lean_del_object(v___x_1557_);
lean_dec(v_fst_1554_);
v_a_1582_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1570_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1570_);
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
}
v___jp_1590_:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1592_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
lean_dec_ref(v_a_1592_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_dec_ref_known(v___x_1593_, 1);
v___y_1560_ = v___y_1591_;
v___y_1561_ = v_a_1543_;
v___y_1562_ = v_a_1544_;
v___y_1563_ = v_a_1545_;
v___y_1564_ = v_a_1546_;
v___y_1565_ = v_a_1547_;
v___y_1566_ = v_a_1548_;
v___y_1567_ = v_a_1549_;
v___y_1568_ = v_a_1550_;
goto v___jp_1559_;
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v___y_1591_);
lean_del_object(v___x_1557_);
lean_dec(v_fst_1554_);
lean_dec(v_tagSuffix_1541_);
lean_dec(v_parentTag_1540_);
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
v___jp_1602_:
{
if (lean_obj_tag(v___y_1604_) == 0)
{
lean_object* v_a_1605_; 
v_a_1605_ = lean_ctor_get(v___y_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___y_1604_, 1);
v___y_1591_ = v___y_1603_;
v_a_1592_ = v_a_1605_;
goto v___jp_1590_;
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v___y_1603_);
lean_del_object(v___x_1557_);
lean_dec(v_fst_1554_);
lean_dec(v_tagSuffix_1541_);
lean_dec(v_parentTag_1540_);
v_a_1606_ = lean_ctor_get(v___y_1604_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___y_1604_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___y_1604_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___y_1604_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
v___jp_1615_:
{
if (v_allowNaturalHoles_1542_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1617_ = lean_array_get_size(v_a_1616_);
v___x_1618_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1619_ = lean_nat_dec_lt(v___x_1614_, v___x_1617_);
if (v___x_1619_ == 0)
{
v___y_1591_ = v_a_1616_;
v_a_1592_ = v___x_1618_;
goto v___jp_1590_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_nat_dec_le(v___x_1617_, v___x_1617_);
if (v___x_1620_ == 0)
{
if (v___x_1619_ == 0)
{
v___y_1591_ = v_a_1616_;
v_a_1592_ = v___x_1618_;
goto v___jp_1590_;
}
else
{
size_t v___x_1621_; size_t v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = ((size_t)0ULL);
v___x_1622_ = lean_usize_of_nat(v___x_1617_);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_1616_, v___x_1621_, v___x_1622_, v___x_1618_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
v___y_1603_ = v_a_1616_;
v___y_1604_ = v___x_1623_;
goto v___jp_1602_;
}
}
else
{
size_t v___x_1624_; size_t v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = ((size_t)0ULL);
v___x_1625_ = lean_usize_of_nat(v___x_1617_);
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_1616_, v___x_1624_, v___x_1625_, v___x_1618_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
v___y_1603_ = v_a_1616_;
v___y_1604_ = v___x_1626_;
goto v___jp_1602_;
}
}
}
else
{
v___y_1560_ = v_a_1616_;
v___y_1561_ = v_a_1543_;
v___y_1562_ = v_a_1544_;
v___y_1563_ = v_a_1545_;
v___y_1564_ = v_a_1546_;
v___y_1565_ = v_a_1547_;
v___y_1566_ = v_a_1548_;
v___y_1567_ = v_a_1549_;
v___y_1568_ = v_a_1550_;
goto v___jp_1559_;
}
}
v___jp_1627_:
{
if (lean_obj_tag(v___y_1628_) == 0)
{
lean_object* v_a_1629_; 
v_a_1629_ = lean_ctor_get(v___y_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___y_1628_, 1);
v_a_1616_ = v_a_1629_;
goto v___jp_1615_;
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_del_object(v___x_1557_);
lean_dec(v_fst_1554_);
lean_dec(v_tagSuffix_1541_);
lean_dec(v_parentTag_1540_);
v_a_1630_ = lean_ctor_get(v___y_1628_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___y_1628_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___y_1628_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___y_1628_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_tagSuffix_1541_);
lean_dec(v_parentTag_1540_);
v_a_1649_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1552_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1552_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object* v_k_1657_, lean_object* v_parentTag_1658_, lean_object* v_tagSuffix_1659_, lean_object* v_allowNaturalHoles_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1670_; lean_object* v_res_1671_; 
v_allowNaturalHoles_boxed_1670_ = lean_unbox(v_allowNaturalHoles_1660_);
v_res_1671_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1657_, v_parentTag_1658_, v_tagSuffix_1659_, v_allowNaturalHoles_boxed_1670_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(lean_object* v_as_1672_, size_t v_i_1673_, size_t v_stop_1674_, lean_object* v_b_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1672_, v_i_1673_, v_stop_1674_, v_b_1675_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___boxed(lean_object* v_as_1686_, lean_object* v_i_1687_, lean_object* v_stop_1688_, lean_object* v_b_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
size_t v_i_boxed_1699_; size_t v_stop_boxed_1700_; lean_object* v_res_1701_; 
v_i_boxed_1699_ = lean_unbox_usize(v_i_1687_);
lean_dec(v_i_1687_);
v_stop_boxed_1700_ = lean_unbox_usize(v_stop_1688_);
lean_dec(v_stop_1688_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(v_as_1686_, v_i_boxed_1699_, v_stop_boxed_1700_, v_b_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec_ref(v_as_1686_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(lean_object* v_as_1702_, size_t v_i_1703_, size_t v_stop_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1702_, v_i_1703_, v_stop_1704_, v_b_1705_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___boxed(lean_object* v_as_1716_, lean_object* v_i_1717_, lean_object* v_stop_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
size_t v_i_boxed_1729_; size_t v_stop_boxed_1730_; lean_object* v_res_1731_; 
v_i_boxed_1729_ = lean_unbox_usize(v_i_1717_);
lean_dec(v_i_1717_);
v_stop_boxed_1730_ = lean_unbox_usize(v_stop_1718_);
lean_dec(v_stop_1718_);
v_res_1731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(v_as_1716_, v_i_boxed_1729_, v_stop_boxed_1730_, v_b_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec_ref(v_as_1716_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(lean_object* v_mvarIds_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1732_, v___y_1734_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(lean_object* v_mvarIds_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(v_mvarIds_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(lean_object* v___x_1746_, lean_object* v_n_1747_, lean_object* v_as_1748_, lean_object* v_lo_1749_, lean_object* v_hi_1750_, lean_object* v_w_1751_, lean_object* v_hlo_1752_, lean_object* v_hhi_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1746_, v_n_1747_, v_as_1748_, v_lo_1749_, v_hi_1750_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1755_, lean_object* v_n_1756_, lean_object* v_as_1757_, lean_object* v_lo_1758_, lean_object* v_hi_1759_, lean_object* v_w_1760_, lean_object* v_hlo_1761_, lean_object* v_hhi_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(v___x_1755_, v_n_1756_, v_as_1757_, v_lo_1758_, v_hi_1759_, v_w_1760_, v_hlo_1761_, v_hhi_1762_);
lean_dec(v_hi_1759_);
lean_dec(v_n_1756_);
lean_dec_ref(v___x_1755_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(lean_object* v___x_1764_, lean_object* v_n_1765_, lean_object* v_lo_1766_, lean_object* v_hi_1767_, lean_object* v_hhi_1768_, lean_object* v_pivot_1769_, lean_object* v_as_1770_, lean_object* v_i_1771_, lean_object* v_k_1772_, lean_object* v_ilo_1773_, lean_object* v_ik_1774_, lean_object* v_w_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1764_, v_hi_1767_, v_pivot_1769_, v_as_1770_, v_i_1771_, v_k_1772_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1777_, lean_object* v_n_1778_, lean_object* v_lo_1779_, lean_object* v_hi_1780_, lean_object* v_hhi_1781_, lean_object* v_pivot_1782_, lean_object* v_as_1783_, lean_object* v_i_1784_, lean_object* v_k_1785_, lean_object* v_ilo_1786_, lean_object* v_ik_1787_, lean_object* v_w_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(v___x_1777_, v_n_1778_, v_lo_1779_, v_hi_1780_, v_hhi_1781_, v_pivot_1782_, v_as_1783_, v_i_1784_, v_k_1785_, v_ilo_1786_, v_ik_1787_, v_w_1788_);
lean_dec(v_hi_1780_);
lean_dec(v_lo_1779_);
lean_dec(v_n_1778_);
lean_dec_ref(v___x_1777_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object* v_k_1790_, lean_object* v_parentTag_1791_, lean_object* v_tagSuffix_1792_, uint8_t v_allowNaturalHoles_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
if (v_allowNaturalHoles_1793_ == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1790_, v_parentTag_1791_, v_tagSuffix_1792_, v_allowNaturalHoles_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
return v___x_1803_;
}
else
{
lean_object* v_declName_x3f_1804_; lean_object* v_macroStack_1805_; uint8_t v_mayPostpone_1806_; uint8_t v_errToSorry_1807_; lean_object* v_autoBoundImplicitContext_1808_; lean_object* v_autoBoundImplicitForbidden_1809_; lean_object* v_sectionVars_1810_; lean_object* v_sectionFVars_1811_; uint8_t v_implicitLambda_1812_; uint8_t v_heedElabAsElim_1813_; uint8_t v_isNoncomputableSection_1814_; uint8_t v_isMetaSection_1815_; uint8_t v_ignoreTCFailures_1816_; uint8_t v_inPattern_1817_; lean_object* v_tacSnap_x3f_1818_; uint8_t v_saveRecAppSyntax_1819_; uint8_t v_holesAsSyntheticOpaque_1820_; uint8_t v_checkDeprecated_1821_; lean_object* v_fixedTermElabs_1822_; uint8_t v___y_1824_; 
v_declName_x3f_1804_ = lean_ctor_get(v_a_1796_, 0);
v_macroStack_1805_ = lean_ctor_get(v_a_1796_, 1);
v_mayPostpone_1806_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8);
v_errToSorry_1807_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1808_ = lean_ctor_get(v_a_1796_, 2);
v_autoBoundImplicitForbidden_1809_ = lean_ctor_get(v_a_1796_, 3);
v_sectionVars_1810_ = lean_ctor_get(v_a_1796_, 4);
v_sectionFVars_1811_ = lean_ctor_get(v_a_1796_, 5);
v_implicitLambda_1812_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1813_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1814_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 4);
v_isMetaSection_1815_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_1816_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 6);
v_inPattern_1817_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1818_ = lean_ctor_get(v_a_1796_, 6);
v_saveRecAppSyntax_1819_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1820_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 9);
v_checkDeprecated_1821_ = lean_ctor_get_uint8(v_a_1796_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1822_ = lean_ctor_get(v_a_1796_, 7);
if (v_holesAsSyntheticOpaque_1820_ == 0)
{
v___y_1824_ = v_allowNaturalHoles_1793_;
goto v___jp_1823_;
}
else
{
v___y_1824_ = v_holesAsSyntheticOpaque_1820_;
goto v___jp_1823_;
}
v___jp_1823_:
{
lean_object* v___x_1825_; uint8_t v_foApprox_1826_; uint8_t v_ctxApprox_1827_; uint8_t v_quasiPatternApprox_1828_; uint8_t v_constApprox_1829_; uint8_t v_isDefEqStuckEx_1830_; uint8_t v_unificationHints_1831_; uint8_t v_proofIrrelevance_1832_; uint8_t v_offsetCnstrs_1833_; uint8_t v_transparency_1834_; uint8_t v_etaStruct_1835_; uint8_t v_univApprox_1836_; uint8_t v_iota_1837_; uint8_t v_beta_1838_; uint8_t v_proj_1839_; uint8_t v_zeta_1840_; uint8_t v_zetaDelta_1841_; uint8_t v_zetaUnused_1842_; uint8_t v_zetaHave_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1873_; 
v___x_1825_ = l_Lean_Meta_Context_config(v_a_1798_);
v_foApprox_1826_ = lean_ctor_get_uint8(v___x_1825_, 0);
v_ctxApprox_1827_ = lean_ctor_get_uint8(v___x_1825_, 1);
v_quasiPatternApprox_1828_ = lean_ctor_get_uint8(v___x_1825_, 2);
v_constApprox_1829_ = lean_ctor_get_uint8(v___x_1825_, 3);
v_isDefEqStuckEx_1830_ = lean_ctor_get_uint8(v___x_1825_, 4);
v_unificationHints_1831_ = lean_ctor_get_uint8(v___x_1825_, 5);
v_proofIrrelevance_1832_ = lean_ctor_get_uint8(v___x_1825_, 6);
v_offsetCnstrs_1833_ = lean_ctor_get_uint8(v___x_1825_, 8);
v_transparency_1834_ = lean_ctor_get_uint8(v___x_1825_, 9);
v_etaStruct_1835_ = lean_ctor_get_uint8(v___x_1825_, 10);
v_univApprox_1836_ = lean_ctor_get_uint8(v___x_1825_, 11);
v_iota_1837_ = lean_ctor_get_uint8(v___x_1825_, 12);
v_beta_1838_ = lean_ctor_get_uint8(v___x_1825_, 13);
v_proj_1839_ = lean_ctor_get_uint8(v___x_1825_, 14);
v_zeta_1840_ = lean_ctor_get_uint8(v___x_1825_, 15);
v_zetaDelta_1841_ = lean_ctor_get_uint8(v___x_1825_, 16);
v_zetaUnused_1842_ = lean_ctor_get_uint8(v___x_1825_, 17);
v_zetaHave_1843_ = lean_ctor_get_uint8(v___x_1825_, 18);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1845_ = v___x_1825_;
v_isShared_1846_ = v_isSharedCheck_1873_;
goto v_resetjp_1844_;
}
else
{
lean_dec(v___x_1825_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1873_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
uint8_t v_trackZetaDelta_1847_; lean_object* v_zetaDeltaSet_1848_; lean_object* v_lctx_1849_; lean_object* v_localInstances_1850_; lean_object* v_defEqCtx_x3f_1851_; lean_object* v_synthPendingDepth_1852_; lean_object* v_canUnfold_x3f_1853_; uint8_t v_univApprox_1854_; uint8_t v_inTypeClassResolution_1855_; uint8_t v_cacheInferType_1856_; lean_object* v___x_1858_; 
v_trackZetaDelta_1847_ = lean_ctor_get_uint8(v_a_1798_, sizeof(void*)*7);
v_zetaDeltaSet_1848_ = lean_ctor_get(v_a_1798_, 1);
v_lctx_1849_ = lean_ctor_get(v_a_1798_, 2);
v_localInstances_1850_ = lean_ctor_get(v_a_1798_, 3);
v_defEqCtx_x3f_1851_ = lean_ctor_get(v_a_1798_, 4);
v_synthPendingDepth_1852_ = lean_ctor_get(v_a_1798_, 5);
v_canUnfold_x3f_1853_ = lean_ctor_get(v_a_1798_, 6);
v_univApprox_1854_ = lean_ctor_get_uint8(v_a_1798_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1855_ = lean_ctor_get_uint8(v_a_1798_, sizeof(void*)*7 + 2);
v_cacheInferType_1856_ = lean_ctor_get_uint8(v_a_1798_, sizeof(void*)*7 + 3);
if (v_isShared_1846_ == 0)
{
v___x_1858_ = v___x_1845_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 0, v_foApprox_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 1, v_ctxApprox_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 2, v_quasiPatternApprox_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 3, v_constApprox_1829_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 4, v_isDefEqStuckEx_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 5, v_unificationHints_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 6, v_proofIrrelevance_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 8, v_offsetCnstrs_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 9, v_transparency_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 10, v_etaStruct_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 11, v_univApprox_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 12, v_iota_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 13, v_beta_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 14, v_proj_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 15, v_zeta_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 16, v_zetaDelta_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 17, v_zetaUnused_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, 18, v_zetaHave_1843_);
v___x_1858_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
uint64_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_ctor_set_uint8(v___x_1858_, 7, v_allowNaturalHoles_1793_);
v___x_1859_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1858_);
lean_inc_ref(v_fixedTermElabs_1822_);
lean_inc(v_tacSnap_x3f_1818_);
lean_inc(v_sectionFVars_1811_);
lean_inc(v_sectionVars_1810_);
lean_inc_ref(v_autoBoundImplicitForbidden_1809_);
lean_inc(v_autoBoundImplicitContext_1808_);
lean_inc(v_macroStack_1805_);
lean_inc(v_declName_x3f_1804_);
v___x_1860_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1860_, 0, v_declName_x3f_1804_);
lean_ctor_set(v___x_1860_, 1, v_macroStack_1805_);
lean_ctor_set(v___x_1860_, 2, v_autoBoundImplicitContext_1808_);
lean_ctor_set(v___x_1860_, 3, v_autoBoundImplicitForbidden_1809_);
lean_ctor_set(v___x_1860_, 4, v_sectionVars_1810_);
lean_ctor_set(v___x_1860_, 5, v_sectionFVars_1811_);
lean_ctor_set(v___x_1860_, 6, v_tacSnap_x3f_1818_);
lean_ctor_set(v___x_1860_, 7, v_fixedTermElabs_1822_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8, v_mayPostpone_1806_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 1, v_errToSorry_1807_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 2, v_implicitLambda_1812_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 3, v_heedElabAsElim_1813_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1814_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 5, v_isMetaSection_1815_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 6, v_ignoreTCFailures_1816_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 7, v_inPattern_1817_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1819_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 9, v___y_1824_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*8 + 10, v_checkDeprecated_1821_);
v___x_1861_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1861_, 0, v___x_1858_);
lean_ctor_set_uint64(v___x_1861_, sizeof(void*)*1, v___x_1859_);
lean_inc(v_canUnfold_x3f_1853_);
lean_inc(v_synthPendingDepth_1852_);
lean_inc(v_defEqCtx_x3f_1851_);
lean_inc_ref(v_localInstances_1850_);
lean_inc_ref(v_lctx_1849_);
lean_inc(v_zetaDeltaSet_1848_);
v___x_1862_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v_zetaDeltaSet_1848_);
lean_ctor_set(v___x_1862_, 2, v_lctx_1849_);
lean_ctor_set(v___x_1862_, 3, v_localInstances_1850_);
lean_ctor_set(v___x_1862_, 4, v_defEqCtx_x3f_1851_);
lean_ctor_set(v___x_1862_, 5, v_synthPendingDepth_1852_);
lean_ctor_set(v___x_1862_, 6, v_canUnfold_x3f_1853_);
lean_ctor_set_uint8(v___x_1862_, sizeof(void*)*7, v_trackZetaDelta_1847_);
lean_ctor_set_uint8(v___x_1862_, sizeof(void*)*7 + 1, v_univApprox_1854_);
lean_ctor_set_uint8(v___x_1862_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1855_);
lean_ctor_set_uint8(v___x_1862_, sizeof(void*)*7 + 3, v_cacheInferType_1856_);
v___x_1863_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1790_, v_parentTag_1791_, v_tagSuffix_1792_, v_allowNaturalHoles_1793_, v_a_1794_, v_a_1795_, v___x_1860_, v_a_1797_, v___x_1862_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec_ref_known(v___x_1862_, 7);
lean_dec_ref_known(v___x_1860_, 8);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
return v___x_1863_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object* v_k_1874_, lean_object* v_parentTag_1875_, lean_object* v_tagSuffix_1876_, lean_object* v_allowNaturalHoles_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1887_; lean_object* v_res_1888_; 
v_allowNaturalHoles_boxed_1887_ = lean_unbox(v_allowNaturalHoles_1877_);
v_res_1888_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v_k_1874_, v_parentTag_1875_, v_tagSuffix_1876_, v_allowNaturalHoles_boxed_1887_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object* v_stx_1889_, lean_object* v_expectedType_x3f_1890_, lean_object* v_tagSuffix_1891_, uint8_t v_allowNaturalHoles_1892_, lean_object* v_parentTag_x3f_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_a_1904_; 
if (lean_obj_tag(v_parentTag_x3f_1893_) == 0)
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_Elab_Tactic_getMainTag___redArg(v_a_1895_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v_a_1904_ = v_a_1910_;
goto v___jp_1903_;
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_tagSuffix_1891_);
lean_dec(v_expectedType_x3f_1890_);
lean_dec(v_stx_1889_);
v_a_1911_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1909_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1909_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_val_1919_; 
v_val_1919_ = lean_ctor_get(v_parentTag_x3f_1893_, 0);
lean_inc(v_val_1919_);
lean_dec_ref_known(v_parentTag_x3f_1893_, 1);
v_a_1904_ = v_val_1919_;
goto v___jp_1903_;
}
v___jp_1903_:
{
uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1905_ = 0;
v___x_1906_ = lean_box(v___x_1905_);
v___x_1907_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermEnsuringType___boxed), 12, 3);
lean_closure_set(v___x_1907_, 0, v_stx_1889_);
lean_closure_set(v___x_1907_, 1, v_expectedType_x3f_1890_);
lean_closure_set(v___x_1907_, 2, v___x_1906_);
v___x_1908_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_1907_, v_a_1904_, v_tagSuffix_1891_, v_allowNaturalHoles_1892_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_1908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object* v_stx_1920_, lean_object* v_expectedType_x3f_1921_, lean_object* v_tagSuffix_1922_, lean_object* v_allowNaturalHoles_1923_, lean_object* v_parentTag_x3f_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1934_; lean_object* v_res_1935_; 
v_allowNaturalHoles_boxed_1934_ = lean_unbox(v_allowNaturalHoles_1923_);
v_res_1935_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_stx_1920_, v_expectedType_x3f_1921_, v_tagSuffix_1922_, v_allowNaturalHoles_boxed_1934_, v_parentTag_x3f_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
return v_res_1935_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lam__0(lean_object* v_a_1936_, lean_object* v_x_1937_){
_start:
{
uint8_t v___x_1938_; 
v___x_1938_ = l_Lean_instBEqMVarId_beq(v_x_1937_, v_a_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__0___boxed(lean_object* v_a_1939_, lean_object* v_x_1940_){
_start:
{
uint8_t v_res_1941_; lean_object* v_r_1942_; 
v_res_1941_ = l_Lean_Elab_Tactic_refineCore___lam__0(v_a_1939_, v_x_1940_);
lean_dec(v_x_1940_);
lean_dec(v_a_1939_);
v_r_1942_ = lean_box(v_res_1941_);
return v_r_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v_ks_1947_; lean_object* v_vs_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1972_; 
v_ks_1947_ = lean_ctor_get(v_x_1943_, 0);
v_vs_1948_ = lean_ctor_get(v_x_1943_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_x_1943_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1950_ = v_x_1943_;
v_isShared_1951_ = v_isSharedCheck_1972_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_vs_1948_);
lean_inc(v_ks_1947_);
lean_dec(v_x_1943_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1972_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = lean_array_get_size(v_ks_1947_);
v___x_1953_ = lean_nat_dec_lt(v_x_1944_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_dec(v_x_1944_);
v___x_1954_ = lean_array_push(v_ks_1947_, v_x_1945_);
v___x_1955_ = lean_array_push(v_vs_1948_, v_x_1946_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v___x_1955_);
lean_ctor_set(v___x_1950_, 0, v___x_1954_);
v___x_1957_ = v___x_1950_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
else
{
lean_object* v_k_x27_1959_; uint8_t v___x_1960_; 
v_k_x27_1959_ = lean_array_fget_borrowed(v_ks_1947_, v_x_1944_);
v___x_1960_ = l_Lean_instBEqMVarId_beq(v_x_1945_, v_k_x27_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1962_; 
if (v_isShared_1951_ == 0)
{
v___x_1962_ = v___x_1950_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_ks_1947_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_vs_1948_);
v___x_1962_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_unsigned_to_nat(1u);
v___x_1964_ = lean_nat_add(v_x_1944_, v___x_1963_);
lean_dec(v_x_1944_);
v_x_1943_ = v___x_1962_;
v_x_1944_ = v___x_1964_;
goto _start;
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1967_ = lean_array_fset(v_ks_1947_, v_x_1944_, v_x_1945_);
v___x_1968_ = lean_array_fset(v_vs_1948_, v_x_1944_, v_x_1946_);
lean_dec(v_x_1944_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v___x_1968_);
lean_ctor_set(v___x_1950_, 0, v___x_1967_);
v___x_1970_ = v___x_1950_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_1973_, lean_object* v_k_1974_, lean_object* v_v_1975_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_1973_, v___x_1976_, v_k_1974_, v_v_1975_);
return v___x_1977_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1979_, size_t v_x_1980_, size_t v_x_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_){
_start:
{
if (lean_obj_tag(v_x_1979_) == 0)
{
lean_object* v_es_1984_; size_t v___x_1985_; size_t v___x_1986_; lean_object* v_j_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v_es_1984_ = lean_ctor_get(v_x_1979_, 0);
v___x_1985_ = ((size_t)31ULL);
v___x_1986_ = lean_usize_land(v_x_1980_, v___x_1985_);
v_j_1987_ = lean_usize_to_nat(v___x_1986_);
v___x_1988_ = lean_array_get_size(v_es_1984_);
v___x_1989_ = lean_nat_dec_lt(v_j_1987_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_dec(v_j_1987_);
lean_dec(v_x_1983_);
lean_dec(v_x_1982_);
return v_x_1979_;
}
else
{
lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2028_; 
lean_inc_ref(v_es_1984_);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_x_1979_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v_x_1979_, 0);
lean_dec(v_unused_2029_);
v___x_1991_ = v_x_1979_;
v_isShared_1992_ = v_isSharedCheck_2028_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v_x_1979_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2028_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_v_1993_; lean_object* v___x_1994_; lean_object* v_xs_x27_1995_; lean_object* v___y_1997_; 
v_v_1993_ = lean_array_fget(v_es_1984_, v_j_1987_);
v___x_1994_ = lean_box(0);
v_xs_x27_1995_ = lean_array_fset(v_es_1984_, v_j_1987_, v___x_1994_);
switch(lean_obj_tag(v_v_1993_))
{
case 0:
{
lean_object* v_key_2002_; lean_object* v_val_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2013_; 
v_key_2002_ = lean_ctor_get(v_v_1993_, 0);
v_val_2003_ = lean_ctor_get(v_v_1993_, 1);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_v_1993_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2005_ = v_v_1993_;
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_val_2003_);
lean_inc(v_key_2002_);
lean_dec(v_v_1993_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2013_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
uint8_t v___x_2007_; 
v___x_2007_ = l_Lean_instBEqMVarId_beq(v_x_1982_, v_key_2002_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_del_object(v___x_2005_);
v___x_2008_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2002_, v_val_2003_, v_x_1982_, v_x_1983_);
v___x_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
v___y_1997_ = v___x_2009_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2011_; 
lean_dec(v_val_2003_);
lean_dec(v_key_2002_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v_x_1983_);
lean_ctor_set(v___x_2005_, 0, v_x_1982_);
v___x_2011_ = v___x_2005_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_x_1982_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_x_1983_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
v___y_1997_ = v___x_2011_;
goto v___jp_1996_;
}
}
}
}
case 1:
{
lean_object* v_node_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2026_; 
v_node_2014_ = lean_ctor_get(v_v_1993_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_v_1993_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2016_ = v_v_1993_;
v_isShared_2017_ = v_isSharedCheck_2026_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_node_2014_);
lean_dec(v_v_1993_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2026_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
size_t v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; size_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2018_ = ((size_t)5ULL);
v___x_2019_ = lean_usize_shift_right(v_x_1980_, v___x_2018_);
v___x_2020_ = ((size_t)1ULL);
v___x_2021_ = lean_usize_add(v_x_1981_, v___x_2020_);
v___x_2022_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_node_2014_, v___x_2019_, v___x_2021_, v_x_1982_, v_x_1983_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2022_);
v___x_2024_ = v___x_2016_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
v___y_1997_ = v___x_2024_;
goto v___jp_1996_;
}
}
}
default: 
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_x_1982_);
lean_ctor_set(v___x_2027_, 1, v_x_1983_);
v___y_1997_ = v___x_2027_;
goto v___jp_1996_;
}
}
v___jp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = lean_array_fset(v_xs_x27_1995_, v_j_1987_, v___y_1997_);
lean_dec(v_j_1987_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1998_);
v___x_2000_ = v___x_1991_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
else
{
lean_object* v_ks_2030_; lean_object* v_vs_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2051_; 
v_ks_2030_ = lean_ctor_get(v_x_1979_, 0);
v_vs_2031_ = lean_ctor_get(v_x_1979_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_x_1979_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2033_ = v_x_1979_;
v_isShared_2034_ = v_isSharedCheck_2051_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_vs_2031_);
lean_inc(v_ks_2030_);
lean_dec(v_x_1979_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2051_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_ks_2030_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_vs_2031_);
v___x_2036_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v_newNode_2037_; uint8_t v___y_2039_; size_t v___x_2045_; uint8_t v___x_2046_; 
v_newNode_2037_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_2036_, v_x_1982_, v_x_1983_);
v___x_2045_ = ((size_t)7ULL);
v___x_2046_ = lean_usize_dec_le(v___x_2045_, v_x_1981_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2047_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2037_);
v___x_2048_ = lean_unsigned_to_nat(4u);
v___x_2049_ = lean_nat_dec_lt(v___x_2047_, v___x_2048_);
lean_dec(v___x_2047_);
v___y_2039_ = v___x_2049_;
goto v___jp_2038_;
}
else
{
v___y_2039_ = v___x_2046_;
goto v___jp_2038_;
}
v___jp_2038_:
{
if (v___y_2039_ == 0)
{
lean_object* v_ks_2040_; lean_object* v_vs_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v_ks_2040_ = lean_ctor_get(v_newNode_2037_, 0);
lean_inc_ref(v_ks_2040_);
v_vs_2041_ = lean_ctor_get(v_newNode_2037_, 1);
lean_inc_ref(v_vs_2041_);
lean_dec_ref(v_newNode_2037_);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2044_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1981_, v_ks_2040_, v_vs_2041_, v___x_2042_, v___x_2043_);
lean_dec_ref(v_vs_2041_);
lean_dec_ref(v_ks_2040_);
return v___x_2044_;
}
else
{
return v_newNode_2037_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_2052_, lean_object* v_keys_2053_, lean_object* v_vals_2054_, lean_object* v_i_2055_, lean_object* v_entries_2056_){
_start:
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = lean_array_get_size(v_keys_2053_);
v___x_2058_ = lean_nat_dec_lt(v_i_2055_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_dec(v_i_2055_);
return v_entries_2056_;
}
else
{
lean_object* v_k_2059_; lean_object* v_v_2060_; uint64_t v___x_2061_; size_t v_h_2062_; size_t v___x_2063_; lean_object* v___x_2064_; size_t v___x_2065_; size_t v___x_2066_; size_t v___x_2067_; size_t v_h_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_k_2059_ = lean_array_fget_borrowed(v_keys_2053_, v_i_2055_);
v_v_2060_ = lean_array_fget_borrowed(v_vals_2054_, v_i_2055_);
v___x_2061_ = l_Lean_instHashableMVarId_hash(v_k_2059_);
v_h_2062_ = lean_uint64_to_usize(v___x_2061_);
v___x_2063_ = ((size_t)5ULL);
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = ((size_t)1ULL);
v___x_2066_ = lean_usize_sub(v_depth_2052_, v___x_2065_);
v___x_2067_ = lean_usize_mul(v___x_2063_, v___x_2066_);
v_h_2068_ = lean_usize_shift_right(v_h_2062_, v___x_2067_);
v___x_2069_ = lean_nat_add(v_i_2055_, v___x_2064_);
lean_dec(v_i_2055_);
lean_inc(v_v_2060_);
lean_inc(v_k_2059_);
v___x_2070_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_entries_2056_, v_h_2068_, v_depth_2052_, v_k_2059_, v_v_2060_);
v_i_2055_ = v___x_2069_;
v_entries_2056_ = v___x_2070_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_2072_, lean_object* v_keys_2073_, lean_object* v_vals_2074_, lean_object* v_i_2075_, lean_object* v_entries_2076_){
_start:
{
size_t v_depth_boxed_2077_; lean_object* v_res_2078_; 
v_depth_boxed_2077_ = lean_unbox_usize(v_depth_2072_);
lean_dec(v_depth_2072_);
v_res_2078_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_2077_, v_keys_2073_, v_vals_2074_, v_i_2075_, v_entries_2076_);
lean_dec_ref(v_vals_2074_);
lean_dec_ref(v_keys_2073_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2079_, lean_object* v_x_2080_, lean_object* v_x_2081_, lean_object* v_x_2082_, lean_object* v_x_2083_){
_start:
{
size_t v_x_3840__boxed_2084_; size_t v_x_3841__boxed_2085_; lean_object* v_res_2086_; 
v_x_3840__boxed_2084_ = lean_unbox_usize(v_x_2080_);
lean_dec(v_x_2080_);
v_x_3841__boxed_2085_ = lean_unbox_usize(v_x_2081_);
lean_dec(v_x_2081_);
v_res_2086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2079_, v_x_3840__boxed_2084_, v_x_3841__boxed_2085_, v_x_2082_, v_x_2083_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(lean_object* v_x_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_){
_start:
{
uint64_t v___x_2090_; size_t v___x_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v___x_2090_ = l_Lean_instHashableMVarId_hash(v_x_2088_);
v___x_2091_ = lean_uint64_to_usize(v___x_2090_);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2087_, v___x_2091_, v___x_2092_, v_x_2088_, v_x_2089_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object* v_mvarId_2094_, lean_object* v_val_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v_mctx_2099_; lean_object* v_cache_2100_; lean_object* v_zetaDeltaFVarIds_2101_; lean_object* v_postponed_2102_; lean_object* v_diag_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2131_; 
v___x_2098_ = lean_st_ref_take(v___y_2096_);
v_mctx_2099_ = lean_ctor_get(v___x_2098_, 0);
v_cache_2100_ = lean_ctor_get(v___x_2098_, 1);
v_zetaDeltaFVarIds_2101_ = lean_ctor_get(v___x_2098_, 2);
v_postponed_2102_ = lean_ctor_get(v___x_2098_, 3);
v_diag_2103_ = lean_ctor_get(v___x_2098_, 4);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2105_ = v___x_2098_;
v_isShared_2106_ = v_isSharedCheck_2131_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_diag_2103_);
lean_inc(v_postponed_2102_);
lean_inc(v_zetaDeltaFVarIds_2101_);
lean_inc(v_cache_2100_);
lean_inc(v_mctx_2099_);
lean_dec(v___x_2098_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2131_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_depth_2107_; lean_object* v_levelAssignDepth_2108_; lean_object* v_lmvarCounter_2109_; lean_object* v_mvarCounter_2110_; lean_object* v_lDecls_2111_; lean_object* v_decls_2112_; lean_object* v_userNames_2113_; lean_object* v_lAssignment_2114_; lean_object* v_eAssignment_2115_; lean_object* v_dAssignment_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2130_; 
v_depth_2107_ = lean_ctor_get(v_mctx_2099_, 0);
v_levelAssignDepth_2108_ = lean_ctor_get(v_mctx_2099_, 1);
v_lmvarCounter_2109_ = lean_ctor_get(v_mctx_2099_, 2);
v_mvarCounter_2110_ = lean_ctor_get(v_mctx_2099_, 3);
v_lDecls_2111_ = lean_ctor_get(v_mctx_2099_, 4);
v_decls_2112_ = lean_ctor_get(v_mctx_2099_, 5);
v_userNames_2113_ = lean_ctor_get(v_mctx_2099_, 6);
v_lAssignment_2114_ = lean_ctor_get(v_mctx_2099_, 7);
v_eAssignment_2115_ = lean_ctor_get(v_mctx_2099_, 8);
v_dAssignment_2116_ = lean_ctor_get(v_mctx_2099_, 9);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_mctx_2099_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2118_ = v_mctx_2099_;
v_isShared_2119_ = v_isSharedCheck_2130_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_dAssignment_2116_);
lean_inc(v_eAssignment_2115_);
lean_inc(v_lAssignment_2114_);
lean_inc(v_userNames_2113_);
lean_inc(v_decls_2112_);
lean_inc(v_lDecls_2111_);
lean_inc(v_mvarCounter_2110_);
lean_inc(v_lmvarCounter_2109_);
lean_inc(v_levelAssignDepth_2108_);
lean_inc(v_depth_2107_);
lean_dec(v_mctx_2099_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2130_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_eAssignment_2115_, v_mvarId_2094_, v_val_2095_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 8, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_depth_2107_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_levelAssignDepth_2108_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_lmvarCounter_2109_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_mvarCounter_2110_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_lDecls_2111_);
lean_ctor_set(v_reuseFailAlloc_2129_, 5, v_decls_2112_);
lean_ctor_set(v_reuseFailAlloc_2129_, 6, v_userNames_2113_);
lean_ctor_set(v_reuseFailAlloc_2129_, 7, v_lAssignment_2114_);
lean_ctor_set(v_reuseFailAlloc_2129_, 8, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2129_, 9, v_dAssignment_2116_);
v___x_2122_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2124_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2122_);
v___x_2124_ = v___x_2105_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_cache_2100_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_zetaDeltaFVarIds_2101_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_postponed_2102_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v_diag_2103_);
v___x_2124_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_st_ref_set(v___y_2096_, v___x_2124_);
v___x_2126_ = lean_box(0);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg___boxed(lean_object* v_mvarId_2132_, lean_object* v_val_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_mvarId_2132_, v_val_2133_, v___y_2134_);
lean_dec(v___y_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(lean_object* v_msgData_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; lean_object* v_env_2144_; lean_object* v___x_2145_; lean_object* v_mctx_2146_; lean_object* v_lctx_2147_; lean_object* v_options_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2143_ = lean_st_ref_get(v___y_2141_);
v_env_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc_ref(v_env_2144_);
lean_dec(v___x_2143_);
v___x_2145_ = lean_st_ref_get(v___y_2139_);
v_mctx_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc_ref(v_mctx_2146_);
lean_dec(v___x_2145_);
v_lctx_2147_ = lean_ctor_get(v___y_2138_, 2);
v_options_2148_ = lean_ctor_get(v___y_2140_, 2);
lean_inc_ref(v_options_2148_);
lean_inc_ref(v_lctx_2147_);
v___x_2149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2149_, 0, v_env_2144_);
lean_ctor_set(v___x_2149_, 1, v_mctx_2146_);
lean_ctor_set(v___x_2149_, 2, v_lctx_2147_);
lean_ctor_set(v___x_2149_, 3, v_options_2148_);
v___x_2150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v_msgData_2137_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2___boxed(lean_object* v_msgData_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msgData_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(lean_object* v_msg_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_ref_2165_; lean_object* v___x_2166_; lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2175_; 
v_ref_2165_ = lean_ctor_get(v___y_2162_, 5);
v___x_2166_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2175_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2175_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
lean_inc(v_ref_2165_);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_ref_2165_);
lean_ctor_set(v___x_2171_, 1, v_a_2167_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set_tag(v___x_2169_, 1);
lean_ctor_set(v___x_2169_, 0, v___x_2171_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg___boxed(lean_object* v_msg_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v_msg_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
return v_res_2182_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__0));
v___x_2185_ = l_Lean_stringToMessageData(v___x_2184_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__2));
v___x_2188_ = l_Lean_stringToMessageData(v___x_2187_);
return v___x_2188_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__4));
v___x_2191_ = l_Lean_stringToMessageData(v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1(lean_object* v_stx_2192_, lean_object* v_tagSuffix_2193_, uint8_t v_allowNaturalHoles_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Elab_Tactic_getMainTarget(v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
v___x_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2206_, 0, v_a_2205_);
v___x_2207_ = lean_box(0);
v___x_2208_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_stx_2192_, v___x_2206_, v_tagSuffix_2193_, v_allowNaturalHoles_2194_, v___x_2207_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v_fst_2210_; lean_object* v_snd_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2257_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v_fst_2210_ = lean_ctor_get(v_a_2209_, 0);
v_snd_2211_ = lean_ctor_get(v_a_2209_, 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_a_2209_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2213_ = v_a_2209_;
v_isShared_2214_ = v_isSharedCheck_2257_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_snd_2211_);
lean_inc(v_fst_2210_);
lean_dec(v_a_2209_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2257_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2196_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v_a_2218_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___x_2230_; uint8_t v___x_2244_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc_n(v_a_2216_, 2);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_fst_2210_, v___y_2200_);
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref(v___x_2217_);
v___x_2230_ = l_Lean_mkMVar(v_a_2216_);
v___x_2244_ = lean_expr_eqv(v_a_2218_, v___x_2230_);
if (v___x_2244_ == 0)
{
lean_object* v___f_2245_; lean_object* v___x_2246_; 
lean_inc(v_a_2216_);
v___f_2245_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2245_, 0, v_a_2216_);
lean_inc(v_a_2218_);
v___x_2246_ = l_Lean_FindMVar_main(v___f_2245_, v_a_2218_, v___x_2207_);
if (lean_obj_tag(v___x_2246_) == 1)
{
lean_dec_ref_known(v___x_2246_, 1);
lean_dec(v_a_2216_);
lean_dec(v_snd_2211_);
goto v___jp_2231_;
}
else
{
lean_dec(v___x_2246_);
if (v___x_2244_ == 0)
{
lean_dec_ref(v___x_2230_);
lean_del_object(v___x_2213_);
v___y_2220_ = v___y_2195_;
v___y_2221_ = v___y_2196_;
v___y_2222_ = v___y_2197_;
v___y_2223_ = v___y_2198_;
v___y_2224_ = v___y_2199_;
v___y_2225_ = v___y_2200_;
v___y_2226_ = v___y_2201_;
v___y_2227_ = v___y_2202_;
goto v___jp_2219_;
}
else
{
lean_dec(v_a_2216_);
lean_dec(v_snd_2211_);
goto v___jp_2231_;
}
}
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec_ref(v___x_2230_);
lean_dec(v_a_2218_);
lean_del_object(v___x_2213_);
v___x_2247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_a_2216_);
lean_ctor_set(v___x_2247_, 1, v_snd_2211_);
v___x_2248_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2247_, v___y_2196_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2248_;
}
v___jp_2219_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_a_2216_, v_a_2218_, v___y_2225_);
lean_dec_ref(v___x_2228_);
v___x_2229_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_snd_2211_, v___y_2221_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2229_;
}
v___jp_2231_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2232_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__1, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1);
v___x_2233_ = l_Lean_indentExpr(v_a_2218_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set_tag(v___x_2213_, 7);
lean_ctor_set(v___x_2213_, 1, v___x_2233_);
lean_ctor_set(v___x_2213_, 0, v___x_2232_);
v___x_2235_ = v___x_2213_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2236_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__3, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_MessageData_ofExpr(v___x_2230_);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_2241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2241_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_del_object(v___x_2213_);
lean_dec(v_snd_2211_);
lean_dec(v_fst_2210_);
v_a_2249_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2215_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2215_);
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
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
v_a_2258_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2208_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2208_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_tagSuffix_2193_);
lean_dec(v_stx_2192_);
v_a_2266_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2204_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2204_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___boxed(lean_object* v_stx_2274_, lean_object* v_tagSuffix_2275_, lean_object* v_allowNaturalHoles_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_2286_; lean_object* v_res_2287_; 
v_allowNaturalHoles_boxed_2286_ = lean_unbox(v_allowNaturalHoles_2276_);
v_res_2287_ = l_Lean_Elab_Tactic_refineCore___lam__1(v_stx_2274_, v_tagSuffix_2275_, v_allowNaturalHoles_boxed_2286_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object* v_stx_2288_, lean_object* v_tagSuffix_2289_, uint8_t v_allowNaturalHoles_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v___x_2300_; lean_object* v___f_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_box(v_allowNaturalHoles_2290_);
v___f_2301_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__1___boxed), 12, 3);
lean_closure_set(v___f_2301_, 0, v_stx_2288_);
lean_closure_set(v___f_2301_, 1, v_tagSuffix_2289_);
lean_closure_set(v___f_2301_, 2, v___x_2300_);
v___x_2302_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2301_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object* v_stx_2303_, lean_object* v_tagSuffix_2304_, lean_object* v_allowNaturalHoles_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_2315_; lean_object* v_res_2316_; 
v_allowNaturalHoles_boxed_2315_ = lean_unbox(v_allowNaturalHoles_2305_);
v_res_2316_ = l_Lean_Elab_Tactic_refineCore(v_stx_2303_, v_tagSuffix_2304_, v_allowNaturalHoles_boxed_2315_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(lean_object* v_mvarId_2317_, lean_object* v_val_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_mvarId_2317_, v_val_2318_, v___y_2324_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___boxed(lean_object* v_mvarId_2329_, lean_object* v_val_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(v_mvarId_2329_, v_val_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(lean_object* v_00_u03b1_2341_, lean_object* v_msg_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v_msg_2342_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___boxed(lean_object* v_00_u03b1_2353_, lean_object* v_msg_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(v_00_u03b1_2353_, v_msg_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0(lean_object* v_00_u03b2_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_x_2366_, v_x_2367_, v_x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2370_, lean_object* v_x_2371_, size_t v_x_2372_, size_t v_x_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2371_, v_x_2372_, v_x_2373_, v_x_2374_, v_x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
size_t v_x_4390__boxed_2383_; size_t v_x_4391__boxed_2384_; lean_object* v_res_2385_; 
v_x_4390__boxed_2383_ = lean_unbox_usize(v_x_2379_);
lean_dec(v_x_2379_);
v_x_4391__boxed_2384_ = lean_unbox_usize(v_x_2380_);
lean_dec(v_x_2380_);
v_res_2385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(v_00_u03b2_2377_, v_x_2378_, v_x_4390__boxed_2383_, v_x_4391__boxed_2384_, v_x_2381_, v_x_2382_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2386_, lean_object* v_n_2387_, lean_object* v_k_2388_, lean_object* v_v_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_2387_, v_k_2388_, v_v_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2391_, size_t v_depth_2392_, lean_object* v_keys_2393_, lean_object* v_vals_2394_, lean_object* v_heq_2395_, lean_object* v_i_2396_, lean_object* v_entries_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_2392_, v_keys_2393_, v_vals_2394_, v_i_2396_, v_entries_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2399_, lean_object* v_depth_2400_, lean_object* v_keys_2401_, lean_object* v_vals_2402_, lean_object* v_heq_2403_, lean_object* v_i_2404_, lean_object* v_entries_2405_){
_start:
{
size_t v_depth_boxed_2406_; lean_object* v_res_2407_; 
v_depth_boxed_2406_ = lean_unbox_usize(v_depth_2400_);
lean_dec(v_depth_2400_);
v_res_2407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_2399_, v_depth_boxed_2406_, v_keys_2401_, v_vals_2402_, v_heq_2403_, v_i_2404_, v_entries_2405_);
lean_dec_ref(v_vals_2402_);
lean_dec_ref(v_keys_2401_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_2408_, lean_object* v_x_2409_, lean_object* v_x_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_2409_, v_x_2410_, v_x_2411_, v_x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object* v_stx_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__1));
lean_inc(v_stx_2422_);
v___x_2433_ = l_Lean_Syntax_isOfKind(v_stx_2422_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; 
lean_dec(v_stx_2422_);
v___x_2434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2434_;
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; 
v___x_2435_ = lean_unsigned_to_nat(1u);
v___x_2436_ = l_Lean_Syntax_getArg(v_stx_2422_, v___x_2435_);
lean_dec(v_stx_2422_);
v___x_2437_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__2));
v___x_2438_ = 0;
v___x_2439_ = l_Lean_Elab_Tactic_refineCore(v___x_2436_, v___x_2437_, v___x_2438_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
return v___x_2439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___boxed(lean_object* v_stx_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Elab_Tactic_evalRefine(v_stx_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1(){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2458_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2459_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__1));
v___x_2460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1));
v___x_2461_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine___boxed), 10, 0);
v___x_2462_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2458_, v___x_2459_, v___x_2460_, v___x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___boxed(lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3(){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1));
v___x_2492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6));
v___x_2493_ = l_Lean_addBuiltinDeclarationRanges(v___x_2491_, v___x_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___boxed(lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object* v_stx_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__1));
lean_inc(v_stx_2504_);
v___x_2515_ = l_Lean_Syntax_isOfKind(v_stx_2504_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; 
lean_dec(v_stx_2504_);
v___x_2516_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2517_ = lean_unsigned_to_nat(1u);
v___x_2518_ = l_Lean_Syntax_getArg(v_stx_2504_, v___x_2517_);
lean_dec(v_stx_2504_);
v___x_2519_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__2));
v___x_2520_ = l_Lean_Elab_Tactic_refineCore(v___x_2518_, v___x_2519_, v___x_2515_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
return v___x_2520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___boxed(lean_object* v_stx_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_Elab_Tactic_evalRefine_x27(v_stx_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2539_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2540_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__1));
v___x_2541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1));
v___x_2542_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine_x27___boxed), 10, 0);
v___x_2543_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2539_, v___x_2540_, v___x_2541_, v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___boxed(lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3(){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1));
v___x_2573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6));
v___x_2574_ = l_Lean_addBuiltinDeclarationRanges(v___x_2572_, v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___boxed(lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
return v_res_2576_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0));
v___x_2579_ = l_Lean_stringToMessageData(v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0(uint8_t v___x_2580_, lean_object* v_stx_2581_, lean_object* v___x_2582_, uint8_t v___x_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
if (v___x_2580_ == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref(v___x_2582_);
v___x_2593_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2593_;
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2594_ = lean_unsigned_to_nat(1u);
v___x_2595_ = l_Lean_Syntax_getArg(v_stx_2581_, v___x_2594_);
v___x_2596_ = lean_box(0);
v___x_2597_ = l_Lean_Name_mkStr1(v___x_2582_);
v___x_2598_ = l_Lean_Elab_Tactic_elabTermWithHoles(v___x_2595_, v___x_2596_, v___x_2597_, v___x_2583_, v___x_2596_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v_fst_2600_; lean_object* v_snd_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2649_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v_fst_2600_ = lean_ctor_get(v_a_2599_, 0);
v_snd_2601_ = lean_ctor_get(v_a_2599_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_a_2599_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2603_ = v_a_2599_;
v_isShared_2604_ = v_isSharedCheck_2649_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_snd_2601_);
lean_inc(v_fst_2600_);
lean_dec(v_a_2599_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2649_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = l_Lean_Expr_getLambdaBody(v_fst_2600_);
v___x_2606_ = l_Lean_Expr_getAppFn(v___x_2605_);
lean_dec_ref(v___x_2605_);
if (lean_obj_tag(v___x_2606_) == 1)
{
lean_object* v_fvarId_2607_; lean_object* v___x_2608_; 
v_fvarId_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_fvarId_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2585_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2610_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v_fst_2600_);
v___x_2610_ = lean_infer_type(v_fst_2600_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = l_Lean_Expr_headBeta(v_a_2611_);
v___x_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
v___x_2614_ = l_Lean_MVarId_replace(v_a_2609_, v_fvarId_2607_, v_fst_2600_, v___x_2613_, v___x_2596_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v_mvarId_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v_mvarId_2616_ = lean_ctor_get(v_a_2615_, 1);
lean_inc(v_mvarId_2616_);
lean_dec(v_a_2615_);
v___x_2617_ = lean_box(0);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 1, v___x_2617_);
lean_ctor_set(v___x_2603_, 0, v_mvarId_2616_);
v___x_2619_ = v___x_2603_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_mvarId_2616_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = l_List_appendTR___redArg(v_snd_2601_, v___x_2619_);
v___x_2621_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2620_, v___y_2585_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
return v___x_2621_;
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_del_object(v___x_2603_);
lean_dec(v_snd_2601_);
v_a_2623_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2614_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2614_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec(v_a_2609_);
lean_dec(v_fvarId_2607_);
lean_del_object(v___x_2603_);
lean_dec(v_snd_2601_);
lean_dec(v_fst_2600_);
v_a_2631_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2610_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2610_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v_fvarId_2607_);
lean_del_object(v___x_2603_);
lean_dec(v_snd_2601_);
lean_dec(v_fst_2600_);
v_a_2639_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2608_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2608_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec_ref(v___x_2606_);
lean_del_object(v___x_2603_);
lean_dec(v_snd_2601_);
lean_dec(v_fst_2600_);
v___x_2647_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1, &l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1);
v___x_2648_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2647_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
return v___x_2648_;
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_a_2650_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2598_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2598_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed(lean_object* v___x_2658_, lean_object* v_stx_2659_, lean_object* v___x_2660_, lean_object* v___x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
uint8_t v___x_1129__boxed_2671_; uint8_t v___x_1131__boxed_2672_; lean_object* v_res_2673_; 
v___x_1129__boxed_2671_ = lean_unbox(v___x_2658_);
v___x_1131__boxed_2672_ = lean_unbox(v___x_2661_);
v_res_2673_ = l_Lean_Elab_Tactic_evalSpecialize___lam__0(v___x_1129__boxed_2671_, v_stx_2659_, v___x_2660_, v___x_1131__boxed_2672_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v_stx_2659_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object* v_stx_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___y_2696_; lean_object* v___x_2697_; 
v___x_2690_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__0));
v___x_2691_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__1));
lean_inc(v_stx_2680_);
v___x_2692_ = l_Lean_Syntax_isOfKind(v_stx_2680_, v___x_2691_);
v___x_2693_ = 1;
v___x_2694_ = lean_box(v___x_2692_);
v___x_2695_ = lean_box(v___x_2693_);
v___y_2696_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed), 13, 4);
lean_closure_set(v___y_2696_, 0, v___x_2694_);
lean_closure_set(v___y_2696_, 1, v_stx_2680_);
lean_closure_set(v___y_2696_, 2, v___x_2690_);
lean_closure_set(v___y_2696_, 3, v___x_2695_);
v___x_2697_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_2696_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___boxed(lean_object* v_stx_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_Elab_Tactic_evalSpecialize(v_stx_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2716_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2717_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__1));
v___x_2718_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1));
v___x_2719_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___boxed), 10, 0);
v___x_2720_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2716_, v___x_2717_, v___x_2718_, v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___boxed(lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3(){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1));
v___x_2749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6));
v___x_2750_ = l_Lean_addBuiltinDeclarationRanges(v___x_2748_, v___x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___boxed(lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object* v_stx_2754_, uint8_t v_mayPostpone_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; uint8_t v___x_2776_; 
v___x_2776_ = l_Lean_Syntax_isIdent(v_stx_2754_);
if (v___x_2776_ == 0)
{
v___y_2766_ = v_a_2756_;
v___y_2767_ = v_a_2757_;
v___y_2768_ = v_a_2758_;
v___y_2769_ = v_a_2759_;
v___y_2770_ = v_a_2760_;
v___y_2771_ = v_a_2761_;
v___y_2772_ = v_a_2762_;
v___y_2773_ = v_a_2763_;
goto v___jp_2765_;
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = ((lean_object*)(l_Lean_Elab_Tactic_elabTermForApply___closed__0));
lean_inc(v_stx_2754_);
v___x_2778_ = l_Lean_Elab_Term_resolveId_x3f(v_stx_2754_, v___x_2777_, v___x_2776_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2787_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2787_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2787_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
if (lean_obj_tag(v_a_2779_) == 1)
{
lean_object* v_val_2783_; lean_object* v___x_2785_; 
lean_dec(v_stx_2754_);
v_val_2783_ = lean_ctor_get(v_a_2779_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v_a_2779_, 1);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v_val_2783_);
v___x_2785_ = v___x_2781_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_val_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
else
{
lean_del_object(v___x_2781_);
lean_dec(v_a_2779_);
v___y_2766_ = v_a_2756_;
v___y_2767_ = v_a_2757_;
v___y_2768_ = v_a_2758_;
v___y_2769_ = v_a_2759_;
v___y_2770_ = v_a_2760_;
v___y_2771_ = v_a_2761_;
v___y_2772_ = v_a_2762_;
v___y_2773_ = v_a_2763_;
goto v___jp_2765_;
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_stx_2754_);
v_a_2788_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2778_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2778_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
v___jp_2765_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_box(0);
v___x_2775_ = l_Lean_Elab_Tactic_elabTerm(v_stx_2754_, v___x_2774_, v_mayPostpone_2755_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object* v_stx_2796_, lean_object* v_mayPostpone_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
uint8_t v_mayPostpone_boxed_2807_; lean_object* v_res_2808_; 
v_mayPostpone_boxed_2807_ = lean_unbox(v_mayPostpone_2797_);
v_res_2808_ = l_Lean_Elab_Tactic_elabTermForApply(v_stx_2796_, v_mayPostpone_boxed_2807_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
return v_res_2808_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0));
v___x_2811_ = l_Lean_stringToMessageData(v___x_2810_);
return v___x_2811_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2));
v___x_2814_ = l_Lean_stringToMessageData(v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0(lean_object* v___x_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2840_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2840_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2840_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
if (lean_obj_tag(v_a_2826_) == 1)
{
lean_object* v_fvarId_2830_; lean_object* v___x_2832_; 
v_fvarId_2830_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_fvarId_2830_);
lean_dec_ref_known(v_a_2826_, 1);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v_fvarId_2830_);
v___x_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_fvarId_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_del_object(v___x_2828_);
v___x_2834_ = lean_obj_once(&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1, &l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1);
v___x_2835_ = l_Lean_MessageData_ofExpr(v_a_2826_);
v___x_2836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = lean_obj_once(&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3, &l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2838_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
return v___x_2839_;
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
v_a_2841_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2825_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2825_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___boxed(lean_object* v___x_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_Elab_Tactic_getFVarId___lam__0(v___x_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object* v_id_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_fileName_2870_; lean_object* v_fileMap_2871_; lean_object* v_options_2872_; lean_object* v_currRecDepth_2873_; lean_object* v_maxRecDepth_2874_; lean_object* v_ref_2875_; lean_object* v_currNamespace_2876_; lean_object* v_openDecls_2877_; lean_object* v_initHeartbeats_2878_; lean_object* v_maxHeartbeats_2879_; lean_object* v_quotContext_2880_; lean_object* v_currMacroScope_2881_; uint8_t v_diag_2882_; lean_object* v_cancelTk_x3f_2883_; uint8_t v_suppressElabErrors_2884_; lean_object* v_inheritedTraceOptions_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___f_2889_; lean_object* v_ref_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_fileName_2870_ = lean_ctor_get(v_a_2867_, 0);
v_fileMap_2871_ = lean_ctor_get(v_a_2867_, 1);
v_options_2872_ = lean_ctor_get(v_a_2867_, 2);
v_currRecDepth_2873_ = lean_ctor_get(v_a_2867_, 3);
v_maxRecDepth_2874_ = lean_ctor_get(v_a_2867_, 4);
v_ref_2875_ = lean_ctor_get(v_a_2867_, 5);
v_currNamespace_2876_ = lean_ctor_get(v_a_2867_, 6);
v_openDecls_2877_ = lean_ctor_get(v_a_2867_, 7);
v_initHeartbeats_2878_ = lean_ctor_get(v_a_2867_, 8);
v_maxHeartbeats_2879_ = lean_ctor_get(v_a_2867_, 9);
v_quotContext_2880_ = lean_ctor_get(v_a_2867_, 10);
v_currMacroScope_2881_ = lean_ctor_get(v_a_2867_, 11);
v_diag_2882_ = lean_ctor_get_uint8(v_a_2867_, sizeof(void*)*14);
v_cancelTk_x3f_2883_ = lean_ctor_get(v_a_2867_, 12);
v_suppressElabErrors_2884_ = lean_ctor_get_uint8(v_a_2867_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2885_ = lean_ctor_get(v_a_2867_, 13);
v___x_2886_ = 0;
v___x_2887_ = lean_box(v___x_2886_);
lean_inc(v_id_2860_);
v___x_2888_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(v___x_2888_, 0, v_id_2860_);
lean_closure_set(v___x_2888_, 1, v___x_2887_);
v___f_2889_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2889_, 0, v___x_2888_);
v_ref_2890_ = l_Lean_replaceRef(v_id_2860_, v_ref_2875_);
lean_dec(v_id_2860_);
lean_inc_ref(v_inheritedTraceOptions_2885_);
lean_inc(v_cancelTk_x3f_2883_);
lean_inc(v_currMacroScope_2881_);
lean_inc(v_quotContext_2880_);
lean_inc(v_maxHeartbeats_2879_);
lean_inc(v_initHeartbeats_2878_);
lean_inc(v_openDecls_2877_);
lean_inc(v_currNamespace_2876_);
lean_inc(v_maxRecDepth_2874_);
lean_inc(v_currRecDepth_2873_);
lean_inc_ref(v_options_2872_);
lean_inc_ref(v_fileMap_2871_);
lean_inc_ref(v_fileName_2870_);
v___x_2891_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2891_, 0, v_fileName_2870_);
lean_ctor_set(v___x_2891_, 1, v_fileMap_2871_);
lean_ctor_set(v___x_2891_, 2, v_options_2872_);
lean_ctor_set(v___x_2891_, 3, v_currRecDepth_2873_);
lean_ctor_set(v___x_2891_, 4, v_maxRecDepth_2874_);
lean_ctor_set(v___x_2891_, 5, v_ref_2890_);
lean_ctor_set(v___x_2891_, 6, v_currNamespace_2876_);
lean_ctor_set(v___x_2891_, 7, v_openDecls_2877_);
lean_ctor_set(v___x_2891_, 8, v_initHeartbeats_2878_);
lean_ctor_set(v___x_2891_, 9, v_maxHeartbeats_2879_);
lean_ctor_set(v___x_2891_, 10, v_quotContext_2880_);
lean_ctor_set(v___x_2891_, 11, v_currMacroScope_2881_);
lean_ctor_set(v___x_2891_, 12, v_cancelTk_x3f_2883_);
lean_ctor_set(v___x_2891_, 13, v_inheritedTraceOptions_2885_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*14, v_diag_2882_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*14 + 1, v_suppressElabErrors_2884_);
v___x_2892_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2889_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v___x_2891_, v_a_2868_);
lean_dec_ref_known(v___x_2891_, 14);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object* v_id_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Elab_Tactic_getFVarId(v_id_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(size_t v_sz_2904_, size_t v_i_2905_, lean_object* v_bs_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = lean_usize_dec_lt(v_i_2905_, v_sz_2904_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_bs_2906_);
return v___x_2917_;
}
else
{
lean_object* v_v_2918_; lean_object* v___x_2919_; 
v_v_2918_ = lean_array_uget_borrowed(v_bs_2906_, v_i_2905_);
lean_inc(v_v_2918_);
v___x_2919_ = l_Lean_Elab_Tactic_getFVarId(v_v_2918_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; lean_object* v_bs_x27_2922_; size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___x_2921_ = lean_unsigned_to_nat(0u);
v_bs_x27_2922_ = lean_array_uset(v_bs_2906_, v_i_2905_, v___x_2921_);
v___x_2923_ = ((size_t)1ULL);
v___x_2924_ = lean_usize_add(v_i_2905_, v___x_2923_);
v___x_2925_ = lean_array_uset(v_bs_x27_2922_, v_i_2905_, v_a_2920_);
v_i_2905_ = v___x_2924_;
v_bs_2906_ = v___x_2925_;
goto _start;
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v_bs_2906_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed(lean_object* v_sz_2935_, lean_object* v_i_2936_, lean_object* v_bs_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
size_t v_sz_boxed_2947_; size_t v_i_boxed_2948_; lean_object* v_res_2949_; 
v_sz_boxed_2947_ = lean_unbox_usize(v_sz_2935_);
lean_dec(v_sz_2935_);
v_i_boxed_2948_ = lean_unbox_usize(v_i_2936_);
lean_dec(v_i_2936_);
v_res_2949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(v_sz_boxed_2947_, v_i_boxed_2948_, v_bs_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object* v_ids_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
size_t v_sz_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_sz_2962_ = lean_array_size(v_ids_2952_);
v___x_2963_ = lean_box_usize(v_sz_2962_);
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarIds___boxed__const__1));
v___x_2965_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed), 12, 3);
lean_closure_set(v___x_2965_, 0, v___x_2963_);
lean_closure_set(v___x_2965_, 1, v___x_2964_);
lean_closure_set(v___x_2965_, 2, v_ids_2952_);
v___x_2966_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2965_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed(lean_object* v_ids_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lean_Elab_Tactic_getFVarIds(v_ids_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_a_2973_);
lean_dec_ref(v_a_2972_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object* v_e_2978_, uint8_t v___x_2979_, lean_object* v_tac_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_val_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_Elab_Tactic_elabTermForApply(v_e_2978_, v___x_2979_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; lean_object* v_a_3025_; uint8_t v___x_3026_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v___x_3024_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_3023_, v___y_2986_);
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref(v___x_3024_);
v___x_3026_ = l_Lean_Expr_isMVar(v_a_3025_);
if (v___x_3026_ == 0)
{
v_val_2991_ = v_a_3025_;
v___y_2992_ = v___y_2982_;
v___y_2993_ = v___y_2983_;
v___y_2994_ = v___y_2984_;
v___y_2995_ = v___y_2985_;
v___y_2996_ = v___y_2986_;
v___y_2997_ = v___y_2987_;
v___y_2998_ = v___y_2988_;
goto v___jp_2990_;
}
else
{
uint8_t v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = 0;
v___x_3028_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_3027_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v___x_3029_; lean_object* v_a_3030_; 
lean_dec_ref_known(v___x_3028_, 1);
v___x_3029_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_3025_, v___y_2986_);
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref(v___x_3029_);
v_val_2991_ = v_a_3030_;
v___y_2992_ = v___y_2982_;
v___y_2993_ = v___y_2983_;
v___y_2994_ = v___y_2984_;
v___y_2995_ = v___y_2985_;
v___y_2996_ = v___y_2986_;
v___y_2997_ = v___y_2987_;
v___y_2998_ = v___y_2988_;
goto v___jp_2990_;
}
else
{
lean_dec(v_a_3025_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec_ref(v_tac_2980_);
return v___x_3028_;
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec_ref(v_tac_2980_);
v_a_3031_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3022_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3022_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
v___jp_2990_:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2992_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
lean_inc(v___y_2998_);
lean_inc_ref(v___y_2997_);
lean_inc(v___y_2996_);
lean_inc_ref(v___y_2995_);
v___x_3001_ = lean_apply_7(v_tac_2980_, v_a_3000_, v_val_2991_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, lean_box(0));
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = 0;
v___x_3004_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_3003_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3005_; 
lean_dec_ref_known(v___x_3004_, 1);
v___x_3005_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3002_, v___y_2992_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
return v___x_3005_;
}
else
{
lean_dec(v_a_3002_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
return v___x_3004_;
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
v_a_3006_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_3001_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3001_);
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
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v_val_2991_);
lean_dec_ref(v_tac_2980_);
v_a_3014_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2999_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2999_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(lean_object* v_e_3039_, lean_object* v___x_3040_, lean_object* v_tac_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
uint8_t v___x_977__boxed_3051_; lean_object* v_res_3052_; 
v___x_977__boxed_3051_ = lean_unbox(v___x_3040_);
v_res_3052_ = l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(v_e_3039_, v___x_977__boxed_3051_, v_tac_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object* v_tac_3053_, lean_object* v_e_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
uint8_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; 
v___x_3064_ = 1;
v___x_3065_ = lean_box(v___x_3064_);
v___f_3066_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3066_, 0, v_e_3054_);
lean_closure_set(v___f_3066_, 1, v___x_3065_);
lean_closure_set(v___f_3066_, 2, v_tac_3053_);
v___x_3067_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3066_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___boxed(lean_object* v_tac_3068_, lean_object* v_e_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v_tac_3068_, v_e_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0(uint8_t v___x_3080_, lean_object* v_g_3081_, lean_object* v_e_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
uint8_t v___x_3088_; uint8_t v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3088_ = 0;
v___x_3089_ = 0;
v___x_3090_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3090_, 0, v___x_3088_);
lean_ctor_set_uint8(v___x_3090_, 1, v___x_3080_);
lean_ctor_set_uint8(v___x_3090_, 2, v___x_3089_);
lean_ctor_set_uint8(v___x_3090_, 3, v___x_3080_);
v___x_3091_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
lean_inc_ref(v_e_3082_);
v___x_3092_ = l_Lean_MessageData_ofExpr(v_e_3082_);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v___x_3091_);
v___x_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
v___x_3096_ = l_Lean_MVarId_apply(v_g_3081_, v_e_3082_, v___x_3090_, v___x_3095_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___boxed(lean_object* v___x_3097_, lean_object* v_g_3098_, lean_object* v_e_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
uint8_t v___x_233__boxed_3105_; lean_object* v_res_3106_; 
v___x_233__boxed_3105_ = lean_unbox(v___x_3097_);
v_res_3106_ = l_Lean_Elab_Tactic_evalApply___lam__0(v___x_233__boxed_3105_, v_g_3098_, v_e_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object* v_stx_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
lean_inc(v_stx_3113_);
v___x_3124_ = l_Lean_Syntax_isOfKind(v_stx_3113_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
lean_dec(v_stx_3113_);
v___x_3125_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; lean_object* v___f_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3126_ = lean_box(v___x_3124_);
v___f_3127_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3127_, 0, v___x_3126_);
v___x_3128_ = lean_unsigned_to_nat(1u);
v___x_3129_ = l_Lean_Syntax_getArg(v_stx_3113_, v___x_3128_);
lean_dec(v_stx_3113_);
v___x_3130_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v___f_3127_, v___x_3129_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_);
return v___x_3130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___boxed(lean_object* v_stx_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_Elab_Tactic_evalApply(v_stx_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1(){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3149_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3150_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
v___x_3151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3152_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___boxed), 10, 0);
v___x_3153_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3149_, v___x_3150_, v___x_3151_, v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___boxed(lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3(){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6));
v___x_3184_ = l_Lean_addBuiltinDeclarationRanges(v___x_3182_, v___x_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___boxed(lean_object* v_a_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3192_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; uint8_t v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v___x_3202_ = 0;
v___x_3203_ = ((lean_object*)(l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0));
v___x_3204_ = l_Lean_MVarId_constructor(v_a_3201_, v___x_3203_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3204_, 1);
v___x_3206_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_3202_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v___x_3207_; 
lean_dec_ref_known(v___x_3206_, 1);
v___x_3207_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3205_, v___y_3192_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
return v___x_3207_;
}
else
{
lean_dec(v_a_3205_);
return v___x_3206_;
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
v_a_3208_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3204_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3204_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
v_a_3216_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3200_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3200_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___boxed(lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg(lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v___f_3244_; lean_object* v___x_3245_; 
v___f_3244_ = ((lean_object*)(l_Lean_Elab_Tactic_evalConstructor___redArg___closed__0));
v___x_3245_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3244_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___boxed(lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lean_Elab_Tactic_evalConstructor___redArg(v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object* v_x_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l_Lean_Elab_Tactic_evalConstructor___redArg(v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object* v_x_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_Elab_Tactic_evalConstructor(v_x_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_x_3267_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3291_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1));
v___x_3293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_3294_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___boxed), 10, 0);
v___x_3295_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3291_, v___x_3292_, v___x_3293_, v___x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___boxed(lean_object* v_a_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3(){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_3325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6));
v___x_3326_ = l_Lean_addBuiltinDeclarationRanges(v___x_3324_, v___x_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___boxed(lean_object* v_a_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
return v_res_3328_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithReducible___closed__0(void){
_start:
{
uint8_t v___x_3329_; uint64_t v___x_3330_; 
v___x_3329_ = 2;
v___x_3330_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object* v_stx_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v___x_3341_; uint8_t v_foApprox_3342_; uint8_t v_ctxApprox_3343_; uint8_t v_quasiPatternApprox_3344_; uint8_t v_constApprox_3345_; uint8_t v_isDefEqStuckEx_3346_; uint8_t v_unificationHints_3347_; uint8_t v_proofIrrelevance_3348_; uint8_t v_assignSyntheticOpaque_3349_; uint8_t v_offsetCnstrs_3350_; uint8_t v_etaStruct_3351_; uint8_t v_univApprox_3352_; uint8_t v_iota_3353_; uint8_t v_beta_3354_; uint8_t v_proj_3355_; uint8_t v_zeta_3356_; uint8_t v_zetaDelta_3357_; uint8_t v_zetaUnused_3358_; uint8_t v_zetaHave_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3396_; 
v___x_3341_ = l_Lean_Meta_Context_config(v_a_3336_);
v_foApprox_3342_ = lean_ctor_get_uint8(v___x_3341_, 0);
v_ctxApprox_3343_ = lean_ctor_get_uint8(v___x_3341_, 1);
v_quasiPatternApprox_3344_ = lean_ctor_get_uint8(v___x_3341_, 2);
v_constApprox_3345_ = lean_ctor_get_uint8(v___x_3341_, 3);
v_isDefEqStuckEx_3346_ = lean_ctor_get_uint8(v___x_3341_, 4);
v_unificationHints_3347_ = lean_ctor_get_uint8(v___x_3341_, 5);
v_proofIrrelevance_3348_ = lean_ctor_get_uint8(v___x_3341_, 6);
v_assignSyntheticOpaque_3349_ = lean_ctor_get_uint8(v___x_3341_, 7);
v_offsetCnstrs_3350_ = lean_ctor_get_uint8(v___x_3341_, 8);
v_etaStruct_3351_ = lean_ctor_get_uint8(v___x_3341_, 10);
v_univApprox_3352_ = lean_ctor_get_uint8(v___x_3341_, 11);
v_iota_3353_ = lean_ctor_get_uint8(v___x_3341_, 12);
v_beta_3354_ = lean_ctor_get_uint8(v___x_3341_, 13);
v_proj_3355_ = lean_ctor_get_uint8(v___x_3341_, 14);
v_zeta_3356_ = lean_ctor_get_uint8(v___x_3341_, 15);
v_zetaDelta_3357_ = lean_ctor_get_uint8(v___x_3341_, 16);
v_zetaUnused_3358_ = lean_ctor_get_uint8(v___x_3341_, 17);
v_zetaHave_3359_ = lean_ctor_get_uint8(v___x_3341_, 18);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3361_ = v___x_3341_;
v_isShared_3362_ = v_isSharedCheck_3396_;
goto v_resetjp_3360_;
}
else
{
lean_dec(v___x_3341_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3396_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
uint8_t v_trackZetaDelta_3363_; lean_object* v_zetaDeltaSet_3364_; lean_object* v_lctx_3365_; lean_object* v_localInstances_3366_; lean_object* v_defEqCtx_x3f_3367_; lean_object* v_synthPendingDepth_3368_; lean_object* v_canUnfold_x3f_3369_; uint8_t v_univApprox_3370_; uint8_t v_inTypeClassResolution_3371_; uint8_t v_cacheInferType_3372_; uint8_t v___x_3373_; lean_object* v_config_3375_; 
v_trackZetaDelta_3363_ = lean_ctor_get_uint8(v_a_3336_, sizeof(void*)*7);
v_zetaDeltaSet_3364_ = lean_ctor_get(v_a_3336_, 1);
v_lctx_3365_ = lean_ctor_get(v_a_3336_, 2);
v_localInstances_3366_ = lean_ctor_get(v_a_3336_, 3);
v_defEqCtx_x3f_3367_ = lean_ctor_get(v_a_3336_, 4);
v_synthPendingDepth_3368_ = lean_ctor_get(v_a_3336_, 5);
v_canUnfold_x3f_3369_ = lean_ctor_get(v_a_3336_, 6);
v_univApprox_3370_ = lean_ctor_get_uint8(v_a_3336_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3371_ = lean_ctor_get_uint8(v_a_3336_, sizeof(void*)*7 + 2);
v_cacheInferType_3372_ = lean_ctor_get_uint8(v_a_3336_, sizeof(void*)*7 + 3);
v___x_3373_ = 2;
if (v_isShared_3362_ == 0)
{
v_config_3375_ = v___x_3361_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 0, v_foApprox_3342_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 1, v_ctxApprox_3343_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 2, v_quasiPatternApprox_3344_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 3, v_constApprox_3345_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 4, v_isDefEqStuckEx_3346_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 5, v_unificationHints_3347_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 6, v_proofIrrelevance_3348_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 7, v_assignSyntheticOpaque_3349_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 8, v_offsetCnstrs_3350_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 10, v_etaStruct_3351_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 11, v_univApprox_3352_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 12, v_iota_3353_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 13, v_beta_3354_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 14, v_proj_3355_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 15, v_zeta_3356_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 16, v_zetaDelta_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 17, v_zetaUnused_3358_);
lean_ctor_set_uint8(v_reuseFailAlloc_3395_, 18, v_zetaHave_3359_);
v_config_3375_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
uint64_t v___x_3376_; uint64_t v___x_3377_; uint64_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint64_t v___x_3381_; uint64_t v___x_3382_; uint64_t v_key_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_ctor_set_uint8(v_config_3375_, 9, v___x_3373_);
v___x_3376_ = l_Lean_Meta_Context_configKey(v_a_3336_);
v___x_3377_ = 3ULL;
v___x_3378_ = lean_uint64_shift_right(v___x_3376_, v___x_3377_);
v___x_3379_ = lean_unsigned_to_nat(1u);
v___x_3380_ = l_Lean_Syntax_getArg(v_stx_3331_, v___x_3379_);
v___x_3381_ = lean_uint64_shift_left(v___x_3378_, v___x_3377_);
v___x_3382_ = lean_uint64_once(&l_Lean_Elab_Tactic_evalWithReducible___closed__0, &l_Lean_Elab_Tactic_evalWithReducible___closed__0_once, _init_l_Lean_Elab_Tactic_evalWithReducible___closed__0);
v_key_3383_ = lean_uint64_lor(v___x_3381_, v___x_3382_);
v___x_3384_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3384_, 0, v_config_3375_);
lean_ctor_set_uint64(v___x_3384_, sizeof(void*)*1, v_key_3383_);
lean_inc(v_canUnfold_x3f_3369_);
lean_inc(v_synthPendingDepth_3368_);
lean_inc(v_defEqCtx_x3f_3367_);
lean_inc_ref(v_localInstances_3366_);
lean_inc_ref(v_lctx_3365_);
lean_inc(v_zetaDeltaSet_3364_);
v___x_3385_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
lean_ctor_set(v___x_3385_, 1, v_zetaDeltaSet_3364_);
lean_ctor_set(v___x_3385_, 2, v_lctx_3365_);
lean_ctor_set(v___x_3385_, 3, v_localInstances_3366_);
lean_ctor_set(v___x_3385_, 4, v_defEqCtx_x3f_3367_);
lean_ctor_set(v___x_3385_, 5, v_synthPendingDepth_3368_);
lean_ctor_set(v___x_3385_, 6, v_canUnfold_x3f_3369_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*7, v_trackZetaDelta_3363_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*7 + 1, v_univApprox_3370_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3371_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*7 + 3, v_cacheInferType_3372_);
v___x_3386_ = l_Lean_Elab_Tactic_evalTactic(v___x_3380_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v___x_3385_, v_a_3337_, v_a_3338_, v_a_3339_);
lean_dec_ref_known(v___x_3385_, 7);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
else
{
return v___x_3386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object* v_stx_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Elab_Tactic_evalWithReducible(v_stx_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_stx_3397_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3421_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1));
v___x_3423_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_3424_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducible___boxed), 10, 0);
v___x_3425_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3421_, v___x_3422_, v___x_3423_, v___x_3424_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___boxed(lean_object* v_a_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3(){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_3455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6));
v___x_3456_ = l_Lean_addBuiltinDeclarationRanges(v___x_3454_, v___x_3455_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___boxed(lean_object* v_a_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
return v_res_3458_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0(void){
_start:
{
uint8_t v___x_3459_; uint64_t v___x_3460_; 
v___x_3459_ = 3;
v___x_3460_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object* v_stx_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v___x_3471_; uint8_t v_foApprox_3472_; uint8_t v_ctxApprox_3473_; uint8_t v_quasiPatternApprox_3474_; uint8_t v_constApprox_3475_; uint8_t v_isDefEqStuckEx_3476_; uint8_t v_unificationHints_3477_; uint8_t v_proofIrrelevance_3478_; uint8_t v_assignSyntheticOpaque_3479_; uint8_t v_offsetCnstrs_3480_; uint8_t v_etaStruct_3481_; uint8_t v_univApprox_3482_; uint8_t v_iota_3483_; uint8_t v_beta_3484_; uint8_t v_proj_3485_; uint8_t v_zeta_3486_; uint8_t v_zetaDelta_3487_; uint8_t v_zetaUnused_3488_; uint8_t v_zetaHave_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3526_; 
v___x_3471_ = l_Lean_Meta_Context_config(v_a_3466_);
v_foApprox_3472_ = lean_ctor_get_uint8(v___x_3471_, 0);
v_ctxApprox_3473_ = lean_ctor_get_uint8(v___x_3471_, 1);
v_quasiPatternApprox_3474_ = lean_ctor_get_uint8(v___x_3471_, 2);
v_constApprox_3475_ = lean_ctor_get_uint8(v___x_3471_, 3);
v_isDefEqStuckEx_3476_ = lean_ctor_get_uint8(v___x_3471_, 4);
v_unificationHints_3477_ = lean_ctor_get_uint8(v___x_3471_, 5);
v_proofIrrelevance_3478_ = lean_ctor_get_uint8(v___x_3471_, 6);
v_assignSyntheticOpaque_3479_ = lean_ctor_get_uint8(v___x_3471_, 7);
v_offsetCnstrs_3480_ = lean_ctor_get_uint8(v___x_3471_, 8);
v_etaStruct_3481_ = lean_ctor_get_uint8(v___x_3471_, 10);
v_univApprox_3482_ = lean_ctor_get_uint8(v___x_3471_, 11);
v_iota_3483_ = lean_ctor_get_uint8(v___x_3471_, 12);
v_beta_3484_ = lean_ctor_get_uint8(v___x_3471_, 13);
v_proj_3485_ = lean_ctor_get_uint8(v___x_3471_, 14);
v_zeta_3486_ = lean_ctor_get_uint8(v___x_3471_, 15);
v_zetaDelta_3487_ = lean_ctor_get_uint8(v___x_3471_, 16);
v_zetaUnused_3488_ = lean_ctor_get_uint8(v___x_3471_, 17);
v_zetaHave_3489_ = lean_ctor_get_uint8(v___x_3471_, 18);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3491_ = v___x_3471_;
v_isShared_3492_ = v_isSharedCheck_3526_;
goto v_resetjp_3490_;
}
else
{
lean_dec(v___x_3471_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3526_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
uint8_t v_trackZetaDelta_3493_; lean_object* v_zetaDeltaSet_3494_; lean_object* v_lctx_3495_; lean_object* v_localInstances_3496_; lean_object* v_defEqCtx_x3f_3497_; lean_object* v_synthPendingDepth_3498_; lean_object* v_canUnfold_x3f_3499_; uint8_t v_univApprox_3500_; uint8_t v_inTypeClassResolution_3501_; uint8_t v_cacheInferType_3502_; uint8_t v___x_3503_; lean_object* v_config_3505_; 
v_trackZetaDelta_3493_ = lean_ctor_get_uint8(v_a_3466_, sizeof(void*)*7);
v_zetaDeltaSet_3494_ = lean_ctor_get(v_a_3466_, 1);
v_lctx_3495_ = lean_ctor_get(v_a_3466_, 2);
v_localInstances_3496_ = lean_ctor_get(v_a_3466_, 3);
v_defEqCtx_x3f_3497_ = lean_ctor_get(v_a_3466_, 4);
v_synthPendingDepth_3498_ = lean_ctor_get(v_a_3466_, 5);
v_canUnfold_x3f_3499_ = lean_ctor_get(v_a_3466_, 6);
v_univApprox_3500_ = lean_ctor_get_uint8(v_a_3466_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3501_ = lean_ctor_get_uint8(v_a_3466_, sizeof(void*)*7 + 2);
v_cacheInferType_3502_ = lean_ctor_get_uint8(v_a_3466_, sizeof(void*)*7 + 3);
v___x_3503_ = 3;
if (v_isShared_3492_ == 0)
{
v_config_3505_ = v___x_3491_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 0, v_foApprox_3472_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 1, v_ctxApprox_3473_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 2, v_quasiPatternApprox_3474_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 3, v_constApprox_3475_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 4, v_isDefEqStuckEx_3476_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 5, v_unificationHints_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 6, v_proofIrrelevance_3478_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 7, v_assignSyntheticOpaque_3479_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 8, v_offsetCnstrs_3480_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 10, v_etaStruct_3481_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 11, v_univApprox_3482_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 12, v_iota_3483_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 13, v_beta_3484_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 14, v_proj_3485_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 15, v_zeta_3486_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 16, v_zetaDelta_3487_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 17, v_zetaUnused_3488_);
lean_ctor_set_uint8(v_reuseFailAlloc_3525_, 18, v_zetaHave_3489_);
v_config_3505_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
uint64_t v___x_3506_; uint64_t v___x_3507_; uint64_t v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; uint64_t v___x_3511_; uint64_t v___x_3512_; uint64_t v_key_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
lean_ctor_set_uint8(v_config_3505_, 9, v___x_3503_);
v___x_3506_ = l_Lean_Meta_Context_configKey(v_a_3466_);
v___x_3507_ = 3ULL;
v___x_3508_ = lean_uint64_shift_right(v___x_3506_, v___x_3507_);
v___x_3509_ = lean_unsigned_to_nat(1u);
v___x_3510_ = l_Lean_Syntax_getArg(v_stx_3461_, v___x_3509_);
v___x_3511_ = lean_uint64_shift_left(v___x_3508_, v___x_3507_);
v___x_3512_ = lean_uint64_once(&l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0, &l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0_once, _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0);
v_key_3513_ = lean_uint64_lor(v___x_3511_, v___x_3512_);
v___x_3514_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3514_, 0, v_config_3505_);
lean_ctor_set_uint64(v___x_3514_, sizeof(void*)*1, v_key_3513_);
lean_inc(v_canUnfold_x3f_3499_);
lean_inc(v_synthPendingDepth_3498_);
lean_inc(v_defEqCtx_x3f_3497_);
lean_inc_ref(v_localInstances_3496_);
lean_inc_ref(v_lctx_3495_);
lean_inc(v_zetaDeltaSet_3494_);
v___x_3515_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
lean_ctor_set(v___x_3515_, 1, v_zetaDeltaSet_3494_);
lean_ctor_set(v___x_3515_, 2, v_lctx_3495_);
lean_ctor_set(v___x_3515_, 3, v_localInstances_3496_);
lean_ctor_set(v___x_3515_, 4, v_defEqCtx_x3f_3497_);
lean_ctor_set(v___x_3515_, 5, v_synthPendingDepth_3498_);
lean_ctor_set(v___x_3515_, 6, v_canUnfold_x3f_3499_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*7, v_trackZetaDelta_3493_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*7 + 1, v_univApprox_3500_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3501_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*7 + 3, v_cacheInferType_3502_);
v___x_3516_ = l_Lean_Elab_Tactic_evalTactic(v___x_3510_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v___x_3515_, v_a_3467_, v_a_3468_, v_a_3469_);
lean_dec_ref_known(v___x_3515_, 7);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
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
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
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
else
{
return v___x_3516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object* v_stx_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Elab_Tactic_evalWithReducibleAndInstances(v_stx_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec(v_stx_3527_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3551_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1));
v___x_3553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_3554_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed), 10, 0);
v___x_3555_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3551_, v___x_3552_, v___x_3553_, v___x_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___boxed(lean_object* v_a_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3(){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3584_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_3585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6));
v___x_3586_ = l_Lean_addBuiltinDeclarationRanges(v___x_3584_, v___x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___boxed(lean_object* v_a_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
return v_res_3588_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithImplicit___closed__0(void){
_start:
{
uint8_t v___x_3589_; uint64_t v___x_3590_; 
v___x_3589_ = 5;
v___x_3590_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit(lean_object* v_stx_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v___x_3601_; uint8_t v_foApprox_3602_; uint8_t v_ctxApprox_3603_; uint8_t v_quasiPatternApprox_3604_; uint8_t v_constApprox_3605_; uint8_t v_isDefEqStuckEx_3606_; uint8_t v_unificationHints_3607_; uint8_t v_proofIrrelevance_3608_; uint8_t v_assignSyntheticOpaque_3609_; uint8_t v_offsetCnstrs_3610_; uint8_t v_etaStruct_3611_; uint8_t v_univApprox_3612_; uint8_t v_iota_3613_; uint8_t v_beta_3614_; uint8_t v_proj_3615_; uint8_t v_zeta_3616_; uint8_t v_zetaDelta_3617_; uint8_t v_zetaUnused_3618_; uint8_t v_zetaHave_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3656_; 
v___x_3601_ = l_Lean_Meta_Context_config(v_a_3596_);
v_foApprox_3602_ = lean_ctor_get_uint8(v___x_3601_, 0);
v_ctxApprox_3603_ = lean_ctor_get_uint8(v___x_3601_, 1);
v_quasiPatternApprox_3604_ = lean_ctor_get_uint8(v___x_3601_, 2);
v_constApprox_3605_ = lean_ctor_get_uint8(v___x_3601_, 3);
v_isDefEqStuckEx_3606_ = lean_ctor_get_uint8(v___x_3601_, 4);
v_unificationHints_3607_ = lean_ctor_get_uint8(v___x_3601_, 5);
v_proofIrrelevance_3608_ = lean_ctor_get_uint8(v___x_3601_, 6);
v_assignSyntheticOpaque_3609_ = lean_ctor_get_uint8(v___x_3601_, 7);
v_offsetCnstrs_3610_ = lean_ctor_get_uint8(v___x_3601_, 8);
v_etaStruct_3611_ = lean_ctor_get_uint8(v___x_3601_, 10);
v_univApprox_3612_ = lean_ctor_get_uint8(v___x_3601_, 11);
v_iota_3613_ = lean_ctor_get_uint8(v___x_3601_, 12);
v_beta_3614_ = lean_ctor_get_uint8(v___x_3601_, 13);
v_proj_3615_ = lean_ctor_get_uint8(v___x_3601_, 14);
v_zeta_3616_ = lean_ctor_get_uint8(v___x_3601_, 15);
v_zetaDelta_3617_ = lean_ctor_get_uint8(v___x_3601_, 16);
v_zetaUnused_3618_ = lean_ctor_get_uint8(v___x_3601_, 17);
v_zetaHave_3619_ = lean_ctor_get_uint8(v___x_3601_, 18);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3621_ = v___x_3601_;
v_isShared_3622_ = v_isSharedCheck_3656_;
goto v_resetjp_3620_;
}
else
{
lean_dec(v___x_3601_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3656_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
uint8_t v_trackZetaDelta_3623_; lean_object* v_zetaDeltaSet_3624_; lean_object* v_lctx_3625_; lean_object* v_localInstances_3626_; lean_object* v_defEqCtx_x3f_3627_; lean_object* v_synthPendingDepth_3628_; lean_object* v_canUnfold_x3f_3629_; uint8_t v_univApprox_3630_; uint8_t v_inTypeClassResolution_3631_; uint8_t v_cacheInferType_3632_; uint8_t v___x_3633_; lean_object* v_config_3635_; 
v_trackZetaDelta_3623_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*7);
v_zetaDeltaSet_3624_ = lean_ctor_get(v_a_3596_, 1);
v_lctx_3625_ = lean_ctor_get(v_a_3596_, 2);
v_localInstances_3626_ = lean_ctor_get(v_a_3596_, 3);
v_defEqCtx_x3f_3627_ = lean_ctor_get(v_a_3596_, 4);
v_synthPendingDepth_3628_ = lean_ctor_get(v_a_3596_, 5);
v_canUnfold_x3f_3629_ = lean_ctor_get(v_a_3596_, 6);
v_univApprox_3630_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3631_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*7 + 2);
v_cacheInferType_3632_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*7 + 3);
v___x_3633_ = 5;
if (v_isShared_3622_ == 0)
{
v_config_3635_ = v___x_3621_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 0, v_foApprox_3602_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 1, v_ctxApprox_3603_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 2, v_quasiPatternApprox_3604_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 3, v_constApprox_3605_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 4, v_isDefEqStuckEx_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 5, v_unificationHints_3607_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 6, v_proofIrrelevance_3608_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 7, v_assignSyntheticOpaque_3609_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 8, v_offsetCnstrs_3610_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 10, v_etaStruct_3611_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 11, v_univApprox_3612_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 12, v_iota_3613_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 13, v_beta_3614_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 14, v_proj_3615_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 15, v_zeta_3616_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 16, v_zetaDelta_3617_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 17, v_zetaUnused_3618_);
lean_ctor_set_uint8(v_reuseFailAlloc_3655_, 18, v_zetaHave_3619_);
v_config_3635_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
uint64_t v___x_3636_; uint64_t v___x_3637_; uint64_t v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; uint64_t v___x_3641_; uint64_t v___x_3642_; uint64_t v_key_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_ctor_set_uint8(v_config_3635_, 9, v___x_3633_);
v___x_3636_ = l_Lean_Meta_Context_configKey(v_a_3596_);
v___x_3637_ = 3ULL;
v___x_3638_ = lean_uint64_shift_right(v___x_3636_, v___x_3637_);
v___x_3639_ = lean_unsigned_to_nat(1u);
v___x_3640_ = l_Lean_Syntax_getArg(v_stx_3591_, v___x_3639_);
v___x_3641_ = lean_uint64_shift_left(v___x_3638_, v___x_3637_);
v___x_3642_ = lean_uint64_once(&l_Lean_Elab_Tactic_evalWithImplicit___closed__0, &l_Lean_Elab_Tactic_evalWithImplicit___closed__0_once, _init_l_Lean_Elab_Tactic_evalWithImplicit___closed__0);
v_key_3643_ = lean_uint64_lor(v___x_3641_, v___x_3642_);
v___x_3644_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3644_, 0, v_config_3635_);
lean_ctor_set_uint64(v___x_3644_, sizeof(void*)*1, v_key_3643_);
lean_inc(v_canUnfold_x3f_3629_);
lean_inc(v_synthPendingDepth_3628_);
lean_inc(v_defEqCtx_x3f_3627_);
lean_inc_ref(v_localInstances_3626_);
lean_inc_ref(v_lctx_3625_);
lean_inc(v_zetaDeltaSet_3624_);
v___x_3645_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
lean_ctor_set(v___x_3645_, 1, v_zetaDeltaSet_3624_);
lean_ctor_set(v___x_3645_, 2, v_lctx_3625_);
lean_ctor_set(v___x_3645_, 3, v_localInstances_3626_);
lean_ctor_set(v___x_3645_, 4, v_defEqCtx_x3f_3627_);
lean_ctor_set(v___x_3645_, 5, v_synthPendingDepth_3628_);
lean_ctor_set(v___x_3645_, 6, v_canUnfold_x3f_3629_);
lean_ctor_set_uint8(v___x_3645_, sizeof(void*)*7, v_trackZetaDelta_3623_);
lean_ctor_set_uint8(v___x_3645_, sizeof(void*)*7 + 1, v_univApprox_3630_);
lean_ctor_set_uint8(v___x_3645_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3631_);
lean_ctor_set_uint8(v___x_3645_, sizeof(void*)*7 + 3, v_cacheInferType_3632_);
v___x_3646_ = l_Lean_Elab_Tactic_evalTactic(v___x_3640_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v___x_3645_, v_a_3597_, v_a_3598_, v_a_3599_);
lean_dec_ref_known(v___x_3645_, 7);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
else
{
return v___x_3646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithImplicit___boxed(lean_object* v_stx_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Elab_Tactic_evalWithImplicit(v_stx_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
lean_dec(v_a_3659_);
lean_dec_ref(v_a_3658_);
lean_dec(v_stx_3657_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1(){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3681_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__1));
v___x_3683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___closed__3));
v___x_3684_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithImplicit___boxed), 10, 0);
v___x_3685_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3681_, v___x_3682_, v___x_3683_, v___x_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1___boxed(lean_object* v_a_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1();
return v_res_3687_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0(void){
_start:
{
uint8_t v___x_3688_; uint64_t v___x_3689_; 
v___x_3688_ = 0;
v___x_3689_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object* v_stx_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v___x_3700_; uint8_t v_foApprox_3701_; uint8_t v_ctxApprox_3702_; uint8_t v_quasiPatternApprox_3703_; uint8_t v_constApprox_3704_; uint8_t v_isDefEqStuckEx_3705_; uint8_t v_unificationHints_3706_; uint8_t v_proofIrrelevance_3707_; uint8_t v_assignSyntheticOpaque_3708_; uint8_t v_offsetCnstrs_3709_; uint8_t v_etaStruct_3710_; uint8_t v_univApprox_3711_; uint8_t v_iota_3712_; uint8_t v_beta_3713_; uint8_t v_proj_3714_; uint8_t v_zeta_3715_; uint8_t v_zetaDelta_3716_; uint8_t v_zetaUnused_3717_; uint8_t v_zetaHave_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3755_; 
v___x_3700_ = l_Lean_Meta_Context_config(v_a_3695_);
v_foApprox_3701_ = lean_ctor_get_uint8(v___x_3700_, 0);
v_ctxApprox_3702_ = lean_ctor_get_uint8(v___x_3700_, 1);
v_quasiPatternApprox_3703_ = lean_ctor_get_uint8(v___x_3700_, 2);
v_constApprox_3704_ = lean_ctor_get_uint8(v___x_3700_, 3);
v_isDefEqStuckEx_3705_ = lean_ctor_get_uint8(v___x_3700_, 4);
v_unificationHints_3706_ = lean_ctor_get_uint8(v___x_3700_, 5);
v_proofIrrelevance_3707_ = lean_ctor_get_uint8(v___x_3700_, 6);
v_assignSyntheticOpaque_3708_ = lean_ctor_get_uint8(v___x_3700_, 7);
v_offsetCnstrs_3709_ = lean_ctor_get_uint8(v___x_3700_, 8);
v_etaStruct_3710_ = lean_ctor_get_uint8(v___x_3700_, 10);
v_univApprox_3711_ = lean_ctor_get_uint8(v___x_3700_, 11);
v_iota_3712_ = lean_ctor_get_uint8(v___x_3700_, 12);
v_beta_3713_ = lean_ctor_get_uint8(v___x_3700_, 13);
v_proj_3714_ = lean_ctor_get_uint8(v___x_3700_, 14);
v_zeta_3715_ = lean_ctor_get_uint8(v___x_3700_, 15);
v_zetaDelta_3716_ = lean_ctor_get_uint8(v___x_3700_, 16);
v_zetaUnused_3717_ = lean_ctor_get_uint8(v___x_3700_, 17);
v_zetaHave_3718_ = lean_ctor_get_uint8(v___x_3700_, 18);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3720_ = v___x_3700_;
v_isShared_3721_ = v_isSharedCheck_3755_;
goto v_resetjp_3719_;
}
else
{
lean_dec(v___x_3700_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3755_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
uint8_t v_trackZetaDelta_3722_; lean_object* v_zetaDeltaSet_3723_; lean_object* v_lctx_3724_; lean_object* v_localInstances_3725_; lean_object* v_defEqCtx_x3f_3726_; lean_object* v_synthPendingDepth_3727_; lean_object* v_canUnfold_x3f_3728_; uint8_t v_univApprox_3729_; uint8_t v_inTypeClassResolution_3730_; uint8_t v_cacheInferType_3731_; uint8_t v___x_3732_; lean_object* v_config_3734_; 
v_trackZetaDelta_3722_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*7);
v_zetaDeltaSet_3723_ = lean_ctor_get(v_a_3695_, 1);
v_lctx_3724_ = lean_ctor_get(v_a_3695_, 2);
v_localInstances_3725_ = lean_ctor_get(v_a_3695_, 3);
v_defEqCtx_x3f_3726_ = lean_ctor_get(v_a_3695_, 4);
v_synthPendingDepth_3727_ = lean_ctor_get(v_a_3695_, 5);
v_canUnfold_x3f_3728_ = lean_ctor_get(v_a_3695_, 6);
v_univApprox_3729_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3730_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*7 + 2);
v_cacheInferType_3731_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*7 + 3);
v___x_3732_ = 0;
if (v_isShared_3721_ == 0)
{
v_config_3734_ = v___x_3720_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 0, v_foApprox_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 1, v_ctxApprox_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 2, v_quasiPatternApprox_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 3, v_constApprox_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 4, v_isDefEqStuckEx_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 5, v_unificationHints_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 6, v_proofIrrelevance_3707_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 7, v_assignSyntheticOpaque_3708_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 8, v_offsetCnstrs_3709_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 10, v_etaStruct_3710_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 11, v_univApprox_3711_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 12, v_iota_3712_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 13, v_beta_3713_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 14, v_proj_3714_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 15, v_zeta_3715_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 16, v_zetaDelta_3716_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 17, v_zetaUnused_3717_);
lean_ctor_set_uint8(v_reuseFailAlloc_3754_, 18, v_zetaHave_3718_);
v_config_3734_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
uint64_t v___x_3735_; uint64_t v___x_3736_; uint64_t v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; uint64_t v___x_3740_; uint64_t v___x_3741_; uint64_t v_key_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_ctor_set_uint8(v_config_3734_, 9, v___x_3732_);
v___x_3735_ = l_Lean_Meta_Context_configKey(v_a_3695_);
v___x_3736_ = 3ULL;
v___x_3737_ = lean_uint64_shift_right(v___x_3735_, v___x_3736_);
v___x_3738_ = lean_unsigned_to_nat(1u);
v___x_3739_ = l_Lean_Syntax_getArg(v_stx_3690_, v___x_3738_);
v___x_3740_ = lean_uint64_shift_left(v___x_3737_, v___x_3736_);
v___x_3741_ = lean_uint64_once(&l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0, &l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0_once, _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0);
v_key_3742_ = lean_uint64_lor(v___x_3740_, v___x_3741_);
v___x_3743_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3743_, 0, v_config_3734_);
lean_ctor_set_uint64(v___x_3743_, sizeof(void*)*1, v_key_3742_);
lean_inc(v_canUnfold_x3f_3728_);
lean_inc(v_synthPendingDepth_3727_);
lean_inc(v_defEqCtx_x3f_3726_);
lean_inc_ref(v_localInstances_3725_);
lean_inc_ref(v_lctx_3724_);
lean_inc(v_zetaDeltaSet_3723_);
v___x_3744_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
lean_ctor_set(v___x_3744_, 1, v_zetaDeltaSet_3723_);
lean_ctor_set(v___x_3744_, 2, v_lctx_3724_);
lean_ctor_set(v___x_3744_, 3, v_localInstances_3725_);
lean_ctor_set(v___x_3744_, 4, v_defEqCtx_x3f_3726_);
lean_ctor_set(v___x_3744_, 5, v_synthPendingDepth_3727_);
lean_ctor_set(v___x_3744_, 6, v_canUnfold_x3f_3728_);
lean_ctor_set_uint8(v___x_3744_, sizeof(void*)*7, v_trackZetaDelta_3722_);
lean_ctor_set_uint8(v___x_3744_, sizeof(void*)*7 + 1, v_univApprox_3729_);
lean_ctor_set_uint8(v___x_3744_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3730_);
lean_ctor_set_uint8(v___x_3744_, sizeof(void*)*7 + 3, v_cacheInferType_3731_);
v___x_3745_ = l_Lean_Elab_Tactic_evalTactic(v___x_3739_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v___x_3744_, v_a_3696_, v_a_3697_, v_a_3698_);
lean_dec_ref_known(v___x_3744_, 7);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
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
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
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
else
{
return v___x_3745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object* v_stx_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_Elab_Tactic_evalWithUnfoldingAll(v_stx_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_stx_3756_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3780_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1));
v___x_3782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_3783_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed), 10, 0);
v___x_3784_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3780_, v___x_3781_, v___x_3782_, v___x_3783_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___boxed(lean_object* v_a_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3(){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_3814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6));
v___x_3815_ = l_Lean_addBuiltinDeclarationRanges(v___x_3813_, v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___boxed(lean_object* v_a_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
return v_res_3817_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0(void){
_start:
{
uint8_t v___x_3818_; uint64_t v___x_3819_; 
v___x_3818_ = 4;
v___x_3819_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3818_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone(lean_object* v_stx_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v___x_3830_; uint8_t v_foApprox_3831_; uint8_t v_ctxApprox_3832_; uint8_t v_quasiPatternApprox_3833_; uint8_t v_constApprox_3834_; uint8_t v_isDefEqStuckEx_3835_; uint8_t v_unificationHints_3836_; uint8_t v_proofIrrelevance_3837_; uint8_t v_assignSyntheticOpaque_3838_; uint8_t v_offsetCnstrs_3839_; uint8_t v_etaStruct_3840_; uint8_t v_univApprox_3841_; uint8_t v_iota_3842_; uint8_t v_beta_3843_; uint8_t v_proj_3844_; uint8_t v_zeta_3845_; uint8_t v_zetaDelta_3846_; uint8_t v_zetaUnused_3847_; uint8_t v_zetaHave_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3885_; 
v___x_3830_ = l_Lean_Meta_Context_config(v_a_3825_);
v_foApprox_3831_ = lean_ctor_get_uint8(v___x_3830_, 0);
v_ctxApprox_3832_ = lean_ctor_get_uint8(v___x_3830_, 1);
v_quasiPatternApprox_3833_ = lean_ctor_get_uint8(v___x_3830_, 2);
v_constApprox_3834_ = lean_ctor_get_uint8(v___x_3830_, 3);
v_isDefEqStuckEx_3835_ = lean_ctor_get_uint8(v___x_3830_, 4);
v_unificationHints_3836_ = lean_ctor_get_uint8(v___x_3830_, 5);
v_proofIrrelevance_3837_ = lean_ctor_get_uint8(v___x_3830_, 6);
v_assignSyntheticOpaque_3838_ = lean_ctor_get_uint8(v___x_3830_, 7);
v_offsetCnstrs_3839_ = lean_ctor_get_uint8(v___x_3830_, 8);
v_etaStruct_3840_ = lean_ctor_get_uint8(v___x_3830_, 10);
v_univApprox_3841_ = lean_ctor_get_uint8(v___x_3830_, 11);
v_iota_3842_ = lean_ctor_get_uint8(v___x_3830_, 12);
v_beta_3843_ = lean_ctor_get_uint8(v___x_3830_, 13);
v_proj_3844_ = lean_ctor_get_uint8(v___x_3830_, 14);
v_zeta_3845_ = lean_ctor_get_uint8(v___x_3830_, 15);
v_zetaDelta_3846_ = lean_ctor_get_uint8(v___x_3830_, 16);
v_zetaUnused_3847_ = lean_ctor_get_uint8(v___x_3830_, 17);
v_zetaHave_3848_ = lean_ctor_get_uint8(v___x_3830_, 18);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3850_ = v___x_3830_;
v_isShared_3851_ = v_isSharedCheck_3885_;
goto v_resetjp_3849_;
}
else
{
lean_dec(v___x_3830_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3885_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
uint8_t v_trackZetaDelta_3852_; lean_object* v_zetaDeltaSet_3853_; lean_object* v_lctx_3854_; lean_object* v_localInstances_3855_; lean_object* v_defEqCtx_x3f_3856_; lean_object* v_synthPendingDepth_3857_; lean_object* v_canUnfold_x3f_3858_; uint8_t v_univApprox_3859_; uint8_t v_inTypeClassResolution_3860_; uint8_t v_cacheInferType_3861_; uint8_t v___x_3862_; lean_object* v_config_3864_; 
v_trackZetaDelta_3852_ = lean_ctor_get_uint8(v_a_3825_, sizeof(void*)*7);
v_zetaDeltaSet_3853_ = lean_ctor_get(v_a_3825_, 1);
v_lctx_3854_ = lean_ctor_get(v_a_3825_, 2);
v_localInstances_3855_ = lean_ctor_get(v_a_3825_, 3);
v_defEqCtx_x3f_3856_ = lean_ctor_get(v_a_3825_, 4);
v_synthPendingDepth_3857_ = lean_ctor_get(v_a_3825_, 5);
v_canUnfold_x3f_3858_ = lean_ctor_get(v_a_3825_, 6);
v_univApprox_3859_ = lean_ctor_get_uint8(v_a_3825_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3860_ = lean_ctor_get_uint8(v_a_3825_, sizeof(void*)*7 + 2);
v_cacheInferType_3861_ = lean_ctor_get_uint8(v_a_3825_, sizeof(void*)*7 + 3);
v___x_3862_ = 4;
if (v_isShared_3851_ == 0)
{
v_config_3864_ = v___x_3850_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 0, v_foApprox_3831_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 1, v_ctxApprox_3832_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 2, v_quasiPatternApprox_3833_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 3, v_constApprox_3834_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 4, v_isDefEqStuckEx_3835_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 5, v_unificationHints_3836_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 6, v_proofIrrelevance_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 7, v_assignSyntheticOpaque_3838_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 8, v_offsetCnstrs_3839_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 10, v_etaStruct_3840_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 11, v_univApprox_3841_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 12, v_iota_3842_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 13, v_beta_3843_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 14, v_proj_3844_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 15, v_zeta_3845_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 16, v_zetaDelta_3846_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 17, v_zetaUnused_3847_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, 18, v_zetaHave_3848_);
v_config_3864_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
uint64_t v___x_3865_; uint64_t v___x_3866_; uint64_t v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; uint64_t v___x_3870_; uint64_t v___x_3871_; uint64_t v_key_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_ctor_set_uint8(v_config_3864_, 9, v___x_3862_);
v___x_3865_ = l_Lean_Meta_Context_configKey(v_a_3825_);
v___x_3866_ = 3ULL;
v___x_3867_ = lean_uint64_shift_right(v___x_3865_, v___x_3866_);
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = l_Lean_Syntax_getArg(v_stx_3820_, v___x_3868_);
v___x_3870_ = lean_uint64_shift_left(v___x_3867_, v___x_3866_);
v___x_3871_ = lean_uint64_once(&l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0, &l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0_once, _init_l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0);
v_key_3872_ = lean_uint64_lor(v___x_3870_, v___x_3871_);
v___x_3873_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3873_, 0, v_config_3864_);
lean_ctor_set_uint64(v___x_3873_, sizeof(void*)*1, v_key_3872_);
lean_inc(v_canUnfold_x3f_3858_);
lean_inc(v_synthPendingDepth_3857_);
lean_inc(v_defEqCtx_x3f_3856_);
lean_inc_ref(v_localInstances_3855_);
lean_inc_ref(v_lctx_3854_);
lean_inc(v_zetaDeltaSet_3853_);
v___x_3874_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
lean_ctor_set(v___x_3874_, 1, v_zetaDeltaSet_3853_);
lean_ctor_set(v___x_3874_, 2, v_lctx_3854_);
lean_ctor_set(v___x_3874_, 3, v_localInstances_3855_);
lean_ctor_set(v___x_3874_, 4, v_defEqCtx_x3f_3856_);
lean_ctor_set(v___x_3874_, 5, v_synthPendingDepth_3857_);
lean_ctor_set(v___x_3874_, 6, v_canUnfold_x3f_3858_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*7, v_trackZetaDelta_3852_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*7 + 1, v_univApprox_3859_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3860_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*7 + 3, v_cacheInferType_3861_);
v___x_3875_ = l_Lean_Elab_Tactic_evalTactic(v___x_3869_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v___x_3874_, v_a_3826_, v_a_3827_, v_a_3828_);
lean_dec_ref_known(v___x_3874_, 7);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3875_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3875_);
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
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
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
else
{
return v___x_3875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed(lean_object* v_stx_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_Elab_Tactic_evalWithUnfoldingNone(v_stx_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_stx_3886_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1(){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3910_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1));
v___x_3912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3));
v___x_3913_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed), 10, 0);
v___x_3914_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3910_, v___x_3911_, v___x_3912_, v___x_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___boxed(lean_object* v_a_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0(lean_object* v_stx_3920_, lean_object* v___x_3921_, uint8_t v___x_3922_, lean_object* v_userName_x3f_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_Elab_Tactic_elabTerm(v_stx_3920_, v___x_3921_, v___x_3922_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_4020_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_3936_ = v___x_3933_;
v_isShared_3937_ = v_isSharedCheck_4020_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3933_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_4020_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
if (lean_obj_tag(v_a_3934_) == 1)
{
lean_object* v_fvarId_3938_; lean_object* v___x_3940_; 
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v_userName_x3f_3923_);
v_fvarId_3938_ = lean_ctor_get(v_a_3934_, 0);
lean_inc(v_fvarId_3938_);
lean_dec_ref_known(v_a_3934_, 1);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 0, v_fvarId_3938_);
v___x_3940_ = v___x_3936_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_fvarId_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
else
{
lean_object* v___x_3942_; 
lean_del_object(v___x_3936_);
lean_inc(v___y_3931_);
lean_inc_ref(v___y_3930_);
lean_inc(v___y_3929_);
lean_inc_ref(v___y_3928_);
lean_inc(v_a_3934_);
v___x_3942_ = lean_infer_type(v_a_3934_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v_userName_3945_; uint8_t v_preserveBinderNames_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
if (lean_obj_tag(v_userName_x3f_3923_) == 0)
{
lean_object* v___x_4009_; 
v___x_4009_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1));
v_userName_3945_ = v___x_4009_;
v_preserveBinderNames_3946_ = v___x_3922_;
v___y_3947_ = v___y_3925_;
v___y_3948_ = v___y_3928_;
v___y_3949_ = v___y_3929_;
v___y_3950_ = v___y_3930_;
v___y_3951_ = v___y_3931_;
goto v___jp_3944_;
}
else
{
lean_object* v_val_4010_; uint8_t v___x_4011_; 
v_val_4010_ = lean_ctor_get(v_userName_x3f_3923_, 0);
lean_inc(v_val_4010_);
lean_dec_ref_known(v_userName_x3f_3923_, 1);
v___x_4011_ = 1;
v_userName_3945_ = v_val_4010_;
v_preserveBinderNames_3946_ = v___x_4011_;
v___y_3947_ = v___y_3925_;
v___y_3948_ = v___y_3928_;
v___y_3949_ = v___y_3929_;
v___y_3950_ = v___y_3930_;
v___y_3951_ = v___y_3931_;
goto v___jp_3944_;
}
v___jp_3944_:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3954_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v___x_3954_ = l_Lean_MVarId_assert(v_a_3953_, v_userName_3945_, v_a_3943_, v_a_3934_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
v___x_3956_ = l_Lean_Meta_intro1Core(v_a_3955_, v_preserveBinderNames_3946_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v_fst_3958_; lean_object* v_snd_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3984_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref_known(v___x_3956_, 1);
v_fst_3958_ = lean_ctor_get(v_a_3957_, 0);
v_snd_3959_ = lean_ctor_get(v_a_3957_, 1);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_a_3957_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3961_ = v_a_3957_;
v_isShared_3962_ = v_isSharedCheck_3984_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_snd_3959_);
lean_inc(v_fst_3958_);
lean_dec(v_a_3957_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3984_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; lean_object* v___x_3965_; 
v___x_3963_ = lean_box(0);
if (v_isShared_3962_ == 0)
{
lean_ctor_set_tag(v___x_3961_, 1);
lean_ctor_set(v___x_3961_, 1, v___x_3963_);
lean_ctor_set(v___x_3961_, 0, v_snd_3959_);
v___x_3965_ = v___x_3961_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_snd_3959_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3965_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3973_ == 0)
{
lean_object* v_unused_3974_; 
v_unused_3974_ = lean_ctor_get(v___x_3966_, 0);
lean_dec(v_unused_3974_);
v___x_3968_ = v___x_3966_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_dec(v___x_3966_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v_fst_3958_);
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_fst_3958_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v_fst_3958_);
v_a_3975_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3966_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3966_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
}
else
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
v_a_3985_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3956_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3956_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
v_a_3993_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3954_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3954_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v_userName_3945_);
lean_dec(v_a_3943_);
lean_dec(v_a_3934_);
v_a_4001_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3952_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3952_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_dec(v_a_3934_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v_userName_x3f_3923_);
v_a_4012_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_3942_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_3942_);
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
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v_userName_x3f_3923_);
v_a_4021_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_3933_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_3933_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(lean_object* v_stx_4029_, lean_object* v___x_4030_, lean_object* v___x_4031_, lean_object* v_userName_x3f_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
uint8_t v___x_1473__boxed_4042_; lean_object* v_res_4043_; 
v___x_1473__boxed_4042_ = lean_unbox(v___x_4031_);
v_res_4043_ = l_Lean_Elab_Tactic_elabAsFVar___lam__0(v_stx_4029_, v___x_4030_, v___x_1473__boxed_4042_, v_userName_x3f_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object* v_stx_4044_, lean_object* v_userName_x3f_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v___x_4055_; uint8_t v___x_4056_; lean_object* v___x_4057_; lean_object* v___f_4058_; lean_object* v___x_4059_; 
v___x_4055_ = lean_box(0);
v___x_4056_ = 0;
v___x_4057_ = lean_box(v___x_4056_);
v___f_4058_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4058_, 0, v_stx_4044_);
lean_closure_set(v___f_4058_, 1, v___x_4055_);
lean_closure_set(v___f_4058_, 2, v___x_4057_);
lean_closure_set(v___f_4058_, 3, v_userName_x3f_4045_);
v___x_4059_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4058_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___boxed(lean_object* v_stx_4060_, lean_object* v_userName_x3f_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Lean_Elab_Tactic_elabAsFVar(v_stx_4060_, v_userName_x3f_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
lean_dec(v_a_4063_);
lean_dec_ref(v_a_4062_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(lean_object* v_k_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v___x_4082_; 
lean_inc(v___y_4076_);
lean_inc_ref(v___y_4075_);
lean_inc(v___y_4074_);
lean_inc_ref(v___y_4073_);
v___x_4082_ = lean_apply_9(v_k_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, lean_box(0));
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed(lean_object* v_k_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(v_k_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(lean_object* v_k_4094_, uint8_t v_allowLevelAssignments_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v___f_4105_; lean_object* v___x_4106_; 
lean_inc(v___y_4099_);
lean_inc_ref(v___y_4098_);
lean_inc(v___y_4097_);
lean_inc_ref(v___y_4096_);
v___f_4105_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4105_, 0, v_k_4094_);
lean_closure_set(v___f_4105_, 1, v___y_4096_);
lean_closure_set(v___f_4105_, 2, v___y_4097_);
lean_closure_set(v___f_4105_, 3, v___y_4098_);
lean_closure_set(v___f_4105_, 4, v___y_4099_);
v___x_4106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_4095_, v___f_4105_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4106_) == 0)
{
return v___x_4106_;
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4106_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4106_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___boxed(lean_object* v_k_4115_, lean_object* v_allowLevelAssignments_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4126_; lean_object* v_res_4127_; 
v_allowLevelAssignments_boxed_4126_ = lean_unbox(v_allowLevelAssignments_4116_);
v_res_4127_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_4115_, v_allowLevelAssignments_boxed_4126_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(lean_object* v_00_u03b1_4128_, lean_object* v_k_4129_, uint8_t v_allowLevelAssignments_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_4129_, v_allowLevelAssignments_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed(lean_object* v_00_u03b1_4141_, lean_object* v_k_4142_, lean_object* v_allowLevelAssignments_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4153_; lean_object* v_res_4154_; 
v_allowLevelAssignments_boxed_4153_ = lean_unbox(v_allowLevelAssignments_4143_);
v_res_4154_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(v_00_u03b1_4141_, v_k_4142_, v_allowLevelAssignments_boxed_4153_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(lean_object* v_a_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v_a_x3f_4163_){
_start:
{
uint8_t v___x_4165_; lean_object* v___x_4166_; 
v___x_4165_ = 0;
v___x_4166_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4155_, v___x_4165_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0___boxed(lean_object* v_a_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v_a_x3f_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v_a_x3f_4175_);
lean_dec(v_a_x3f_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(lean_object* v_x_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; 
v___x_4188_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4180_, v___y_4182_, v___y_4184_, v___y_4186_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v_r_4190_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4188_, 1);
lean_inc(v___y_4186_);
lean_inc_ref(v___y_4185_);
lean_inc(v___y_4184_);
lean_inc_ref(v___y_4183_);
lean_inc(v___y_4182_);
lean_inc_ref(v___y_4181_);
lean_inc(v___y_4180_);
lean_inc_ref(v___y_4179_);
v_r_4190_ = lean_apply_9(v_x_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, lean_box(0));
if (lean_obj_tag(v_r_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4215_; 
v_a_4191_ = lean_ctor_get(v_r_4190_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v_r_4190_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4193_ = v_r_4190_;
v_isShared_4194_ = v_isSharedCheck_4215_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v_r_4190_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4215_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
lean_inc(v_a_4191_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 1);
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_4189_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___x_4196_);
lean_dec_ref(v___x_4196_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4204_ == 0)
{
lean_object* v_unused_4205_; 
v_unused_4205_ = lean_ctor_get(v___x_4197_, 0);
lean_dec(v_unused_4205_);
v___x_4199_ = v___x_4197_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_dec(v___x_4197_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_a_4191_);
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4191_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec(v_a_4191_);
v_a_4206_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4197_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4197_);
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
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v_a_4216_ = lean_ctor_get(v_r_4190_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v_r_4190_, 1);
v___x_4217_ = lean_box(0);
v___x_4218_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_4189_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___x_4217_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; 
v_unused_4226_ = lean_ctor_get(v___x_4218_, 0);
lean_dec(v_unused_4226_);
v___x_4220_ = v___x_4218_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_dec(v___x_4218_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set_tag(v___x_4220_, 1);
lean_ctor_set(v___x_4220_, 0, v_a_4216_);
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4216_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v_a_4216_);
v_a_4227_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4218_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4218_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v_x_4178_);
v_a_4235_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4188_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4188_);
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
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___boxed(lean_object* v_x_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(lean_object* v_00_u03b1_4254_, lean_object* v_x_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___boxed(lean_object* v_00_u03b1_4266_, lean_object* v_x_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(v_00_u03b1_4266_, v_x_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(lean_object* v_a_4278_, lean_object* v_as_4279_, lean_object* v_i_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_zero_4286_; uint8_t v_isZero_4287_; 
v_zero_4286_ = lean_unsigned_to_nat(0u);
v_isZero_4287_ = lean_nat_dec_eq(v_i_4280_, v_zero_4286_);
if (v_isZero_4287_ == 1)
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_dec(v_i_4280_);
lean_dec_ref(v_a_4278_);
v___x_4288_ = lean_box(0);
v___x_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
return v___x_4289_;
}
else
{
lean_object* v_one_4290_; lean_object* v_n_4291_; lean_object* v___x_4292_; 
v_one_4290_ = lean_unsigned_to_nat(1u);
v_n_4291_ = lean_nat_sub(v_i_4280_, v_one_4290_);
lean_dec(v_i_4280_);
v___x_4292_ = lean_array_fget(v_as_4279_, v_n_4291_);
if (lean_obj_tag(v___x_4292_) == 0)
{
v_i_4280_ = v_n_4291_;
goto _start;
}
else
{
lean_object* v_val_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4326_; 
v_val_4294_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4296_ = v___x_4292_;
v_isShared_4297_ = v_isSharedCheck_4326_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_val_4294_);
lean_dec(v___x_4292_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4326_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = l_Lean_LocalDecl_type(v_val_4294_);
lean_inc_ref(v_a_4278_);
v___x_4299_ = l_Lean_Meta_isExprDefEq(v_a_4278_, v___x_4298_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4317_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4317_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4317_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
uint8_t v___y_4305_; uint8_t v___x_4314_; uint8_t v___x_4315_; 
v___x_4314_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4294_);
v___x_4315_ = lean_bool_not(v___x_4314_);
if (v___x_4315_ == 0)
{
lean_dec(v_a_4300_);
v___y_4305_ = v___x_4315_;
goto v___jp_4304_;
}
else
{
uint8_t v___x_4316_; 
v___x_4316_ = lean_unbox(v_a_4300_);
lean_dec(v_a_4300_);
v___y_4305_ = v___x_4316_;
goto v___jp_4304_;
}
v___jp_4304_:
{
if (v___y_4305_ == 0)
{
lean_del_object(v___x_4302_);
lean_del_object(v___x_4296_);
lean_dec(v_val_4294_);
v_i_4280_ = v_n_4291_;
goto _start;
}
else
{
lean_object* v___x_4307_; lean_object* v___x_4309_; 
lean_dec(v_n_4291_);
lean_dec_ref(v_a_4278_);
v___x_4307_ = l_Lean_LocalDecl_fvarId(v_val_4294_);
lean_dec(v_val_4294_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v___x_4307_);
v___x_4309_ = v___x_4296_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4307_);
v___x_4309_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4311_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v___x_4309_);
v___x_4311_ = v___x_4302_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_del_object(v___x_4296_);
lean_dec(v_val_4294_);
lean_dec(v_n_4291_);
lean_dec_ref(v_a_4278_);
v_a_4318_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4299_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4299_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_a_4327_, lean_object* v_as_4328_, lean_object* v_i_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_4327_, v_as_4328_, v_i_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec_ref(v_as_4328_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_4336_, lean_object* v_as_4337_, lean_object* v_i_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v_zero_4348_; uint8_t v_isZero_4349_; 
v_zero_4348_ = lean_unsigned_to_nat(0u);
v_isZero_4349_ = lean_nat_dec_eq(v_i_4338_, v_zero_4348_);
if (v_isZero_4349_ == 1)
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
lean_dec(v_i_4338_);
lean_dec_ref(v_a_4336_);
v___x_4350_ = lean_box(0);
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4350_);
return v___x_4351_;
}
else
{
lean_object* v_one_4352_; lean_object* v_n_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_one_4352_ = lean_unsigned_to_nat(1u);
v_n_4353_ = lean_nat_sub(v_i_4338_, v_one_4352_);
lean_dec(v_i_4338_);
v___x_4354_ = lean_array_fget_borrowed(v_as_4337_, v_n_4353_);
lean_inc_ref(v_a_4336_);
v___x_4355_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_4336_, v___x_4354_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
if (lean_obj_tag(v_a_4356_) == 0)
{
lean_dec_ref_known(v___x_4355_, 1);
v_i_4338_ = v_n_4353_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_4356_, 1);
lean_dec(v_n_4353_);
lean_dec_ref(v_a_4336_);
return v___x_4355_;
}
}
else
{
lean_dec(v_n_4353_);
lean_dec_ref(v_a_4336_);
return v___x_4355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(lean_object* v_a_4358_, lean_object* v_x_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
if (lean_obj_tag(v_x_4359_) == 0)
{
lean_object* v_cs_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v_cs_4369_ = lean_ctor_get(v_x_4359_, 0);
v___x_4370_ = lean_array_get_size(v_cs_4369_);
v___x_4371_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_4358_, v_cs_4369_, v___x_4370_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
return v___x_4371_;
}
else
{
lean_object* v_vs_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v_vs_4372_ = lean_ctor_get(v_x_4359_, 0);
v___x_4373_ = lean_array_get_size(v_vs_4372_);
v___x_4374_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_4358_, v_vs_4372_, v___x_4373_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
return v___x_4374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(lean_object* v_a_4375_, lean_object* v_x_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_4375_, v_x_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec_ref(v_x_4376_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_4387_, lean_object* v_as_4388_, lean_object* v_i_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_4387_, v_as_4388_, v_i_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec_ref(v_as_4388_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object* v_a_4400_, lean_object* v_t_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v_root_4411_; lean_object* v_tail_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v_root_4411_ = lean_ctor_get(v_t_4401_, 0);
v_tail_4412_ = lean_ctor_get(v_t_4401_, 1);
v___x_4413_ = lean_array_get_size(v_tail_4412_);
lean_inc_ref(v_a_4400_);
v___x_4414_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_4400_, v_tail_4412_, v___x_4413_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4415_);
if (lean_obj_tag(v_a_4415_) == 0)
{
lean_object* v___x_4416_; 
lean_dec_ref_known(v___x_4414_, 1);
v___x_4416_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_4400_, v_root_4411_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
return v___x_4416_;
}
else
{
lean_dec_ref_known(v_a_4415_, 1);
lean_dec_ref(v_a_4400_);
return v___x_4414_;
}
}
else
{
lean_dec_ref(v_a_4400_);
return v___x_4414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object* v_a_4417_, lean_object* v_t_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_4417_, v_t_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec_ref(v_t_4418_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(lean_object* v_a_4429_, lean_object* v_lctx_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v_decls_4440_; lean_object* v___x_4441_; 
v_decls_4440_ = lean_ctor_get(v_lctx_4430_, 1);
v___x_4441_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_4429_, v_decls_4440_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object* v_a_4442_, lean_object* v_lctx_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_4442_, v_lctx_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec_ref(v_lctx_4443_);
return v_res_4453_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4455_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___lam__0___closed__0));
v___x_4456_ = l_Lean_stringToMessageData(v___x_4455_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object* v___x_4457_, lean_object* v___x_4458_, uint8_t v___x_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_Lean_Elab_Tactic_elabTerm(v___x_4457_, v___x_4458_, v___x_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; lean_object* v_lctx_4471_; lean_object* v___x_4472_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc_n(v_a_4470_, 2);
lean_dec_ref_known(v___x_4469_, 1);
v_lctx_4471_ = lean_ctor_get(v___y_4464_, 2);
v___x_4472_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_4470_, v_lctx_4471_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4485_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4475_ = v___x_4472_;
v_isShared_4476_ = v_isSharedCheck_4485_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4485_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
if (lean_obj_tag(v_a_4473_) == 0)
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
lean_del_object(v___x_4475_);
v___x_4477_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRename___lam__0___closed__1, &l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1);
v___x_4478_ = l_Lean_indentExpr(v_a_4470_);
v___x_4479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4477_);
lean_ctor_set(v___x_4479_, 1, v___x_4478_);
v___x_4480_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_4479_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4480_;
}
else
{
lean_object* v_val_4481_; lean_object* v___x_4483_; 
lean_dec(v_a_4470_);
v_val_4481_ = lean_ctor_get(v_a_4473_, 0);
lean_inc(v_val_4481_);
lean_dec_ref_known(v_a_4473_, 1);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 0, v_val_4481_);
v___x_4483_ = v___x_4475_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_val_4481_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec(v_a_4470_);
v_a_4486_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4472_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4472_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
v_a_4494_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4469_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4469_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object* v___x_4502_, lean_object* v___x_4503_, lean_object* v___x_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
uint8_t v___x_7469__boxed_4514_; lean_object* v_res_4515_; 
v___x_7469__boxed_4514_ = lean_unbox(v___x_4504_);
v_res_4515_ = l_Lean_Elab_Tactic_evalRename___lam__0(v___x_4502_, v___x_4503_, v___x_7469__boxed_4514_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1(lean_object* v___x_4516_, lean_object* v_h_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v___x_4527_; 
v___x_4527_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v___x_4516_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4529_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_a_4528_);
lean_dec_ref_known(v___x_4527_, 1);
v___x_4529_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_4519_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v___x_4529_, 1);
v___x_4531_ = l_Lean_TSyntax_getId(v_h_4517_);
v___x_4532_ = l_Lean_MVarId_rename(v_a_4530_, v_a_4528_, v___x_4531_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v___x_4532_, 1);
v___x_4534_ = lean_box(0);
v___x_4535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4535_, 0, v_a_4533_);
lean_ctor_set(v___x_4535_, 1, v___x_4534_);
v___x_4536_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_4535_, v___y_4519_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
return v___x_4536_;
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
v_a_4537_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4532_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4532_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec(v_a_4528_);
v_a_4545_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4529_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4529_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
v_a_4553_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4527_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4527_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1___boxed(lean_object* v___x_4561_, lean_object* v_h_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l_Lean_Elab_Tactic_evalRename___lam__1(v___x_4561_, v_h_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v_h_4562_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object* v_stx_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v___x_4592_; uint8_t v___x_4593_; 
v___x_4592_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
lean_inc(v_stx_4582_);
v___x_4593_ = l_Lean_Syntax_isOfKind(v_stx_4582_, v___x_4592_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; 
lean_dec(v_stx_4582_);
v___x_4594_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_4594_;
}
else
{
lean_object* v___x_4595_; lean_object* v_h_4596_; lean_object* v___x_4597_; uint8_t v___x_4598_; 
v___x_4595_ = lean_unsigned_to_nat(3u);
v_h_4596_ = l_Lean_Syntax_getArg(v_stx_4582_, v___x_4595_);
v___x_4597_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__3));
lean_inc(v_h_4596_);
v___x_4598_ = l_Lean_Syntax_isOfKind(v_h_4596_, v___x_4597_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; 
lean_dec(v_h_4596_);
lean_dec(v_stx_4582_);
v___x_4599_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_4599_;
}
else
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___f_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___f_4609_; lean_object* v___x_4610_; 
v___x_4600_ = lean_unsigned_to_nat(1u);
v___x_4601_ = l_Lean_Syntax_getArg(v_stx_4582_, v___x_4600_);
lean_dec(v_stx_4582_);
v___x_4602_ = lean_box(0);
v___x_4603_ = lean_box(v___x_4598_);
v___f_4604_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__0___boxed), 12, 3);
lean_closure_set(v___f_4604_, 0, v___x_4601_);
lean_closure_set(v___f_4604_, 1, v___x_4602_);
lean_closure_set(v___f_4604_, 2, v___x_4603_);
v___x_4605_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_4605_, 0, lean_box(0));
lean_closure_set(v___x_4605_, 1, v___f_4604_);
v___x_4606_ = 0;
v___x_4607_ = lean_box(v___x_4606_);
v___x_4608_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed), 12, 3);
lean_closure_set(v___x_4608_, 0, lean_box(0));
lean_closure_set(v___x_4608_, 1, v___x_4605_);
lean_closure_set(v___x_4608_, 2, v___x_4607_);
v___f_4609_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__1___boxed), 11, 2);
lean_closure_set(v___f_4609_, 0, v___x_4608_);
lean_closure_set(v___f_4609_, 1, v_h_4596_);
v___x_4610_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4609_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___boxed(lean_object* v_stx_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_Lean_Elab_Tactic_evalRename(v_stx_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_);
lean_dec(v_a_4619_);
lean_dec_ref(v_a_4618_);
lean_dec(v_a_4617_);
lean_dec_ref(v_a_4616_);
lean_dec(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(lean_object* v_a_4622_, lean_object* v_as_4623_, lean_object* v_i_4624_, lean_object* v_a_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_4622_, v_as_4623_, v_i_4624_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(lean_object* v_a_4636_, lean_object* v_as_4637_, lean_object* v_i_4638_, lean_object* v_a_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(v_a_4636_, v_as_4637_, v_i_4638_, v_a_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec_ref(v_as_4637_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(lean_object* v_a_4650_, lean_object* v_as_4651_, lean_object* v_i_4652_, lean_object* v_a_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v___x_4663_; 
v___x_4663_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_4650_, v_as_4651_, v_i_4652_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_a_4664_, lean_object* v_as_4665_, lean_object* v_i_4666_, lean_object* v_a_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(v_a_4664_, v_as_4665_, v_i_4666_, v_a_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec_ref(v_as_4665_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1(){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4685_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4686_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
v___x_4687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_4688_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___boxed), 10, 0);
v___x_4689_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4685_, v___x_4686_, v___x_4687_, v___x_4688_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___boxed(lean_object* v_a_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3(){
_start:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4718_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_4719_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6));
v___x_4720_ = l_Lean_addBuiltinDeclarationRanges(v___x_4718_, v___x_4719_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___boxed(lean_object* v_a_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
return v_res_4722_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rename(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Rename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithImplicit___regBuiltin_Lean_Elab_Tactic_evalWithImplicit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_ElabTerm(builtin);
}
#ifdef __cplusplus
}
#endif
