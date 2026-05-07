// Lean compiler output
// Module: Lean.Elab.Tactic.ElabTerm
// Imports: public import Lean.Meta.Tactic.Constructor public import Lean.Meta.Tactic.Replace public import Lean.Meta.Tactic.Rename public import Lean.Elab.Tactic.Config
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
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
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
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_10_);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(uint8_t v_cond_112_, lean_object* v_____r_113_){
_start:
{
if (v_cond_112_ == 0)
{
uint8_t v___x_114_; 
v___x_114_ = 1;
return v___x_114_;
}
else
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed(lean_object* v_cond_116_, lean_object* v_____r_117_){
_start:
{
uint8_t v_cond_boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_cond_boxed_118_ = lean_unbox(v_cond_116_);
v_res_119_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_boxed_118_, v_____r_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1(lean_object* v___f_121_, lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_box(0);
v___x_124_ = lean_apply_1(v___f_121_, v___x_123_);
v___x_125_ = lean_unbox(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed(lean_object* v___f_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1(v___f_126_, v_x_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(uint8_t v_cond_138_, lean_object* v_act_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_options_149_; lean_object* v_declName_x3f_150_; lean_object* v_macroStack_151_; uint8_t v_mayPostpone_152_; uint8_t v_errToSorry_153_; lean_object* v_autoBoundImplicitContext_154_; lean_object* v_autoBoundImplicitForbidden_155_; lean_object* v_sectionVars_156_; lean_object* v_sectionFVars_157_; uint8_t v_implicitLambda_158_; uint8_t v_heedElabAsElim_159_; uint8_t v_isNoncomputableSection_160_; uint8_t v_isMetaSection_161_; uint8_t v_ignoreTCFailures_162_; uint8_t v_inPattern_163_; lean_object* v_tacSnap_x3f_164_; uint8_t v_saveRecAppSyntax_165_; uint8_t v_holesAsSyntheticOpaque_166_; uint8_t v_checkDeprecated_167_; lean_object* v_fixedTermElabs_168_; lean_object* v___y_170_; uint8_t v___y_174_; 
v_options_149_ = lean_ctor_get(v___y_146_, 2);
v_declName_x3f_150_ = lean_ctor_get(v___y_142_, 0);
v_macroStack_151_ = lean_ctor_get(v___y_142_, 1);
v_mayPostpone_152_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8);
v_errToSorry_153_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_154_ = lean_ctor_get(v___y_142_, 2);
v_autoBoundImplicitForbidden_155_ = lean_ctor_get(v___y_142_, 3);
v_sectionVars_156_ = lean_ctor_get(v___y_142_, 4);
v_sectionFVars_157_ = lean_ctor_get(v___y_142_, 5);
v_implicitLambda_158_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 2);
v_heedElabAsElim_159_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_160_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 4);
v_isMetaSection_161_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_162_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 6);
v_inPattern_163_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_164_ = lean_ctor_get(v___y_142_, 6);
v_saveRecAppSyntax_165_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_166_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 9);
v_checkDeprecated_167_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*8 + 10);
v_fixedTermElabs_168_ = lean_ctor_get(v___y_142_, 7);
if (lean_obj_tag(v_tacSnap_x3f_164_) == 0)
{
v___y_170_ = v_tacSnap_x3f_164_;
goto v___jp_169_;
}
else
{
lean_object* v_val_176_; lean_object* v_old_x3f_177_; lean_object* v___x_178_; lean_object* v___f_179_; 
v_val_176_ = lean_ctor_get(v_tacSnap_x3f_164_, 0);
v_old_x3f_177_ = lean_ctor_get(v_val_176_, 0);
v___x_178_ = lean_box(v_cond_138_);
v___f_179_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_179_, 0, v___x_178_);
if (lean_obj_tag(v_old_x3f_177_) == 1)
{
if (v_cond_138_ == 0)
{
lean_dec_ref(v___f_179_);
goto v___jp_180_;
}
else
{
lean_object* v_val_183_; lean_object* v_map_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_val_183_ = lean_ctor_get(v_old_x3f_177_, 0);
v_map_184_ = lean_ctor_get(v_options_149_, 0);
v___x_185_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__3));
v___x_186_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_184_, v___x_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_dec_ref(v___f_179_);
goto v___jp_180_;
}
else
{
lean_object* v_val_187_; 
v_val_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_val_187_);
lean_dec_ref(v___x_186_);
if (lean_obj_tag(v_val_187_) == 1)
{
uint8_t v_v_188_; 
v_v_188_ = lean_ctor_get_uint8(v_val_187_, 0);
lean_dec_ref(v_val_187_);
if (v_v_188_ == 0)
{
lean_dec_ref(v___f_179_);
goto v___jp_180_;
}
else
{
lean_object* v_stx_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_stx_189_ = lean_ctor_get(v_val_183_, 0);
v___f_190_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_190_, 0, v___f_179_);
v___x_191_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___closed__4));
v___x_192_ = lean_box(0);
v___x_193_ = 0;
lean_inc(v_stx_189_);
v___x_194_ = l_Lean_Syntax_formatStx(v_stx_189_, v___x_192_, v___x_193_);
v___x_195_ = l_Std_Format_defWidth;
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = l_Std_Format_pretty(v___x_194_, v___x_195_, v___x_196_, v___x_196_);
v___x_198_ = lean_string_append(v___x_191_, v___x_197_);
lean_dec_ref(v___x_197_);
v___x_199_ = lean_dbg_trace(v___x_198_, v___f_190_);
v___x_200_ = lean_unbox(v___x_199_);
lean_dec(v___x_199_);
v___y_174_ = v___x_200_;
goto v___jp_173_;
}
}
else
{
lean_dec(v_val_187_);
lean_dec_ref(v___f_179_);
goto v___jp_180_;
}
}
}
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
lean_dec_ref(v___f_179_);
v___x_201_ = lean_box(0);
v___x_202_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_138_, v___x_201_);
v___y_174_ = v___x_202_;
goto v___jp_173_;
}
v___jp_180_:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_box(0);
v___x_182_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___lam__0(v_cond_138_, v___x_181_);
v___y_174_ = v___x_182_;
goto v___jp_173_;
}
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc_ref(v_fixedTermElabs_168_);
lean_inc(v_sectionFVars_157_);
lean_inc(v_sectionVars_156_);
lean_inc_ref(v_autoBoundImplicitForbidden_155_);
lean_inc(v_autoBoundImplicitContext_154_);
lean_inc(v_macroStack_151_);
lean_inc(v_declName_x3f_150_);
v___x_171_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_171_, 0, v_declName_x3f_150_);
lean_ctor_set(v___x_171_, 1, v_macroStack_151_);
lean_ctor_set(v___x_171_, 2, v_autoBoundImplicitContext_154_);
lean_ctor_set(v___x_171_, 3, v_autoBoundImplicitForbidden_155_);
lean_ctor_set(v___x_171_, 4, v_sectionVars_156_);
lean_ctor_set(v___x_171_, 5, v_sectionFVars_157_);
lean_ctor_set(v___x_171_, 6, v___y_170_);
lean_ctor_set(v___x_171_, 7, v_fixedTermElabs_168_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8, v_mayPostpone_152_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 1, v_errToSorry_153_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 2, v_implicitLambda_158_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 3, v_heedElabAsElim_159_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 4, v_isNoncomputableSection_160_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 5, v_isMetaSection_161_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 6, v_ignoreTCFailures_162_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 7, v_inPattern_163_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_165_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_166_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*8 + 10, v_checkDeprecated_167_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
lean_inc(v___y_143_);
lean_inc(v___y_141_);
lean_inc_ref(v___y_140_);
v___x_172_ = lean_apply_9(v_act_139_, v___y_140_, v___y_141_, v___x_171_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, lean_box(0));
return v___x_172_;
}
v___jp_173_:
{
if (v___y_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(0);
v___y_170_ = v___x_175_;
goto v___jp_169_;
}
else
{
lean_inc(v_tacSnap_x3f_164_);
v___y_170_ = v_tacSnap_x3f_164_;
goto v___jp_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg___boxed(lean_object* v_cond_203_, lean_object* v_act_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
uint8_t v_cond_boxed_214_; lean_object* v_res_215_; 
v_cond_boxed_214_ = lean_unbox(v_cond_203_);
v_res_215_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_boxed_214_, v_act_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(lean_object* v_00_u03b1_216_, uint8_t v_cond_217_, lean_object* v_act_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v_cond_217_, v_act_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___boxed(lean_object* v_00_u03b1_229_, lean_object* v_cond_230_, lean_object* v_act_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v_cond_boxed_241_; lean_object* v_res_242_; 
v_cond_boxed_241_ = lean_unbox(v_cond_230_);
v_res_242_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1(v_00_u03b1_229_, v_cond_boxed_241_, v_act_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(lean_object* v_k_243_, uint8_t v_mayPostpone_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_243_, v_mayPostpone_244_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed(lean_object* v_k_255_, lean_object* v_mayPostpone_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
uint8_t v_mayPostpone_boxed_266_; lean_object* v_res_267_; 
v_mayPostpone_boxed_266_ = lean_unbox(v_mayPostpone_256_);
v_res_267_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(v_k_255_, v_mayPostpone_boxed_266_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(lean_object* v___f_268_, lean_object* v_k_269_, uint8_t v_mayPostpone_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
uint8_t v_recover_280_; 
v_recover_280_ = lean_ctor_get_uint8(v___y_271_, sizeof(void*)*1);
if (v_recover_280_ == 0)
{
lean_object* v___x_281_; 
lean_dec_ref(v_k_269_);
v___x_281_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_runTermElab_spec__0___redArg(v___f_268_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; 
lean_dec_ref(v___f_268_);
v___x_282_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_runTermElab_go___redArg(v_k_269_, v_mayPostpone_270_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed(lean_object* v___f_283_, lean_object* v_k_284_, lean_object* v_mayPostpone_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
uint8_t v_mayPostpone_boxed_295_; lean_object* v_res_296_; 
v_mayPostpone_boxed_295_ = lean_unbox(v_mayPostpone_285_);
v_res_296_ = l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(v___f_283_, v_k_284_, v_mayPostpone_boxed_295_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object* v_k_297_, uint8_t v_mayPostpone_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___f_311_; uint8_t v___x_312_; lean_object* v___x_313_; 
v___x_308_ = lean_box(v_mayPostpone_298_);
lean_inc_ref(v_k_297_);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_309_, 0, v_k_297_);
lean_closure_set(v___f_309_, 1, v___x_308_);
v___x_310_ = lean_box(v_mayPostpone_298_);
v___f_311_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_311_, 0, v___f_309_);
lean_closure_set(v___f_311_, 1, v_k_297_);
lean_closure_set(v___f_311_, 2, v___x_310_);
v___x_312_ = 1;
v___x_313_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00Lean_Elab_Tactic_runTermElab_spec__1___redArg(v___x_312_, v___f_311_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___boxed(lean_object* v_k_314_, lean_object* v_mayPostpone_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
uint8_t v_mayPostpone_boxed_325_; lean_object* v_res_326_; 
v_mayPostpone_boxed_325_ = lean_unbox(v_mayPostpone_315_);
v_res_326_ = l_Lean_Elab_Tactic_runTermElab___redArg(v_k_314_, v_mayPostpone_boxed_325_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object* v_00_u03b1_327_, lean_object* v_k_328_, uint8_t v_mayPostpone_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Elab_Tactic_runTermElab___redArg(v_k_328_, v_mayPostpone_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object* v_00_u03b1_340_, lean_object* v_k_341_, lean_object* v_mayPostpone_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
uint8_t v_mayPostpone_boxed_352_; lean_object* v_res_353_; 
v_mayPostpone_boxed_352_ = lean_unbox(v_mayPostpone_342_);
v_res_353_ = l_Lean_Elab_Tactic_runTermElab(v_00_u03b1_340_, v_k_341_, v_mayPostpone_boxed_352_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(lean_object* v_e_354_, lean_object* v___y_355_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = l_Lean_Expr_hasMVar(v_e_354_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v_e_354_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v_mctx_360_; lean_object* v___x_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_364_; lean_object* v_cache_365_; lean_object* v_zetaDeltaFVarIds_366_; lean_object* v_postponed_367_; lean_object* v_diag_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_377_; 
v___x_359_ = lean_st_ref_get(v___y_355_);
v_mctx_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc_ref(v_mctx_360_);
lean_dec(v___x_359_);
v___x_361_ = l_Lean_instantiateMVarsCore(v_mctx_360_, v_e_354_);
v_fst_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_fst_362_);
v_snd_363_ = lean_ctor_get(v___x_361_, 1);
lean_inc(v_snd_363_);
lean_dec_ref(v___x_361_);
v___x_364_ = lean_st_ref_take(v___y_355_);
v_cache_365_ = lean_ctor_get(v___x_364_, 1);
v_zetaDeltaFVarIds_366_ = lean_ctor_get(v___x_364_, 2);
v_postponed_367_ = lean_ctor_get(v___x_364_, 3);
v_diag_368_ = lean_ctor_get(v___x_364_, 4);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_378_);
v___x_370_ = v___x_364_;
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_diag_368_);
lean_inc(v_postponed_367_);
lean_inc(v_zetaDeltaFVarIds_366_);
lean_inc(v_cache_365_);
lean_dec(v___x_364_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_snd_363_);
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_snd_363_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_cache_365_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_zetaDeltaFVarIds_366_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_postponed_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_diag_368_);
v___x_373_ = v_reuseFailAlloc_376_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_st_ref_set(v___y_355_, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v_fst_362_);
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg___boxed(lean_object* v_e_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_e_379_, v___y_380_);
lean_dec(v___y_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(lean_object* v_e_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_e_383_, v___y_389_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___boxed(lean_object* v_e_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0(v_e_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object* v_stx_405_, lean_object* v_expectedType_x3f_406_, uint8_t v_mayPostpone_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_fileName_421_; lean_object* v_fileMap_422_; lean_object* v_options_423_; lean_object* v_currRecDepth_424_; lean_object* v_maxRecDepth_425_; lean_object* v_ref_426_; lean_object* v_currNamespace_427_; lean_object* v_openDecls_428_; lean_object* v_initHeartbeats_429_; lean_object* v_maxHeartbeats_430_; lean_object* v_quotContext_431_; lean_object* v_currMacroScope_432_; uint8_t v_diag_433_; lean_object* v_cancelTk_x3f_434_; uint8_t v_suppressElabErrors_435_; lean_object* v_inheritedTraceOptions_436_; lean_object* v_ref_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_417_ = 1;
v___x_418_ = lean_box(v___x_417_);
v___x_419_ = lean_box(v___x_417_);
lean_inc(v_stx_405_);
v___x_420_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_420_, 0, v_stx_405_);
lean_closure_set(v___x_420_, 1, v_expectedType_x3f_406_);
lean_closure_set(v___x_420_, 2, v___x_418_);
lean_closure_set(v___x_420_, 3, v___x_419_);
v_fileName_421_ = lean_ctor_get(v_a_414_, 0);
v_fileMap_422_ = lean_ctor_get(v_a_414_, 1);
v_options_423_ = lean_ctor_get(v_a_414_, 2);
v_currRecDepth_424_ = lean_ctor_get(v_a_414_, 3);
v_maxRecDepth_425_ = lean_ctor_get(v_a_414_, 4);
v_ref_426_ = lean_ctor_get(v_a_414_, 5);
v_currNamespace_427_ = lean_ctor_get(v_a_414_, 6);
v_openDecls_428_ = lean_ctor_get(v_a_414_, 7);
v_initHeartbeats_429_ = lean_ctor_get(v_a_414_, 8);
v_maxHeartbeats_430_ = lean_ctor_get(v_a_414_, 9);
v_quotContext_431_ = lean_ctor_get(v_a_414_, 10);
v_currMacroScope_432_ = lean_ctor_get(v_a_414_, 11);
v_diag_433_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*14);
v_cancelTk_x3f_434_ = lean_ctor_get(v_a_414_, 12);
v_suppressElabErrors_435_ = lean_ctor_get_uint8(v_a_414_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_436_ = lean_ctor_get(v_a_414_, 13);
v_ref_437_ = l_Lean_replaceRef(v_stx_405_, v_ref_426_);
lean_dec(v_stx_405_);
lean_inc_ref(v_inheritedTraceOptions_436_);
lean_inc(v_cancelTk_x3f_434_);
lean_inc(v_currMacroScope_432_);
lean_inc(v_quotContext_431_);
lean_inc(v_maxHeartbeats_430_);
lean_inc(v_initHeartbeats_429_);
lean_inc(v_openDecls_428_);
lean_inc(v_currNamespace_427_);
lean_inc(v_maxRecDepth_425_);
lean_inc(v_currRecDepth_424_);
lean_inc_ref(v_options_423_);
lean_inc_ref(v_fileMap_422_);
lean_inc_ref(v_fileName_421_);
v___x_438_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_438_, 0, v_fileName_421_);
lean_ctor_set(v___x_438_, 1, v_fileMap_422_);
lean_ctor_set(v___x_438_, 2, v_options_423_);
lean_ctor_set(v___x_438_, 3, v_currRecDepth_424_);
lean_ctor_set(v___x_438_, 4, v_maxRecDepth_425_);
lean_ctor_set(v___x_438_, 5, v_ref_437_);
lean_ctor_set(v___x_438_, 6, v_currNamespace_427_);
lean_ctor_set(v___x_438_, 7, v_openDecls_428_);
lean_ctor_set(v___x_438_, 8, v_initHeartbeats_429_);
lean_ctor_set(v___x_438_, 9, v_maxHeartbeats_430_);
lean_ctor_set(v___x_438_, 10, v_quotContext_431_);
lean_ctor_set(v___x_438_, 11, v_currMacroScope_432_);
lean_ctor_set(v___x_438_, 12, v_cancelTk_x3f_434_);
lean_ctor_set(v___x_438_, 13, v_inheritedTraceOptions_436_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*14, v_diag_433_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*14 + 1, v_suppressElabErrors_435_);
v___x_439_ = l_Lean_Elab_Tactic_runTermElab___redArg(v___x_420_, v_mayPostpone_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v___x_438_, v_a_415_);
lean_dec_ref(v___x_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v___x_439_);
v___x_441_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_440_, v_a_413_);
return v___x_441_;
}
else
{
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object* v_stx_442_, lean_object* v_expectedType_x3f_443_, lean_object* v_mayPostpone_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
uint8_t v_mayPostpone_boxed_454_; lean_object* v_res_455_; 
v_mayPostpone_boxed_454_ = lean_unbox(v_mayPostpone_444_);
v_res_455_ = l_Lean_Elab_Tactic_elabTerm(v_stx_442_, v_expectedType_x3f_443_, v_mayPostpone_boxed_454_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object* v_stx_456_, lean_object* v_expectedType_x3f_457_, uint8_t v_mayPostpone_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; 
lean_inc(v_expectedType_x3f_457_);
v___x_468_ = l_Lean_Elab_Tactic_elabTerm(v_stx_456_, v_expectedType_x3f_457_, v_mayPostpone_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
if (lean_obj_tag(v_expectedType_x3f_457_) == 0)
{
return v___x_468_;
}
else
{
lean_object* v_a_469_; lean_object* v_val_470_; lean_object* v___x_471_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc_n(v_a_469_, 2);
lean_dec_ref(v___x_468_);
v_val_470_ = lean_ctor_get(v_expectedType_x3f_457_, 0);
lean_inc(v_val_470_);
lean_dec_ref(v_expectedType_x3f_457_);
lean_inc(v_a_466_);
lean_inc_ref(v_a_465_);
lean_inc(v_a_464_);
lean_inc_ref(v_a_463_);
v___x_471_ = lean_infer_type(v_a_469_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_552_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_552_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_552_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_552_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
uint8_t v_a_477_; lean_object* v___x_499_; uint8_t v_foApprox_500_; uint8_t v_ctxApprox_501_; uint8_t v_quasiPatternApprox_502_; uint8_t v_constApprox_503_; uint8_t v_isDefEqStuckEx_504_; uint8_t v_unificationHints_505_; uint8_t v_proofIrrelevance_506_; uint8_t v_offsetCnstrs_507_; uint8_t v_transparency_508_; uint8_t v_etaStruct_509_; uint8_t v_univApprox_510_; uint8_t v_iota_511_; uint8_t v_beta_512_; uint8_t v_proj_513_; uint8_t v_zeta_514_; uint8_t v_zetaDelta_515_; uint8_t v_zetaUnused_516_; uint8_t v_zetaHave_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_551_; 
v___x_499_ = l_Lean_Meta_Context_config(v_a_463_);
v_foApprox_500_ = lean_ctor_get_uint8(v___x_499_, 0);
v_ctxApprox_501_ = lean_ctor_get_uint8(v___x_499_, 1);
v_quasiPatternApprox_502_ = lean_ctor_get_uint8(v___x_499_, 2);
v_constApprox_503_ = lean_ctor_get_uint8(v___x_499_, 3);
v_isDefEqStuckEx_504_ = lean_ctor_get_uint8(v___x_499_, 4);
v_unificationHints_505_ = lean_ctor_get_uint8(v___x_499_, 5);
v_proofIrrelevance_506_ = lean_ctor_get_uint8(v___x_499_, 6);
v_offsetCnstrs_507_ = lean_ctor_get_uint8(v___x_499_, 8);
v_transparency_508_ = lean_ctor_get_uint8(v___x_499_, 9);
v_etaStruct_509_ = lean_ctor_get_uint8(v___x_499_, 10);
v_univApprox_510_ = lean_ctor_get_uint8(v___x_499_, 11);
v_iota_511_ = lean_ctor_get_uint8(v___x_499_, 12);
v_beta_512_ = lean_ctor_get_uint8(v___x_499_, 13);
v_proj_513_ = lean_ctor_get_uint8(v___x_499_, 14);
v_zeta_514_ = lean_ctor_get_uint8(v___x_499_, 15);
v_zetaDelta_515_ = lean_ctor_get_uint8(v___x_499_, 16);
v_zetaUnused_516_ = lean_ctor_get_uint8(v___x_499_, 17);
v_zetaHave_517_ = lean_ctor_get_uint8(v___x_499_, 18);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_551_ == 0)
{
v___x_519_ = v___x_499_;
v_isShared_520_ = v_isSharedCheck_551_;
goto v_resetjp_518_;
}
else
{
lean_dec(v___x_499_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_551_;
goto v_resetjp_518_;
}
v___jp_476_:
{
if (v_a_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_del_object(v___x_474_);
v___x_478_ = lean_box(0);
lean_inc(v_a_469_);
v___x_479_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_478_, v_val_470_, v_a_472_, v_a_469_, v___x_478_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_487_);
v___x_481_ = v___x_479_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_dec(v___x_479_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v_a_469_);
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_469_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_a_469_);
v_a_488_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_479_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_479_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v___x_497_; 
lean_dec(v_a_472_);
lean_dec(v_val_470_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v_a_469_);
v___x_497_ = v___x_474_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_469_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
v_resetjp_518_:
{
uint8_t v_trackZetaDelta_521_; lean_object* v_zetaDeltaSet_522_; lean_object* v_lctx_523_; lean_object* v_localInstances_524_; lean_object* v_defEqCtx_x3f_525_; lean_object* v_synthPendingDepth_526_; lean_object* v_canUnfold_x3f_527_; uint8_t v_univApprox_528_; uint8_t v_inTypeClassResolution_529_; uint8_t v_cacheInferType_530_; uint8_t v___x_531_; lean_object* v___x_533_; 
v_trackZetaDelta_521_ = lean_ctor_get_uint8(v_a_463_, sizeof(void*)*7);
v_zetaDeltaSet_522_ = lean_ctor_get(v_a_463_, 1);
v_lctx_523_ = lean_ctor_get(v_a_463_, 2);
v_localInstances_524_ = lean_ctor_get(v_a_463_, 3);
v_defEqCtx_x3f_525_ = lean_ctor_get(v_a_463_, 4);
v_synthPendingDepth_526_ = lean_ctor_get(v_a_463_, 5);
v_canUnfold_x3f_527_ = lean_ctor_get(v_a_463_, 6);
v_univApprox_528_ = lean_ctor_get_uint8(v_a_463_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_529_ = lean_ctor_get_uint8(v_a_463_, sizeof(void*)*7 + 2);
v_cacheInferType_530_ = lean_ctor_get_uint8(v_a_463_, sizeof(void*)*7 + 3);
v___x_531_ = 1;
if (v_isShared_520_ == 0)
{
v___x_533_ = v___x_519_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 0, v_foApprox_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 1, v_ctxApprox_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 2, v_quasiPatternApprox_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 3, v_constApprox_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 4, v_isDefEqStuckEx_504_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 5, v_unificationHints_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 6, v_proofIrrelevance_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 8, v_offsetCnstrs_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 9, v_transparency_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 10, v_etaStruct_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 11, v_univApprox_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 12, v_iota_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 13, v_beta_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 14, v_proj_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 15, v_zeta_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 16, v_zetaDelta_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 17, v_zetaUnused_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, 18, v_zetaHave_517_);
v___x_533_ = v_reuseFailAlloc_550_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
uint64_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_ctor_set_uint8(v___x_533_, 7, v___x_531_);
v___x_534_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set_uint64(v___x_535_, sizeof(void*)*1, v___x_534_);
lean_inc(v_canUnfold_x3f_527_);
lean_inc(v_synthPendingDepth_526_);
lean_inc(v_defEqCtx_x3f_525_);
lean_inc_ref(v_localInstances_524_);
lean_inc_ref(v_lctx_523_);
lean_inc(v_zetaDeltaSet_522_);
v___x_536_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v_zetaDeltaSet_522_);
lean_ctor_set(v___x_536_, 2, v_lctx_523_);
lean_ctor_set(v___x_536_, 3, v_localInstances_524_);
lean_ctor_set(v___x_536_, 4, v_defEqCtx_x3f_525_);
lean_ctor_set(v___x_536_, 5, v_synthPendingDepth_526_);
lean_ctor_set(v___x_536_, 6, v_canUnfold_x3f_527_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*7, v_trackZetaDelta_521_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*7 + 1, v_univApprox_528_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*7 + 2, v_inTypeClassResolution_529_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*7 + 3, v_cacheInferType_530_);
lean_inc(v_val_470_);
lean_inc(v_a_472_);
v___x_537_ = l_Lean_Meta_isExprDefEq(v_a_472_, v_val_470_, v___x_536_, v_a_464_, v_a_465_, v_a_466_);
lean_dec_ref(v___x_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; uint8_t v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref(v___x_537_);
v___x_539_ = lean_unbox(v_a_538_);
lean_dec(v_a_538_);
v_a_477_ = v___x_539_;
goto v___jp_476_;
}
else
{
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_540_; uint8_t v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_537_);
v___x_541_ = lean_unbox(v_a_540_);
lean_dec(v_a_540_);
v_a_477_ = v___x_541_;
goto v___jp_476_;
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_del_object(v___x_474_);
lean_dec(v_a_472_);
lean_dec(v_val_470_);
lean_dec(v_a_469_);
v_a_542_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_537_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_537_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
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
lean_dec(v_val_470_);
lean_dec(v_a_469_);
return v___x_471_;
}
}
}
else
{
lean_dec(v_expectedType_x3f_457_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object* v_stx_553_, lean_object* v_expectedType_x3f_554_, lean_object* v_mayPostpone_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
uint8_t v_mayPostpone_boxed_565_; lean_object* v_res_566_; 
v_mayPostpone_boxed_565_ = lean_unbox(v_mayPostpone_555_);
v_res_566_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v_stx_553_, v_expectedType_x3f_554_, v_mayPostpone_boxed_565_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
return v_res_566_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_box(0);
v___x_568_ = l_Lean_Elab_abortTacticExceptionId;
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___boxed(lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(lean_object* v_00_u03b1_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(lean_object* v_00_u03b1_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(v_00_u03b1_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object* v_mvarIds_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_box(0);
v___x_608_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_mvarIds_597_, v___x_607_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_619_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_619_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_619_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_619_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
uint8_t v___x_613_; 
v___x_613_ = lean_unbox(v_a_609_);
lean_dec(v_a_609_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = lean_box(0);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v___x_618_; 
lean_del_object(v___x_611_);
v___x_618_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg();
return v___x_618_;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_a_620_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_608_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_608_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object* v_mvarIds_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_mvarIds_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec_ref(v_mvarIds_628_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(lean_object* v___x_639_, lean_object* v_mvarCounterSaved_640_, lean_object* v_as_641_, size_t v_i_642_, size_t v_stop_643_, lean_object* v_b_644_){
_start:
{
lean_object* v___y_646_; uint8_t v___x_650_; 
v___x_650_ = lean_usize_dec_eq(v_i_642_, v_stop_643_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_index_653_; uint8_t v___x_654_; 
v___x_651_ = lean_array_uget_borrowed(v_as_641_, v_i_642_);
lean_inc(v___x_651_);
v___x_652_ = l_Lean_MetavarContext_getDecl(v___x_639_, v___x_651_);
v_index_653_ = lean_ctor_get(v___x_652_, 6);
lean_inc(v_index_653_);
lean_dec_ref(v___x_652_);
v___x_654_ = lean_nat_dec_le(v_mvarCounterSaved_640_, v_index_653_);
lean_dec(v_index_653_);
if (v___x_654_ == 0)
{
v___y_646_ = v_b_644_;
goto v___jp_645_;
}
else
{
lean_object* v___x_655_; 
lean_inc(v___x_651_);
v___x_655_ = lean_array_push(v_b_644_, v___x_651_);
v___y_646_ = v___x_655_;
goto v___jp_645_;
}
}
else
{
return v_b_644_;
}
v___jp_645_:
{
size_t v___x_647_; size_t v___x_648_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_642_, v___x_647_);
v_i_642_ = v___x_648_;
v_b_644_ = v___y_646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(lean_object* v___x_656_, lean_object* v_mvarCounterSaved_657_, lean_object* v_as_658_, lean_object* v_i_659_, lean_object* v_stop_660_, lean_object* v_b_661_){
_start:
{
size_t v_i_boxed_662_; size_t v_stop_boxed_663_; lean_object* v_res_664_; 
v_i_boxed_662_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_stop_boxed_663_ = lean_unbox_usize(v_stop_660_);
lean_dec(v_stop_660_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v___x_656_, v_mvarCounterSaved_657_, v_as_658_, v_i_boxed_662_, v_stop_boxed_663_, v_b_661_);
lean_dec_ref(v_as_658_);
lean_dec(v_mvarCounterSaved_657_);
lean_dec_ref(v___x_656_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object* v_mvarIds_667_, lean_object* v_mvarCounterSaved_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_671_ = lean_st_ref_get(v_a_669_);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_array_get_size(v_mvarIds_667_);
v___x_674_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_675_ = lean_nat_dec_lt(v___x_672_, v___x_673_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
lean_dec(v___x_671_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
return v___x_676_;
}
else
{
lean_object* v_mctx_677_; uint8_t v___x_678_; 
v_mctx_677_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_mctx_677_);
lean_dec(v___x_671_);
v___x_678_ = lean_nat_dec_le(v___x_673_, v___x_673_);
if (v___x_678_ == 0)
{
if (v___x_675_ == 0)
{
lean_object* v___x_679_; 
lean_dec_ref(v_mctx_677_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_674_);
return v___x_679_;
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_673_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_677_, v_mvarCounterSaved_668_, v_mvarIds_667_, v___x_680_, v___x_681_, v___x_674_);
lean_dec_ref(v_mctx_677_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
else
{
size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_684_ = ((size_t)0ULL);
v___x_685_ = lean_usize_of_nat(v___x_673_);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_filterOldMVars_spec__0(v_mctx_677_, v_mvarCounterSaved_668_, v_mvarIds_667_, v___x_684_, v___x_685_, v___x_674_);
lean_dec_ref(v_mctx_677_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(lean_object* v_mvarIds_688_, lean_object* v_mvarCounterSaved_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_688_, v_mvarCounterSaved_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec(v_mvarCounterSaved_689_);
lean_dec_ref(v_mvarIds_688_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object* v_mvarIds_693_, lean_object* v_mvarCounterSaved_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_mvarIds_693_, v_mvarCounterSaved_694_, v_a_696_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object* v_mvarIds_701_, lean_object* v_mvarCounterSaved_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_Tactic_filterOldMVars(v_mvarIds_701_, v_mvarCounterSaved_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_mvarCounterSaved_702_);
lean_dec_ref(v_mvarIds_701_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(lean_object* v_x_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
lean_inc(v___y_713_);
lean_inc_ref(v___y_712_);
lean_inc(v___y_711_);
lean_inc_ref(v___y_710_);
v___x_719_ = lean_apply_9(v_x_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, lean_box(0));
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed(lean_object* v_x_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0(v_x_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(lean_object* v_mvarId_731_, lean_object* v_x_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___f_742_; lean_object* v___x_743_; 
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
v___f_742_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_742_, 0, v_x_732_);
lean_closure_set(v___f_742_, 1, v___y_733_);
lean_closure_set(v___f_742_, 2, v___y_734_);
lean_closure_set(v___f_742_, 3, v___y_735_);
lean_closure_set(v___f_742_, 4, v___y_736_);
v___x_743_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_731_, v___f_742_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_743_) == 0)
{
return v___x_743_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg___boxed(lean_object* v_mvarId_752_, lean_object* v_x_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_752_, v_x_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(lean_object* v_00_u03b1_764_, lean_object* v_mvarId_765_, lean_object* v_x_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_mvarId_765_, v_x_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___boxed(lean_object* v_00_u03b1_777_, lean_object* v_mvarId_778_, lean_object* v_x_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0(v_00_u03b1_777_, v_mvarId_778_, v_x_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_789_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2));
v___x_795_ = l_Lean_stringToMessageData(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(lean_object* v_a_796_, lean_object* v_x_797_, lean_object* v_tacName_798_, uint8_t v_checkNewUnassigned_799_, lean_object* v_mvarCounter_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; 
lean_inc(v_a_796_);
v___x_810_ = l_Lean_MVarId_getType(v_a_796_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref(v___x_810_);
lean_inc(v_a_796_);
v___x_812_ = l_Lean_MVarId_getTag(v_a_796_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_812_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
lean_inc_ref(v___y_805_);
lean_inc(v___y_804_);
lean_inc_ref(v___y_803_);
lean_inc(v___y_802_);
lean_inc_ref(v___y_801_);
v___x_814_ = lean_apply_11(v_x_797_, v_a_811_, v_a_813_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, lean_box(0));
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
if (v_checkNewUnassigned_799_ == 0)
{
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
v___y_817_ = v___y_805_;
v___y_818_ = v___y_806_;
v___y_819_ = v___y_807_;
v___y_820_ = v___y_808_;
goto v___jp_816_;
}
else
{
lean_object* v___x_847_; 
lean_inc(v_a_815_);
v___x_847_ = l_Lean_Meta_getMVars(v_a_815_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___x_847_);
v___x_849_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_848_, v_mvarCounter_800_, v___y_806_);
lean_dec(v_a_848_);
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref(v___x_849_);
v___x_851_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_850_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v_a_850_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_dec_ref(v___x_851_);
v___y_817_ = v___y_805_;
v___y_818_ = v___y_806_;
v___y_819_ = v___y_807_;
v___y_820_ = v___y_808_;
goto v___jp_816_;
}
else
{
lean_dec(v_a_815_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v_tacName_798_);
lean_dec(v_a_796_);
return v___x_851_;
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_a_815_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v_tacName_798_);
lean_dec(v_a_796_);
v_a_852_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_847_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_847_);
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
v___jp_816_:
{
lean_object* v___x_821_; 
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v_a_815_);
lean_inc(v_a_796_);
v___x_821_ = lean_checked_assign(v_a_796_, v_a_815_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_838_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_838_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_838_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_838_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
uint8_t v___x_826_; 
v___x_826_ = lean_unbox(v_a_822_);
lean_dec(v_a_822_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_del_object(v___x_824_);
v___x_827_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1);
v___x_828_ = l_Lean_indentExpr(v_a_815_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3, &l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
v___x_833_ = l_Lean_Meta_throwTacticEx___redArg(v_tacName_798_, v_a_796_, v___x_832_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v___x_833_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v_a_815_);
lean_dec(v_tacName_798_);
lean_dec(v_a_796_);
v___x_834_ = lean_box(0);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_834_);
v___x_836_ = v___x_824_;
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
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v_a_815_);
lean_dec(v_tacName_798_);
lean_dec(v_a_796_);
v_a_839_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_821_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_821_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v_tacName_798_);
lean_dec(v_a_796_);
v_a_860_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_814_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_814_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
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
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_a_811_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v_tacName_798_);
lean_dec_ref(v_x_797_);
lean_dec(v_a_796_);
v_a_868_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_812_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_812_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v_tacName_798_);
lean_dec_ref(v_x_797_);
lean_dec(v_a_796_);
v_a_876_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_810_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_810_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(lean_object* v_a_884_, lean_object* v_x_885_, lean_object* v_tacName_886_, lean_object* v_checkNewUnassigned_887_, lean_object* v_mvarCounter_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_898_; lean_object* v_res_899_; 
v_checkNewUnassigned_boxed_898_ = lean_unbox(v_checkNewUnassigned_887_);
v_res_899_ = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(v_a_884_, v_x_885_, v_tacName_886_, v_checkNewUnassigned_boxed_898_, v_mvarCounter_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v_mvarCounter_888_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object* v_tacName_900_, lean_object* v_x_901_, uint8_t v_checkNewUnassigned_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_st_ref_get(v_a_908_);
v___x_913_ = l_Lean_Elab_Tactic_popMainGoal___redArg(v_a_904_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_mctx_914_; lean_object* v_a_915_; lean_object* v_mvarCounter_916_; lean_object* v___x_917_; lean_object* v___f_918_; lean_object* v___x_919_; 
v_mctx_914_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_mctx_914_);
lean_dec(v___x_912_);
v_a_915_ = lean_ctor_get(v___x_913_, 0);
lean_inc_n(v_a_915_, 3);
lean_dec_ref(v___x_913_);
v_mvarCounter_916_ = lean_ctor_get(v_mctx_914_, 3);
lean_inc(v_mvarCounter_916_);
lean_dec_ref(v_mctx_914_);
v___x_917_ = lean_box(v_checkNewUnassigned_902_);
v___f_918_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed), 14, 5);
lean_closure_set(v___f_918_, 0, v_a_915_);
lean_closure_set(v___f_918_, 1, v_x_901_);
lean_closure_set(v___f_918_, 2, v_tacName_900_);
lean_closure_set(v___f_918_, 3, v___x_917_);
lean_closure_set(v___f_918_, 4, v_mvarCounter_916_);
v___x_919_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_closeMainGoalUsing_spec__0___redArg(v_a_915_, v___f_918_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_dec(v_a_915_);
return v___x_919_;
}
else
{
lean_object* v_a_920_; uint8_t v___y_922_; uint8_t v___x_932_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
v___x_932_ = l_Lean_Exception_isInterrupt(v_a_920_);
if (v___x_932_ == 0)
{
uint8_t v___x_933_; 
lean_inc(v_a_920_);
v___x_933_ = l_Lean_Exception_isRuntime(v_a_920_);
v___y_922_ = v___x_933_;
goto v___jp_921_;
}
else
{
v___y_922_ = v___x_932_;
goto v___jp_921_;
}
v___jp_921_:
{
if (v___y_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec_ref(v___x_919_);
v___x_923_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_915_, v_a_904_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_923_, 0);
lean_dec(v_unused_931_);
v___x_925_ = v___x_923_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_dec(v___x_923_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 1);
lean_ctor_set(v___x_925_, 0, v_a_920_);
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_920_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_dec(v_a_920_);
return v___x_923_;
}
}
else
{
lean_dec(v_a_920_);
lean_dec(v_a_915_);
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v___x_912_);
lean_dec_ref(v_x_901_);
lean_dec(v_tacName_900_);
v_a_934_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_913_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_913_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object* v_tacName_942_, lean_object* v_x_943_, lean_object* v_checkNewUnassigned_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
uint8_t v_checkNewUnassigned_boxed_954_; lean_object* v_res_955_; 
v_checkNewUnassigned_boxed_954_ = lean_unbox(v_checkNewUnassigned_944_);
v_res_955_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v_tacName_942_, v_x_943_, v_checkNewUnassigned_boxed_954_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_955_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = lean_box(0);
v___x_957_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg(){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___closed__0);
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg___boxed(lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(lean_object* v_00_u03b1_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___boxed(lean_object* v_00_u03b1_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0(v_00_u03b1_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0(lean_object* v___x_986_, lean_object* v_type_987_, lean_object* v_x_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v_type_987_);
v___x_999_ = 0;
v___x_1000_ = l_Lean_Elab_Tactic_elabTermEnsuringType(v___x_986_, v___x_998_, v___x_999_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0___boxed(lean_object* v___x_1001_, lean_object* v_type_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_Elab_Tactic_evalExact___lam__0(v___x_1001_, v_type_1002_, v_x_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v_x_1003_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object* v_stx_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
lean_inc(v_stx_1025_);
v___x_1036_ = l_Lean_Syntax_isOfKind(v_stx_1025_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
lean_dec(v_stx_1025_);
v___x_1037_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1038_ = lean_unsigned_to_nat(1u);
v___x_1039_ = l_Lean_Syntax_getArg(v_stx_1025_, v___x_1038_);
lean_dec(v_stx_1025_);
v___f_1040_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1040_, 0, v___x_1039_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__5));
v___x_1042_ = l_Lean_Elab_Tactic_closeMainGoalUsing(v___x_1041_, v___f_1040_, v___x_1036_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___boxed(lean_object* v_stx_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Elab_Tactic_evalExact(v_stx_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1(){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1061_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExact___closed__4));
v___x_1063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1064_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___boxed), 10, 0);
v___x_1065_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1061_, v___x_1062_, v___x_1063_, v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___boxed(lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1();
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1));
v___x_1095_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6));
v___x_1096_ = l_Lean_addBuiltinDeclarationRanges(v___x_1094_, v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___boxed(lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3();
return v_res_1098_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(lean_object* v_mctx_1099_, lean_object* v_mvarId_u2081_1100_, lean_object* v_mvarId_u2082_1101_){
_start:
{
lean_object* v_decl_u2081_1102_; lean_object* v_index_1103_; lean_object* v_decl_u2082_1104_; lean_object* v_index_1105_; uint8_t v___x_1106_; 
lean_inc(v_mvarId_u2081_1100_);
v_decl_u2081_1102_ = l_Lean_MetavarContext_getDecl(v_mctx_1099_, v_mvarId_u2081_1100_);
v_index_1103_ = lean_ctor_get(v_decl_u2081_1102_, 6);
lean_inc(v_index_1103_);
lean_dec_ref(v_decl_u2081_1102_);
lean_inc(v_mvarId_u2082_1101_);
v_decl_u2082_1104_ = l_Lean_MetavarContext_getDecl(v_mctx_1099_, v_mvarId_u2082_1101_);
v_index_1105_ = lean_ctor_get(v_decl_u2082_1104_, 6);
lean_inc(v_index_1105_);
lean_dec_ref(v_decl_u2082_1104_);
v___x_1106_ = lean_nat_dec_eq(v_index_1103_, v_index_1105_);
if (v___x_1106_ == 0)
{
uint8_t v___x_1107_; 
lean_dec(v_mvarId_u2082_1101_);
lean_dec(v_mvarId_u2081_1100_);
v___x_1107_ = lean_nat_dec_lt(v_index_1103_, v_index_1105_);
lean_dec(v_index_1105_);
lean_dec(v_index_1103_);
return v___x_1107_;
}
else
{
uint8_t v___x_1108_; 
lean_dec(v_index_1105_);
lean_dec(v_index_1103_);
v___x_1108_ = l_Lean_Name_quickLt(v_mvarId_u2081_1100_, v_mvarId_u2082_1101_);
lean_dec(v_mvarId_u2082_1101_);
lean_dec(v_mvarId_u2081_1100_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(lean_object* v_mctx_1109_, lean_object* v_mvarId_u2081_1110_, lean_object* v_mvarId_u2082_1111_){
_start:
{
uint8_t v_res_1112_; lean_object* v_r_1113_; 
v_res_1112_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(v_mctx_1109_, v_mvarId_u2081_1110_, v_mvarId_u2082_1111_);
lean_dec_ref(v_mctx_1109_);
v_r_1113_ = lean_box(v_res_1112_);
return v_r_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(lean_object* v_mvarIds_1114_, lean_object* v_toPure_1115_, lean_object* v_mctx_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1117_ = lean_array_get_size(v_mvarIds_1114_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_nat_dec_eq(v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___f_1120_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___y_1129_; uint8_t v___x_1131_; 
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1120_, 0, v_mctx_1116_);
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_sub(v___x_1117_, v___x_1126_);
v___x_1131_ = lean_nat_dec_le(v___x_1118_, v___x_1127_);
if (v___x_1131_ == 0)
{
lean_inc(v___x_1127_);
v___y_1129_ = v___x_1127_;
goto v___jp_1128_;
}
else
{
v___y_1129_ = v___x_1118_;
goto v___jp_1128_;
}
v___jp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_1120_, v___x_1117_, v_mvarIds_1114_, v___y_1122_, v___y_1123_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_1123_);
v___x_1125_ = lean_apply_2(v_toPure_1115_, lean_box(0), v___x_1124_);
return v___x_1125_;
}
v___jp_1128_:
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_nat_dec_le(v___y_1129_, v___x_1127_);
if (v___x_1130_ == 0)
{
lean_dec(v___x_1127_);
lean_inc(v___y_1129_);
v___y_1122_ = v___y_1129_;
v___y_1123_ = v___y_1129_;
goto v___jp_1121_;
}
else
{
v___y_1122_ = v___y_1129_;
v___y_1123_ = v___x_1127_;
goto v___jp_1121_;
}
}
}
else
{
lean_object* v___x_1132_; 
lean_dec_ref(v_mctx_1116_);
v___x_1132_ = lean_apply_2(v_toPure_1115_, lean_box(0), v_mvarIds_1114_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_mvarIds_1135_){
_start:
{
lean_object* v_toApplicative_1136_; lean_object* v_toBind_1137_; lean_object* v_getMCtx_1138_; lean_object* v_toPure_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; 
v_toApplicative_1136_ = lean_ctor_get(v_inst_1134_, 0);
lean_inc_ref(v_toApplicative_1136_);
v_toBind_1137_ = lean_ctor_get(v_inst_1134_, 1);
lean_inc(v_toBind_1137_);
lean_dec_ref(v_inst_1134_);
v_getMCtx_1138_ = lean_ctor_get(v_inst_1133_, 0);
lean_inc(v_getMCtx_1138_);
lean_dec_ref(v_inst_1133_);
v_toPure_1139_ = lean_ctor_get(v_toApplicative_1136_, 1);
lean_inc(v_toPure_1139_);
lean_dec_ref(v_toApplicative_1136_);
v___f_1140_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1140_, 0, v_mvarIds_1135_);
lean_closure_set(v___f_1140_, 1, v_toPure_1139_);
v___x_1141_ = lean_apply_4(v_toBind_1137_, lean_box(0), lean_box(0), v_getMCtx_1138_, v___f_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_mvarIds_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1143_, v_inst_1144_, v_mvarIds_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_mvarIds_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1147_, v_inst_1148_, v_mvarIds_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object* v_m_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_mvarIds_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v_inst_1152_, v_inst_1153_, v_mvarIds_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v_mctx_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_st_ref_get(v___y_1157_);
v_mctx_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc_ref(v_mctx_1162_);
lean_dec(v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_mctx_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0___boxed(lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__0(v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1(lean_object* v_val_1170_, lean_object* v_toPure_1171_, lean_object* v_newMVarIds_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v_val_1170_);
lean_ctor_set(v___x_1173_, 1, v_newMVarIds_1172_);
v___x_1174_ = lean_apply_2(v_toPure_1171_, lean_box(0), v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2(lean_object* v___x_1175_, lean_object* v___x_1176_, lean_object* v_inst_1177_, lean_object* v_toBind_1178_, lean_object* v___f_1179_, lean_object* v_newMVarIds_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(v___x_1175_, v___x_1176_, v_newMVarIds_1180_);
v___x_1182_ = lean_apply_2(v_inst_1177_, lean_box(0), v___x_1181_);
v___x_1183_ = lean_apply_4(v_toBind_1178_, lean_box(0), lean_box(0), v___x_1182_, v___f_1179_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3(lean_object* v_mvarCounter_1184_, lean_object* v_inst_1185_, lean_object* v_toBind_1186_, lean_object* v___f_1187_, lean_object* v_newMVarIds_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_filterOldMVars___boxed), 7, 2);
lean_closure_set(v___x_1189_, 0, v_newMVarIds_1188_);
lean_closure_set(v___x_1189_, 1, v_mvarCounter_1184_);
v___x_1190_ = lean_apply_2(v_inst_1185_, lean_box(0), v___x_1189_);
v___x_1191_ = lean_apply_4(v_toBind_1186_, lean_box(0), lean_box(0), v___x_1190_, v___f_1187_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4(lean_object* v_toPure_1192_, lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v_inst_1195_, lean_object* v_toBind_1196_, lean_object* v_mvarCounter_1197_, lean_object* v_val_1198_){
_start:
{
lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_inc_ref(v_val_1198_);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1199_, 0, v_val_1198_);
lean_closure_set(v___f_1199_, 1, v_toPure_1192_);
lean_inc_n(v_toBind_1196_, 2);
lean_inc_n(v_inst_1195_, 2);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1200_, 0, v___x_1193_);
lean_closure_set(v___f_1200_, 1, v___x_1194_);
lean_closure_set(v___f_1200_, 2, v_inst_1195_);
lean_closure_set(v___f_1200_, 3, v_toBind_1196_);
lean_closure_set(v___f_1200_, 4, v___f_1199_);
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1201_, 0, v_mvarCounter_1197_);
lean_closure_set(v___f_1201_, 1, v_inst_1195_);
lean_closure_set(v___f_1201_, 2, v_toBind_1196_);
lean_closure_set(v___f_1201_, 3, v___f_1200_);
v___x_1202_ = lean_alloc_closure((void*)(l_Lean_Meta_getMVarsNoDelayed___boxed), 6, 1);
lean_closure_set(v___x_1202_, 0, v_val_1198_);
v___x_1203_ = lean_apply_2(v_inst_1195_, lean_box(0), v___x_1202_);
v___x_1204_ = lean_apply_4(v_toBind_1196_, lean_box(0), lean_box(0), v___x_1203_, v___f_1201_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5(lean_object* v_toPure_1205_, lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v_inst_1208_, lean_object* v_toBind_1209_, lean_object* v_k_1210_, lean_object* v_____do__lift_1211_){
_start:
{
lean_object* v_mvarCounter_1212_; lean_object* v___f_1213_; lean_object* v___x_1214_; 
v_mvarCounter_1212_ = lean_ctor_get(v_____do__lift_1211_, 3);
lean_inc(v_mvarCounter_1212_);
lean_dec_ref(v_____do__lift_1211_);
lean_inc(v_toBind_1209_);
v___f_1213_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1213_, 0, v_toPure_1205_);
lean_closure_set(v___f_1213_, 1, v___x_1206_);
lean_closure_set(v___f_1213_, 2, v___x_1207_);
lean_closure_set(v___f_1213_, 3, v_inst_1208_);
lean_closure_set(v___f_1213_, 4, v_toBind_1209_);
lean_closure_set(v___f_1213_, 5, v_mvarCounter_1212_);
v___x_1214_ = lean_apply_4(v_toBind_1209_, lean_box(0), lean_box(0), v_k_1210_, v___f_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0(void){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_instMonadEIO(lean_box(0));
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__0);
v___x_1217_ = l_StateRefT_x27_instMonad___redArg(v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___redArg(lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_k_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_toApplicative_1228_; lean_object* v_toFunctor_1229_; lean_object* v_toSeq_1230_; lean_object* v_toSeqLeft_1231_; lean_object* v_toSeqRight_1232_; lean_object* v___f_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_toApplicative_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1278_; 
v___x_1226_ = l_Lean_Meta_instMonadMCtxMetaM;
v___x_1227_ = lean_obj_once(&l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1, &l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__1);
v_toApplicative_1228_ = lean_ctor_get(v___x_1227_, 0);
v_toFunctor_1229_ = lean_ctor_get(v_toApplicative_1228_, 0);
v_toSeq_1230_ = lean_ctor_get(v_toApplicative_1228_, 2);
v_toSeqLeft_1231_ = lean_ctor_get(v_toApplicative_1228_, 3);
v_toSeqRight_1232_ = lean_ctor_get(v_toApplicative_1228_, 4);
v___f_1233_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__2));
v___f_1234_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1229_, 2);
v___f_1235_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1235_, 0, v_toFunctor_1229_);
v___f_1236_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1236_, 0, v_toFunctor_1229_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___f_1235_);
lean_ctor_set(v___x_1237_, 1, v___f_1236_);
lean_inc(v_toSeqRight_1232_);
v___f_1238_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1238_, 0, v_toSeqRight_1232_);
lean_inc(v_toSeqLeft_1231_);
v___f_1239_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1239_, 0, v_toSeqLeft_1231_);
lean_inc(v_toSeq_1230_);
v___f_1240_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1240_, 0, v_toSeq_1230_);
v___x_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1237_);
lean_ctor_set(v___x_1241_, 1, v___f_1233_);
lean_ctor_set(v___x_1241_, 2, v___f_1240_);
lean_ctor_set(v___x_1241_, 3, v___f_1239_);
lean_ctor_set(v___x_1241_, 4, v___f_1238_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v___f_1234_);
v___x_1243_ = l_StateRefT_x27_instMonad___redArg(v___x_1242_);
v_toApplicative_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1243_, 1);
lean_dec(v_unused_1279_);
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1278_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_toApplicative_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1278_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_toFunctor_1248_; lean_object* v_toSeq_1249_; lean_object* v_toSeqLeft_1250_; lean_object* v_toSeqRight_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1276_; 
v_toFunctor_1248_ = lean_ctor_get(v_toApplicative_1244_, 0);
v_toSeq_1249_ = lean_ctor_get(v_toApplicative_1244_, 2);
v_toSeqLeft_1250_ = lean_ctor_get(v_toApplicative_1244_, 3);
v_toSeqRight_1251_ = lean_ctor_get(v_toApplicative_1244_, 4);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_toApplicative_1244_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; 
v_unused_1277_ = lean_ctor_get(v_toApplicative_1244_, 1);
lean_dec(v_unused_1277_);
v___x_1253_ = v_toApplicative_1244_;
v_isShared_1254_ = v_isSharedCheck_1276_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_toSeqRight_1251_);
lean_inc(v_toSeqLeft_1250_);
lean_inc(v_toSeq_1249_);
lean_inc(v_toFunctor_1248_);
lean_dec(v_toApplicative_1244_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1276_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___f_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___x_1264_; 
v___f_1255_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__4));
v___f_1256_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__5));
lean_inc_ref(v_toFunctor_1248_);
v___f_1257_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1257_, 0, v_toFunctor_1248_);
v___f_1258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1258_, 0, v_toFunctor_1248_);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___f_1257_);
lean_ctor_set(v___x_1259_, 1, v___f_1258_);
v___f_1260_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1260_, 0, v_toSeqRight_1251_);
v___f_1261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1261_, 0, v_toSeqLeft_1250_);
v___f_1262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1262_, 0, v_toSeq_1249_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 4, v___f_1260_);
lean_ctor_set(v___x_1253_, 3, v___f_1261_);
lean_ctor_set(v___x_1253_, 2, v___f_1262_);
lean_ctor_set(v___x_1253_, 1, v___f_1255_);
lean_ctor_set(v___x_1253_, 0, v___x_1259_);
v___x_1264_ = v___x_1253_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v___f_1255_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v___f_1262_);
lean_ctor_set(v_reuseFailAlloc_1275_, 3, v___f_1261_);
lean_ctor_set(v_reuseFailAlloc_1275_, 4, v___f_1260_);
v___x_1264_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___f_1256_);
lean_ctor_set(v___x_1246_, 0, v___x_1264_);
v___x_1266_ = v___x_1246_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___f_1256_);
v___x_1266_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v_toApplicative_1267_; lean_object* v_toBind_1268_; lean_object* v_toPure_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___f_1272_; lean_object* v___x_1273_; 
v_toApplicative_1267_ = lean_ctor_get(v_inst_1223_, 0);
lean_inc_ref(v_toApplicative_1267_);
v_toBind_1268_ = lean_ctor_get(v_inst_1223_, 1);
lean_inc_n(v_toBind_1268_, 2);
lean_dec_ref(v_inst_1223_);
v_toPure_1269_ = lean_ctor_get(v_toApplicative_1267_, 1);
lean_inc(v_toPure_1269_);
lean_dec_ref(v_toApplicative_1267_);
v___f_1270_ = ((lean_object*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___closed__6));
lean_inc(v_inst_1224_);
v___x_1271_ = lean_apply_2(v_inst_1224_, lean_box(0), v___f_1270_);
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_collectFreshMVars___redArg___lam__5), 7, 6);
lean_closure_set(v___f_1272_, 0, v_toPure_1269_);
lean_closure_set(v___f_1272_, 1, v___x_1226_);
lean_closure_set(v___f_1272_, 2, v___x_1266_);
lean_closure_set(v___f_1272_, 3, v_inst_1224_);
lean_closure_set(v___f_1272_, 4, v_toBind_1268_);
lean_closure_set(v___f_1272_, 5, v_k_1225_);
v___x_1273_ = lean_apply_4(v_toBind_1268_, lean_box(0), lean_box(0), v___x_1271_, v___f_1272_);
return v___x_1273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars(lean_object* v_m_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_k_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Elab_Tactic_collectFreshMVars___redArg(v_inst_1281_, v_inst_1282_, v_k_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(lean_object* v_as_1285_, size_t v_i_1286_, size_t v_stop_1287_, lean_object* v_b_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_a_1297_; uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_eq(v_i_1286_, v_stop_1287_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1305_; 
v___x_1302_ = lean_array_uget_borrowed(v_as_1285_, v_i_1286_);
lean_inc(v___x_1302_);
v___x_1305_ = l_Lean_Elab_Term_isLetRecAuxMVar(v___x_1302_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; uint8_t v___x_1307_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref(v___x_1305_);
v___x_1307_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
if (v___x_1307_ == 0)
{
goto v___jp_1303_;
}
else
{
v_a_1297_ = v_b_1288_;
goto v___jp_1296_;
}
}
else
{
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1308_; uint8_t v___x_1309_; 
v_a_1308_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1308_);
lean_dec_ref(v___x_1305_);
v___x_1309_ = lean_unbox(v_a_1308_);
lean_dec(v_a_1308_);
if (v___x_1309_ == 0)
{
v_a_1297_ = v_b_1288_;
goto v___jp_1296_;
}
else
{
goto v___jp_1303_;
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_b_1288_);
v_a_1310_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1305_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1305_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
v___jp_1303_:
{
lean_object* v___x_1304_; 
lean_inc(v___x_1302_);
v___x_1304_ = lean_array_push(v_b_1288_, v___x_1302_);
v_a_1297_ = v___x_1304_;
goto v___jp_1296_;
}
}
else
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_b_1288_);
return v___x_1318_;
}
v___jp_1296_:
{
size_t v___x_1298_; size_t v___x_1299_; 
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1286_, v___x_1298_);
v_i_1286_ = v___x_1299_;
v_b_1288_ = v_a_1297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg___boxed(lean_object* v_as_1319_, lean_object* v_i_1320_, lean_object* v_stop_1321_, lean_object* v_b_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
size_t v_i_boxed_1330_; size_t v_stop_boxed_1331_; lean_object* v_res_1332_; 
v_i_boxed_1330_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_stop_boxed_1331_ = lean_unbox_usize(v_stop_1321_);
lean_dec(v_stop_1321_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1319_, v_i_boxed_1330_, v_stop_boxed_1331_, v_b_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec_ref(v_as_1319_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(lean_object* v_as_1333_, size_t v_i_1334_, size_t v_stop_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_eq(v_i_1334_, v_stop_1335_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_array_uget_borrowed(v_as_1333_, v_i_1334_);
lean_inc(v___x_1343_);
v___x_1344_ = l_Lean_MVarId_getKind(v___x_1343_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v_a_1347_; uint8_t v___x_1351_; uint8_t v___x_1352_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref(v___x_1344_);
v___x_1351_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
v___x_1352_ = l_Lean_MetavarKind_isNatural(v___x_1351_);
if (v___x_1352_ == 0)
{
v_a_1347_ = v_b_1336_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1353_; 
lean_inc(v___x_1343_);
v___x_1353_ = lean_array_push(v_b_1336_, v___x_1343_);
v_a_1347_ = v___x_1353_;
goto v___jp_1346_;
}
v___jp_1346_:
{
size_t v___x_1348_; size_t v___x_1349_; 
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = lean_usize_add(v_i_1334_, v___x_1348_);
v_i_1334_ = v___x_1349_;
v_b_1336_ = v_a_1347_;
goto _start;
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_b_1336_);
v_a_1354_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1344_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1344_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_b_1336_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg___boxed(lean_object* v_as_1363_, lean_object* v_i_1364_, lean_object* v_stop_1365_, lean_object* v_b_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
size_t v_i_boxed_1372_; size_t v_stop_boxed_1373_; lean_object* v_res_1374_; 
v_i_boxed_1372_ = lean_unbox_usize(v_i_1364_);
lean_dec(v_i_1364_);
v_stop_boxed_1373_ = lean_unbox_usize(v_stop_1365_);
lean_dec(v_stop_1365_);
v_res_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1363_, v_i_boxed_1372_, v_stop_boxed_1373_, v_b_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec_ref(v_as_1363_);
return v_res_1374_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v___x_1375_, lean_object* v_mvarId_u2081_1376_, lean_object* v_mvarId_u2082_1377_){
_start:
{
lean_object* v_decl_u2081_1378_; lean_object* v_index_1379_; lean_object* v_decl_u2082_1380_; lean_object* v_index_1381_; uint8_t v___x_1382_; 
lean_inc(v_mvarId_u2081_1376_);
v_decl_u2081_1378_ = l_Lean_MetavarContext_getDecl(v___x_1375_, v_mvarId_u2081_1376_);
v_index_1379_ = lean_ctor_get(v_decl_u2081_1378_, 6);
lean_inc(v_index_1379_);
lean_dec_ref(v_decl_u2081_1378_);
lean_inc(v_mvarId_u2082_1377_);
v_decl_u2082_1380_ = l_Lean_MetavarContext_getDecl(v___x_1375_, v_mvarId_u2082_1377_);
v_index_1381_ = lean_ctor_get(v_decl_u2082_1380_, 6);
lean_inc(v_index_1381_);
lean_dec_ref(v_decl_u2082_1380_);
v___x_1382_ = lean_nat_dec_eq(v_index_1379_, v_index_1381_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; 
lean_dec(v_mvarId_u2082_1377_);
lean_dec(v_mvarId_u2081_1376_);
v___x_1383_ = lean_nat_dec_lt(v_index_1379_, v_index_1381_);
lean_dec(v_index_1381_);
lean_dec(v_index_1379_);
return v___x_1383_;
}
else
{
uint8_t v___x_1384_; 
lean_dec(v_index_1381_);
lean_dec(v_index_1379_);
v___x_1384_ = l_Lean_Name_quickLt(v_mvarId_u2081_1376_, v_mvarId_u2082_1377_);
lean_dec(v_mvarId_u2082_1377_);
lean_dec(v_mvarId_u2081_1376_);
return v___x_1384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v___x_1385_, lean_object* v_mvarId_u2081_1386_, lean_object* v_mvarId_u2082_1387_){
_start:
{
uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_res_1388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1385_, v_mvarId_u2081_1386_, v_mvarId_u2082_1387_);
lean_dec_ref(v___x_1385_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___x_1390_, lean_object* v_hi_1391_, lean_object* v_pivot_1392_, lean_object* v_as_1393_, lean_object* v_i_1394_, lean_object* v_k_1395_){
_start:
{
uint8_t v___y_1397_; uint8_t v___x_1406_; 
v___x_1406_ = lean_nat_dec_lt(v_k_1395_, v_hi_1391_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec(v_k_1395_);
lean_dec(v_pivot_1392_);
v___x_1407_ = lean_array_fswap(v_as_1393_, v_i_1394_, v_hi_1391_);
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_i_1394_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; lean_object* v_decl_u2081_1410_; lean_object* v_index_1411_; lean_object* v_decl_u2082_1412_; lean_object* v_index_1413_; uint8_t v___x_1414_; 
v___x_1409_ = lean_array_fget_borrowed(v_as_1393_, v_k_1395_);
lean_inc(v___x_1409_);
v_decl_u2081_1410_ = l_Lean_MetavarContext_getDecl(v___x_1390_, v___x_1409_);
v_index_1411_ = lean_ctor_get(v_decl_u2081_1410_, 6);
lean_inc(v_index_1411_);
lean_dec_ref(v_decl_u2081_1410_);
lean_inc(v_pivot_1392_);
v_decl_u2082_1412_ = l_Lean_MetavarContext_getDecl(v___x_1390_, v_pivot_1392_);
v_index_1413_ = lean_ctor_get(v_decl_u2082_1412_, 6);
lean_inc(v_index_1413_);
lean_dec_ref(v_decl_u2082_1412_);
v___x_1414_ = lean_nat_dec_eq(v_index_1411_, v_index_1413_);
if (v___x_1414_ == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_nat_dec_lt(v_index_1411_, v_index_1413_);
lean_dec(v_index_1413_);
lean_dec(v_index_1411_);
v___y_1397_ = v___x_1415_;
goto v___jp_1396_;
}
else
{
uint8_t v___x_1416_; 
lean_dec(v_index_1413_);
lean_dec(v_index_1411_);
v___x_1416_ = l_Lean_Name_quickLt(v___x_1409_, v_pivot_1392_);
v___y_1397_ = v___x_1416_;
goto v___jp_1396_;
}
}
v___jp_1396_:
{
if (v___y_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_nat_add(v_k_1395_, v___x_1398_);
lean_dec(v_k_1395_);
v_k_1395_ = v___x_1399_;
goto _start;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1401_ = lean_array_fswap(v_as_1393_, v_i_1394_, v_k_1395_);
v___x_1402_ = lean_unsigned_to_nat(1u);
v___x_1403_ = lean_nat_add(v_i_1394_, v___x_1402_);
lean_dec(v_i_1394_);
v___x_1404_ = lean_nat_add(v_k_1395_, v___x_1402_);
lean_dec(v_k_1395_);
v_as_1393_ = v___x_1401_;
v_i_1394_ = v___x_1403_;
v_k_1395_ = v___x_1404_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___x_1417_, lean_object* v_hi_1418_, lean_object* v_pivot_1419_, lean_object* v_as_1420_, lean_object* v_i_1421_, lean_object* v_k_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1417_, v_hi_1418_, v_pivot_1419_, v_as_1420_, v_i_1421_, v_k_1422_);
lean_dec(v_hi_1418_);
lean_dec_ref(v___x_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(lean_object* v___x_1424_, lean_object* v_n_1425_, lean_object* v_as_1426_, lean_object* v_lo_1427_, lean_object* v_hi_1428_){
_start:
{
lean_object* v___y_1430_; uint8_t v___x_1440_; 
v___x_1440_ = lean_nat_dec_lt(v_lo_1427_, v_hi_1428_);
if (v___x_1440_ == 0)
{
lean_dec(v_lo_1427_);
return v_as_1426_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_mid_1443_; lean_object* v___y_1445_; lean_object* v___y_1451_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1441_ = lean_nat_add(v_lo_1427_, v_hi_1428_);
v___x_1442_ = lean_unsigned_to_nat(1u);
v_mid_1443_ = lean_nat_shiftr(v___x_1441_, v___x_1442_);
lean_dec(v___x_1441_);
v___x_1456_ = lean_array_fget_borrowed(v_as_1426_, v_mid_1443_);
v___x_1457_ = lean_array_fget_borrowed(v_as_1426_, v_lo_1427_);
lean_inc(v___x_1457_);
lean_inc(v___x_1456_);
v___x_1458_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1424_, v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
v___y_1451_ = v_as_1426_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_array_fswap(v_as_1426_, v_lo_1427_, v_mid_1443_);
v___y_1451_ = v___x_1459_;
goto v___jp_1450_;
}
v___jp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_array_fget_borrowed(v___y_1445_, v_mid_1443_);
v___x_1447_ = lean_array_fget_borrowed(v___y_1445_, v_hi_1428_);
lean_inc(v___x_1447_);
lean_inc(v___x_1446_);
v___x_1448_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1424_, v___x_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_dec(v_mid_1443_);
v___y_1430_ = v___y_1445_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_array_fswap(v___y_1445_, v_mid_1443_, v_hi_1428_);
lean_dec(v_mid_1443_);
v___y_1430_ = v___x_1449_;
goto v___jp_1429_;
}
}
v___jp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1452_ = lean_array_fget_borrowed(v___y_1451_, v_hi_1428_);
v___x_1453_ = lean_array_fget_borrowed(v___y_1451_, v_lo_1427_);
lean_inc(v___x_1453_);
lean_inc(v___x_1452_);
v___x_1454_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___lam__0(v___x_1424_, v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
v___y_1445_ = v___y_1451_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_array_fswap(v___y_1451_, v_lo_1427_, v_hi_1428_);
v___y_1445_ = v___x_1455_;
goto v___jp_1444_;
}
}
}
v___jp_1429_:
{
lean_object* v_pivot_1431_; lean_object* v___x_1432_; lean_object* v_fst_1433_; lean_object* v_snd_1434_; uint8_t v___x_1435_; 
v_pivot_1431_ = lean_array_fget(v___y_1430_, v_hi_1428_);
lean_inc_n(v_lo_1427_, 2);
v___x_1432_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1424_, v_hi_1428_, v_pivot_1431_, v___y_1430_, v_lo_1427_, v_lo_1427_);
v_fst_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_fst_1433_);
v_snd_1434_ = lean_ctor_get(v___x_1432_, 1);
lean_inc(v_snd_1434_);
lean_dec_ref(v___x_1432_);
v___x_1435_ = lean_nat_dec_le(v_hi_1428_, v_fst_1433_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1424_, v_n_1425_, v_snd_1434_, v_lo_1427_, v_fst_1433_);
v___x_1437_ = lean_unsigned_to_nat(1u);
v___x_1438_ = lean_nat_add(v_fst_1433_, v___x_1437_);
lean_dec(v_fst_1433_);
v_as_1426_ = v___x_1436_;
v_lo_1427_ = v___x_1438_;
goto _start;
}
else
{
lean_dec(v_fst_1433_);
lean_dec(v_lo_1427_);
return v_snd_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_1460_, lean_object* v_n_1461_, lean_object* v_as_1462_, lean_object* v_lo_1463_, lean_object* v_hi_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1460_, v_n_1461_, v_as_1462_, v_lo_1463_, v_hi_1464_);
lean_dec(v_hi_1464_);
lean_dec(v_n_1461_);
lean_dec_ref(v___x_1460_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(lean_object* v_mvarIds_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v_mctx_1470_; lean_object* v___x_1471_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1469_ = lean_st_ref_get(v___y_1467_);
v_mctx_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc_ref(v_mctx_1470_);
lean_dec(v___x_1469_);
v___x_1471_ = lean_array_get_size(v_mvarIds_1466_);
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_nat_dec_eq(v___x_1471_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___y_1482_; uint8_t v___x_1484_; 
v___x_1479_ = lean_unsigned_to_nat(1u);
v___x_1480_ = lean_nat_sub(v___x_1471_, v___x_1479_);
v___x_1484_ = lean_nat_dec_le(v___x_1477_, v___x_1480_);
if (v___x_1484_ == 0)
{
lean_inc(v___x_1480_);
v___y_1482_ = v___x_1480_;
goto v___jp_1481_;
}
else
{
v___y_1482_ = v___x_1477_;
goto v___jp_1481_;
}
v___jp_1481_:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_nat_dec_le(v___y_1482_, v___x_1480_);
if (v___x_1483_ == 0)
{
lean_dec(v___x_1480_);
lean_inc(v___y_1482_);
v___y_1473_ = v___y_1482_;
v___y_1474_ = v___y_1482_;
goto v___jp_1472_;
}
else
{
v___y_1473_ = v___y_1482_;
v___y_1474_ = v___x_1480_;
goto v___jp_1472_;
}
}
}
else
{
lean_object* v___x_1485_; 
lean_dec_ref(v_mctx_1470_);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_mvarIds_1466_);
return v___x_1485_;
}
v___jp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v_mctx_1470_, v___x_1471_, v_mvarIds_1466_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v_mctx_1470_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(lean_object* v_mvarIds_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1486_, v___y_1487_);
lean_dec(v___y_1487_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(lean_object* v_k_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v_mctx_1501_; lean_object* v_mvarCounter_1502_; lean_object* v___x_1503_; 
v___x_1500_ = lean_st_ref_get(v___y_1496_);
v_mctx_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc_ref(v_mctx_1501_);
lean_dec(v___x_1500_);
v_mvarCounter_1502_ = lean_ctor_get(v_mctx_1501_, 3);
lean_inc(v_mvarCounter_1502_);
lean_dec_ref(v_mctx_1501_);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1497_);
lean_inc(v___y_1496_);
lean_inc_ref(v___y_1495_);
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
v___x_1503_ = lean_apply_9(v_k_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, lean_box(0));
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc_n(v_a_1504_, 2);
lean_dec_ref(v___x_1503_);
v___x_1505_ = l_Lean_Meta_getMVarsNoDelayed(v_a_1504_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v_a_1508_; lean_object* v___x_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1518_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1506_, v_mvarCounter_1502_, v___y_1496_);
lean_dec(v_mvarCounter_1502_);
lean_dec(v_a_1506_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1507_);
v___x_1509_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_a_1508_, v___y_1496_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_a_1504_);
lean_ctor_set(v___x_1514_, 1, v_a_1510_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_a_1504_);
lean_dec(v_mvarCounter_1502_);
v_a_1519_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1505_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1505_);
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
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_mvarCounter_1502_);
v_a_1527_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1503_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1503_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(lean_object* v_k_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object* v_k_1546_, lean_object* v_parentTag_1547_, lean_object* v_tagSuffix_1548_, uint8_t v_allowNaturalHoles_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(v_k_1546_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v_fst_1561_; lean_object* v_snd_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1655_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1559_);
v_fst_1561_ = lean_ctor_get(v_a_1560_, 0);
v_snd_1562_ = lean_ctor_get(v_a_1560_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_a_1560_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1564_ = v_a_1560_;
v_isShared_1565_ = v_isSharedCheck_1655_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_snd_1562_);
lean_inc(v_fst_1561_);
lean_dec(v_a_1560_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1655_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1598_; lean_object* v_a_1599_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___x_1621_; lean_object* v_a_1623_; lean_object* v___y_1635_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1645_ = lean_array_get_size(v_snd_1562_);
v___x_1646_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1647_ = lean_nat_dec_lt(v___x_1621_, v___x_1645_);
if (v___x_1647_ == 0)
{
lean_dec(v_snd_1562_);
v_a_1623_ = v___x_1646_;
goto v___jp_1622_;
}
else
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_nat_dec_le(v___x_1645_, v___x_1645_);
if (v___x_1648_ == 0)
{
if (v___x_1647_ == 0)
{
lean_dec(v_snd_1562_);
v_a_1623_ = v___x_1646_;
goto v___jp_1622_;
}
else
{
size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = lean_usize_of_nat(v___x_1645_);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_1562_, v___x_1649_, v___x_1650_, v___x_1646_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_snd_1562_);
v___y_1635_ = v___x_1651_;
goto v___jp_1634_;
}
}
else
{
size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = lean_usize_of_nat(v___x_1645_);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_snd_1562_, v___x_1652_, v___x_1653_, v___x_1646_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_snd_1562_);
v___y_1635_ = v___x_1654_;
goto v___jp_1634_;
}
}
v___jp_1566_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_array_to_list(v___y_1567_);
v___x_1577_ = l_Lean_Elab_Tactic_tagUntaggedGoals(v_parentTag_1547_, v_tagSuffix_1548_, v___x_1576_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1587_; 
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; 
v_unused_1588_ = lean_ctor_get(v___x_1577_, 0);
lean_dec(v_unused_1588_);
v___x_1579_ = v___x_1577_;
v_isShared_1580_ = v_isSharedCheck_1587_;
goto v_resetjp_1578_;
}
else
{
lean_dec(v___x_1577_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1587_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 1, v___x_1576_);
v___x_1582_ = v___x_1564_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_fst_1561_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v___x_1576_);
v___x_1582_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1582_);
v___x_1584_ = v___x_1579_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v___x_1576_);
lean_del_object(v___x_1564_);
lean_dec(v_fst_1561_);
v_a_1589_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1577_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1577_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
v___jp_1597_:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1599_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec_ref(v_a_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_dec_ref(v___x_1600_);
v___y_1567_ = v___y_1598_;
v___y_1568_ = v_a_1550_;
v___y_1569_ = v_a_1551_;
v___y_1570_ = v_a_1552_;
v___y_1571_ = v_a_1553_;
v___y_1572_ = v_a_1554_;
v___y_1573_ = v_a_1555_;
v___y_1574_ = v_a_1556_;
v___y_1575_ = v_a_1557_;
goto v___jp_1566_;
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v___y_1598_);
lean_del_object(v___x_1564_);
lean_dec(v_fst_1561_);
lean_dec(v_tagSuffix_1548_);
lean_dec(v_parentTag_1547_);
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
v___jp_1609_:
{
if (lean_obj_tag(v___y_1611_) == 0)
{
lean_object* v_a_1612_; 
v_a_1612_ = lean_ctor_get(v___y_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___y_1611_);
v___y_1598_ = v___y_1610_;
v_a_1599_ = v_a_1612_;
goto v___jp_1597_;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v___y_1610_);
lean_del_object(v___x_1564_);
lean_dec(v_fst_1561_);
lean_dec(v_tagSuffix_1548_);
lean_dec(v_parentTag_1547_);
v_a_1613_ = lean_ctor_get(v___y_1611_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___y_1611_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___y_1611_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___y_1611_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
v___jp_1622_:
{
if (v_allowNaturalHoles_1549_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1624_ = lean_array_get_size(v_a_1623_);
v___x_1625_ = ((lean_object*)(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0));
v___x_1626_ = lean_nat_dec_lt(v___x_1621_, v___x_1624_);
if (v___x_1626_ == 0)
{
v___y_1598_ = v_a_1623_;
v_a_1599_ = v___x_1625_;
goto v___jp_1597_;
}
else
{
uint8_t v___x_1627_; 
v___x_1627_ = lean_nat_dec_le(v___x_1624_, v___x_1624_);
if (v___x_1627_ == 0)
{
if (v___x_1626_ == 0)
{
v___y_1598_ = v_a_1623_;
v_a_1599_ = v___x_1625_;
goto v___jp_1597_;
}
else
{
size_t v___x_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = lean_usize_of_nat(v___x_1624_);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_1623_, v___x_1628_, v___x_1629_, v___x_1625_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
v___y_1610_ = v_a_1623_;
v___y_1611_ = v___x_1630_;
goto v___jp_1609_;
}
}
else
{
size_t v___x_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = lean_usize_of_nat(v___x_1624_);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_a_1623_, v___x_1631_, v___x_1632_, v___x_1625_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
v___y_1610_ = v_a_1623_;
v___y_1611_ = v___x_1633_;
goto v___jp_1609_;
}
}
}
else
{
v___y_1567_ = v_a_1623_;
v___y_1568_ = v_a_1550_;
v___y_1569_ = v_a_1551_;
v___y_1570_ = v_a_1552_;
v___y_1571_ = v_a_1553_;
v___y_1572_ = v_a_1554_;
v___y_1573_ = v_a_1555_;
v___y_1574_ = v_a_1556_;
v___y_1575_ = v_a_1557_;
goto v___jp_1566_;
}
}
v___jp_1634_:
{
if (lean_obj_tag(v___y_1635_) == 0)
{
lean_object* v_a_1636_; 
v_a_1636_ = lean_ctor_get(v___y_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref(v___y_1635_);
v_a_1623_ = v_a_1636_;
goto v___jp_1622_;
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_del_object(v___x_1564_);
lean_dec(v_fst_1561_);
lean_dec(v_tagSuffix_1548_);
lean_dec(v_parentTag_1547_);
v_a_1637_ = lean_ctor_get(v___y_1635_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___y_1635_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___y_1635_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___y_1635_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_tagSuffix_1548_);
lean_dec(v_parentTag_1547_);
v_a_1656_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1559_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1559_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object* v_k_1664_, lean_object* v_parentTag_1665_, lean_object* v_tagSuffix_1666_, lean_object* v_allowNaturalHoles_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1677_; lean_object* v_res_1678_; 
v_allowNaturalHoles_boxed_1677_ = lean_unbox(v_allowNaturalHoles_1667_);
v_res_1678_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1664_, v_parentTag_1665_, v_tagSuffix_1666_, v_allowNaturalHoles_boxed_1677_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(lean_object* v_as_1679_, size_t v_i_1680_, size_t v_stop_1681_, lean_object* v_b_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___redArg(v_as_1679_, v_i_1680_, v_stop_1681_, v_b_1682_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1___boxed(lean_object* v_as_1693_, lean_object* v_i_1694_, lean_object* v_stop_1695_, lean_object* v_b_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
size_t v_i_boxed_1706_; size_t v_stop_boxed_1707_; lean_object* v_res_1708_; 
v_i_boxed_1706_ = lean_unbox_usize(v_i_1694_);
lean_dec(v_i_1694_);
v_stop_boxed_1707_ = lean_unbox_usize(v_stop_1695_);
lean_dec(v_stop_1695_);
v_res_1708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__1(v_as_1693_, v_i_boxed_1706_, v_stop_boxed_1707_, v_b_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec_ref(v_as_1693_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(lean_object* v_as_1709_, size_t v_i_1710_, size_t v_stop_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___redArg(v_as_1709_, v_i_1710_, v_stop_1711_, v_b_1712_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2___boxed(lean_object* v_as_1723_, lean_object* v_i_1724_, lean_object* v_stop_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
size_t v_i_boxed_1736_; size_t v_stop_boxed_1737_; lean_object* v_res_1738_; 
v_i_boxed_1736_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_stop_boxed_1737_ = lean_unbox_usize(v_stop_1725_);
lean_dec(v_stop_1725_);
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__2(v_as_1723_, v_i_boxed_1736_, v_stop_boxed_1737_, v_b_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v_as_1723_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(lean_object* v_mvarIds_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(v_mvarIds_1739_, v___y_1741_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(lean_object* v_mvarIds_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(v_mvarIds_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(lean_object* v___x_1753_, lean_object* v_n_1754_, lean_object* v_as_1755_, lean_object* v_lo_1756_, lean_object* v_hi_1757_, lean_object* v_w_1758_, lean_object* v_hlo_1759_, lean_object* v_hhi_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___redArg(v___x_1753_, v_n_1754_, v_as_1755_, v_lo_1756_, v_hi_1757_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1762_, lean_object* v_n_1763_, lean_object* v_as_1764_, lean_object* v_lo_1765_, lean_object* v_hi_1766_, lean_object* v_w_1767_, lean_object* v_hlo_1768_, lean_object* v_hhi_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1(v___x_1762_, v_n_1763_, v_as_1764_, v_lo_1765_, v_hi_1766_, v_w_1767_, v_hlo_1768_, v_hhi_1769_);
lean_dec(v_hi_1766_);
lean_dec(v_n_1763_);
lean_dec_ref(v___x_1762_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(lean_object* v___x_1771_, lean_object* v_n_1772_, lean_object* v_lo_1773_, lean_object* v_hi_1774_, lean_object* v_hhi_1775_, lean_object* v_pivot_1776_, lean_object* v_as_1777_, lean_object* v_i_1778_, lean_object* v_k_1779_, lean_object* v_ilo_1780_, lean_object* v_ik_1781_, lean_object* v_w_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1771_, v_hi_1774_, v_pivot_1776_, v_as_1777_, v_i_1778_, v_k_1779_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1784_, lean_object* v_n_1785_, lean_object* v_lo_1786_, lean_object* v_hi_1787_, lean_object* v_hhi_1788_, lean_object* v_pivot_1789_, lean_object* v_as_1790_, lean_object* v_i_1791_, lean_object* v_k_1792_, lean_object* v_ilo_1793_, lean_object* v_ik_1794_, lean_object* v_w_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___00Lean_Elab_Tactic_collectFreshMVars___at___00__private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__1_spec__4(v___x_1784_, v_n_1785_, v_lo_1786_, v_hi_1787_, v_hhi_1788_, v_pivot_1789_, v_as_1790_, v_i_1791_, v_k_1792_, v_ilo_1793_, v_ik_1794_, v_w_1795_);
lean_dec(v_hi_1787_);
lean_dec(v_lo_1786_);
lean_dec(v_n_1785_);
lean_dec_ref(v___x_1784_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object* v_k_1797_, lean_object* v_parentTag_1798_, lean_object* v_tagSuffix_1799_, uint8_t v_allowNaturalHoles_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
if (v_allowNaturalHoles_1800_ == 0)
{
lean_object* v___x_1810_; 
v___x_1810_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1797_, v_parentTag_1798_, v_tagSuffix_1799_, v_allowNaturalHoles_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1810_;
}
else
{
lean_object* v_declName_x3f_1811_; lean_object* v_macroStack_1812_; uint8_t v_mayPostpone_1813_; uint8_t v_errToSorry_1814_; lean_object* v_autoBoundImplicitContext_1815_; lean_object* v_autoBoundImplicitForbidden_1816_; lean_object* v_sectionVars_1817_; lean_object* v_sectionFVars_1818_; uint8_t v_implicitLambda_1819_; uint8_t v_heedElabAsElim_1820_; uint8_t v_isNoncomputableSection_1821_; uint8_t v_isMetaSection_1822_; uint8_t v_ignoreTCFailures_1823_; uint8_t v_inPattern_1824_; lean_object* v_tacSnap_x3f_1825_; uint8_t v_saveRecAppSyntax_1826_; uint8_t v_holesAsSyntheticOpaque_1827_; uint8_t v_checkDeprecated_1828_; lean_object* v_fixedTermElabs_1829_; uint8_t v___y_1831_; 
v_declName_x3f_1811_ = lean_ctor_get(v_a_1803_, 0);
v_macroStack_1812_ = lean_ctor_get(v_a_1803_, 1);
v_mayPostpone_1813_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8);
v_errToSorry_1814_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1815_ = lean_ctor_get(v_a_1803_, 2);
v_autoBoundImplicitForbidden_1816_ = lean_ctor_get(v_a_1803_, 3);
v_sectionVars_1817_ = lean_ctor_get(v_a_1803_, 4);
v_sectionFVars_1818_ = lean_ctor_get(v_a_1803_, 5);
v_implicitLambda_1819_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1820_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1821_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 4);
v_isMetaSection_1822_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_1823_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 6);
v_inPattern_1824_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1825_ = lean_ctor_get(v_a_1803_, 6);
v_saveRecAppSyntax_1826_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1827_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 9);
v_checkDeprecated_1828_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1829_ = lean_ctor_get(v_a_1803_, 7);
if (v_holesAsSyntheticOpaque_1827_ == 0)
{
v___y_1831_ = v_allowNaturalHoles_1800_;
goto v___jp_1830_;
}
else
{
v___y_1831_ = v_holesAsSyntheticOpaque_1827_;
goto v___jp_1830_;
}
v___jp_1830_:
{
lean_object* v___x_1832_; uint8_t v_foApprox_1833_; uint8_t v_ctxApprox_1834_; uint8_t v_quasiPatternApprox_1835_; uint8_t v_constApprox_1836_; uint8_t v_isDefEqStuckEx_1837_; uint8_t v_unificationHints_1838_; uint8_t v_proofIrrelevance_1839_; uint8_t v_offsetCnstrs_1840_; uint8_t v_transparency_1841_; uint8_t v_etaStruct_1842_; uint8_t v_univApprox_1843_; uint8_t v_iota_1844_; uint8_t v_beta_1845_; uint8_t v_proj_1846_; uint8_t v_zeta_1847_; uint8_t v_zetaDelta_1848_; uint8_t v_zetaUnused_1849_; uint8_t v_zetaHave_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1880_; 
v___x_1832_ = l_Lean_Meta_Context_config(v_a_1805_);
v_foApprox_1833_ = lean_ctor_get_uint8(v___x_1832_, 0);
v_ctxApprox_1834_ = lean_ctor_get_uint8(v___x_1832_, 1);
v_quasiPatternApprox_1835_ = lean_ctor_get_uint8(v___x_1832_, 2);
v_constApprox_1836_ = lean_ctor_get_uint8(v___x_1832_, 3);
v_isDefEqStuckEx_1837_ = lean_ctor_get_uint8(v___x_1832_, 4);
v_unificationHints_1838_ = lean_ctor_get_uint8(v___x_1832_, 5);
v_proofIrrelevance_1839_ = lean_ctor_get_uint8(v___x_1832_, 6);
v_offsetCnstrs_1840_ = lean_ctor_get_uint8(v___x_1832_, 8);
v_transparency_1841_ = lean_ctor_get_uint8(v___x_1832_, 9);
v_etaStruct_1842_ = lean_ctor_get_uint8(v___x_1832_, 10);
v_univApprox_1843_ = lean_ctor_get_uint8(v___x_1832_, 11);
v_iota_1844_ = lean_ctor_get_uint8(v___x_1832_, 12);
v_beta_1845_ = lean_ctor_get_uint8(v___x_1832_, 13);
v_proj_1846_ = lean_ctor_get_uint8(v___x_1832_, 14);
v_zeta_1847_ = lean_ctor_get_uint8(v___x_1832_, 15);
v_zetaDelta_1848_ = lean_ctor_get_uint8(v___x_1832_, 16);
v_zetaUnused_1849_ = lean_ctor_get_uint8(v___x_1832_, 17);
v_zetaHave_1850_ = lean_ctor_get_uint8(v___x_1832_, 18);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1852_ = v___x_1832_;
v_isShared_1853_ = v_isSharedCheck_1880_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1832_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1880_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
uint8_t v_trackZetaDelta_1854_; lean_object* v_zetaDeltaSet_1855_; lean_object* v_lctx_1856_; lean_object* v_localInstances_1857_; lean_object* v_defEqCtx_x3f_1858_; lean_object* v_synthPendingDepth_1859_; lean_object* v_canUnfold_x3f_1860_; uint8_t v_univApprox_1861_; uint8_t v_inTypeClassResolution_1862_; uint8_t v_cacheInferType_1863_; lean_object* v___x_1865_; 
v_trackZetaDelta_1854_ = lean_ctor_get_uint8(v_a_1805_, sizeof(void*)*7);
v_zetaDeltaSet_1855_ = lean_ctor_get(v_a_1805_, 1);
v_lctx_1856_ = lean_ctor_get(v_a_1805_, 2);
v_localInstances_1857_ = lean_ctor_get(v_a_1805_, 3);
v_defEqCtx_x3f_1858_ = lean_ctor_get(v_a_1805_, 4);
v_synthPendingDepth_1859_ = lean_ctor_get(v_a_1805_, 5);
v_canUnfold_x3f_1860_ = lean_ctor_get(v_a_1805_, 6);
v_univApprox_1861_ = lean_ctor_get_uint8(v_a_1805_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1862_ = lean_ctor_get_uint8(v_a_1805_, sizeof(void*)*7 + 2);
v_cacheInferType_1863_ = lean_ctor_get_uint8(v_a_1805_, sizeof(void*)*7 + 3);
if (v_isShared_1853_ == 0)
{
v___x_1865_ = v___x_1852_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 0, v_foApprox_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 1, v_ctxApprox_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 2, v_quasiPatternApprox_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 3, v_constApprox_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 4, v_isDefEqStuckEx_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 5, v_unificationHints_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 6, v_proofIrrelevance_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 8, v_offsetCnstrs_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 9, v_transparency_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 10, v_etaStruct_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 11, v_univApprox_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 12, v_iota_1844_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 13, v_beta_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 14, v_proj_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 15, v_zeta_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 16, v_zetaDelta_1848_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 17, v_zetaUnused_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1879_, 18, v_zetaHave_1850_);
v___x_1865_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
uint64_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_ctor_set_uint8(v___x_1865_, 7, v_allowNaturalHoles_1800_);
v___x_1866_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1865_);
lean_inc_ref(v_fixedTermElabs_1829_);
lean_inc(v_tacSnap_x3f_1825_);
lean_inc(v_sectionFVars_1818_);
lean_inc(v_sectionVars_1817_);
lean_inc_ref(v_autoBoundImplicitForbidden_1816_);
lean_inc(v_autoBoundImplicitContext_1815_);
lean_inc(v_macroStack_1812_);
lean_inc(v_declName_x3f_1811_);
v___x_1867_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1867_, 0, v_declName_x3f_1811_);
lean_ctor_set(v___x_1867_, 1, v_macroStack_1812_);
lean_ctor_set(v___x_1867_, 2, v_autoBoundImplicitContext_1815_);
lean_ctor_set(v___x_1867_, 3, v_autoBoundImplicitForbidden_1816_);
lean_ctor_set(v___x_1867_, 4, v_sectionVars_1817_);
lean_ctor_set(v___x_1867_, 5, v_sectionFVars_1818_);
lean_ctor_set(v___x_1867_, 6, v_tacSnap_x3f_1825_);
lean_ctor_set(v___x_1867_, 7, v_fixedTermElabs_1829_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8, v_mayPostpone_1813_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 1, v_errToSorry_1814_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 2, v_implicitLambda_1819_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 3, v_heedElabAsElim_1820_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1821_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 5, v_isMetaSection_1822_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 6, v_ignoreTCFailures_1823_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 7, v_inPattern_1824_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1826_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 9, v___y_1831_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*8 + 10, v_checkDeprecated_1828_);
v___x_1868_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1868_, 0, v___x_1865_);
lean_ctor_set_uint64(v___x_1868_, sizeof(void*)*1, v___x_1866_);
lean_inc(v_canUnfold_x3f_1860_);
lean_inc(v_synthPendingDepth_1859_);
lean_inc(v_defEqCtx_x3f_1858_);
lean_inc_ref(v_localInstances_1857_);
lean_inc_ref(v_lctx_1856_);
lean_inc(v_zetaDeltaSet_1855_);
v___x_1869_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v_zetaDeltaSet_1855_);
lean_ctor_set(v___x_1869_, 2, v_lctx_1856_);
lean_ctor_set(v___x_1869_, 3, v_localInstances_1857_);
lean_ctor_set(v___x_1869_, 4, v_defEqCtx_x3f_1858_);
lean_ctor_set(v___x_1869_, 5, v_synthPendingDepth_1859_);
lean_ctor_set(v___x_1869_, 6, v_canUnfold_x3f_1860_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*7, v_trackZetaDelta_1854_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*7 + 1, v_univApprox_1861_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1862_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*7 + 3, v_cacheInferType_1863_);
v___x_1870_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(v_k_1797_, v_parentTag_1798_, v_tagSuffix_1799_, v_allowNaturalHoles_1800_, v_a_1801_, v_a_1802_, v___x_1867_, v_a_1804_, v___x_1869_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec_ref(v___x_1869_);
lean_dec_ref(v___x_1867_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
else
{
return v___x_1870_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object* v_k_1881_, lean_object* v_parentTag_1882_, lean_object* v_tagSuffix_1883_, lean_object* v_allowNaturalHoles_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1894_; lean_object* v_res_1895_; 
v_allowNaturalHoles_boxed_1894_ = lean_unbox(v_allowNaturalHoles_1884_);
v_res_1895_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v_k_1881_, v_parentTag_1882_, v_tagSuffix_1883_, v_allowNaturalHoles_boxed_1894_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object* v_stx_1896_, lean_object* v_expectedType_x3f_1897_, lean_object* v_tagSuffix_1898_, uint8_t v_allowNaturalHoles_1899_, lean_object* v_parentTag_x3f_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_a_1911_; 
if (lean_obj_tag(v_parentTag_x3f_1900_) == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_Elab_Tactic_getMainTag___redArg(v_a_1902_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
v_a_1911_ = v_a_1917_;
goto v___jp_1910_;
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_tagSuffix_1898_);
lean_dec(v_expectedType_x3f_1897_);
lean_dec(v_stx_1896_);
v_a_1918_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1916_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1916_);
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
lean_object* v_val_1926_; 
v_val_1926_ = lean_ctor_get(v_parentTag_x3f_1900_, 0);
lean_inc(v_val_1926_);
lean_dec_ref(v_parentTag_x3f_1900_);
v_a_1911_ = v_val_1926_;
goto v___jp_1910_;
}
v___jp_1910_:
{
uint8_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1912_ = 0;
v___x_1913_ = lean_box(v___x_1912_);
v___x_1914_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermEnsuringType___boxed), 12, 3);
lean_closure_set(v___x_1914_, 0, v_stx_1896_);
lean_closure_set(v___x_1914_, 1, v_expectedType_x3f_1897_);
lean_closure_set(v___x_1914_, 2, v___x_1913_);
v___x_1915_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(v___x_1914_, v_a_1911_, v_tagSuffix_1898_, v_allowNaturalHoles_1899_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object* v_stx_1927_, lean_object* v_expectedType_x3f_1928_, lean_object* v_tagSuffix_1929_, lean_object* v_allowNaturalHoles_1930_, lean_object* v_parentTag_x3f_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_1941_; lean_object* v_res_1942_; 
v_allowNaturalHoles_boxed_1941_ = lean_unbox(v_allowNaturalHoles_1930_);
v_res_1942_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_stx_1927_, v_expectedType_x3f_1928_, v_tagSuffix_1929_, v_allowNaturalHoles_boxed_1941_, v_parentTag_x3f_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
return v_res_1942_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lam__0(lean_object* v_a_1943_, lean_object* v_x_1944_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Lean_instBEqMVarId_beq(v_x_1944_, v_a_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__0___boxed(lean_object* v_a_1946_, lean_object* v_x_1947_){
_start:
{
uint8_t v_res_1948_; lean_object* v_r_1949_; 
v_res_1948_ = l_Lean_Elab_Tactic_refineCore___lam__0(v_a_1946_, v_x_1947_);
lean_dec(v_x_1947_);
lean_dec(v_a_1946_);
v_r_1949_ = lean_box(v_res_1948_);
return v_r_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_x_1950_, lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v_ks_1954_; lean_object* v_vs_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1979_; 
v_ks_1954_ = lean_ctor_get(v_x_1950_, 0);
v_vs_1955_ = lean_ctor_get(v_x_1950_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_x_1950_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1957_ = v_x_1950_;
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_vs_1955_);
lean_inc(v_ks_1954_);
lean_dec(v_x_1950_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1959_ = lean_array_get_size(v_ks_1954_);
v___x_1960_ = lean_nat_dec_lt(v_x_1951_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_dec(v_x_1951_);
v___x_1961_ = lean_array_push(v_ks_1954_, v_x_1952_);
v___x_1962_ = lean_array_push(v_vs_1955_, v_x_1953_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v___x_1962_);
lean_ctor_set(v___x_1957_, 0, v___x_1961_);
v___x_1964_ = v___x_1957_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
else
{
lean_object* v_k_x27_1966_; uint8_t v___x_1967_; 
v_k_x27_1966_ = lean_array_fget_borrowed(v_ks_1954_, v_x_1951_);
v___x_1967_ = l_Lean_instBEqMVarId_beq(v_x_1952_, v_k_x27_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1969_; 
if (v_isShared_1958_ == 0)
{
v___x_1969_ = v___x_1957_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_ks_1954_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_vs_1955_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_unsigned_to_nat(1u);
v___x_1971_ = lean_nat_add(v_x_1951_, v___x_1970_);
lean_dec(v_x_1951_);
v_x_1950_ = v___x_1969_;
v_x_1951_ = v___x_1971_;
goto _start;
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1974_ = lean_array_fset(v_ks_1954_, v_x_1951_, v_x_1952_);
v___x_1975_ = lean_array_fset(v_vs_1955_, v_x_1951_, v_x_1953_);
lean_dec(v_x_1951_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v___x_1975_);
lean_ctor_set(v___x_1957_, 0, v___x_1974_);
v___x_1977_ = v___x_1957_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_n_1980_, lean_object* v_k_1981_, lean_object* v_v_1982_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_n_1980_, v___x_1983_, v_k_1981_, v_v_1982_);
return v___x_1984_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1985_; size_t v___x_1986_; size_t v___x_1987_; 
v___x_1985_ = ((size_t)5ULL);
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_shift_left(v___x_1986_, v___x_1985_);
return v___x_1987_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1988_; size_t v___x_1989_; size_t v___x_1990_; 
v___x_1988_ = ((size_t)1ULL);
v___x_1989_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1990_ = lean_usize_sub(v___x_1989_, v___x_1988_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1992_, size_t v_x_1993_, size_t v_x_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
if (lean_obj_tag(v_x_1992_) == 0)
{
lean_object* v_es_1997_; size_t v___x_1998_; size_t v___x_1999_; size_t v___x_2000_; size_t v___x_2001_; lean_object* v_j_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v_es_1997_ = lean_ctor_get(v_x_1992_, 0);
v___x_1998_ = ((size_t)5ULL);
v___x_1999_ = ((size_t)1ULL);
v___x_2000_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2001_ = lean_usize_land(v_x_1993_, v___x_2000_);
v_j_2002_ = lean_usize_to_nat(v___x_2001_);
v___x_2003_ = lean_array_get_size(v_es_1997_);
v___x_2004_ = lean_nat_dec_lt(v_j_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_dec(v_j_2002_);
lean_dec(v_x_1996_);
lean_dec(v_x_1995_);
return v_x_1992_;
}
else
{
lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2041_; 
lean_inc_ref(v_es_1997_);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v_x_1992_, 0);
lean_dec(v_unused_2042_);
v___x_2006_ = v_x_1992_;
v_isShared_2007_ = v_isSharedCheck_2041_;
goto v_resetjp_2005_;
}
else
{
lean_dec(v_x_1992_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2041_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v_v_2008_; lean_object* v___x_2009_; lean_object* v_xs_x27_2010_; lean_object* v___y_2012_; 
v_v_2008_ = lean_array_fget(v_es_1997_, v_j_2002_);
v___x_2009_ = lean_box(0);
v_xs_x27_2010_ = lean_array_fset(v_es_1997_, v_j_2002_, v___x_2009_);
switch(lean_obj_tag(v_v_2008_))
{
case 0:
{
lean_object* v_key_2017_; lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2028_; 
v_key_2017_ = lean_ctor_get(v_v_2008_, 0);
v_val_2018_ = lean_ctor_get(v_v_2008_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_v_2008_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2020_ = v_v_2008_;
v_isShared_2021_ = v_isSharedCheck_2028_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_inc(v_key_2017_);
lean_dec(v_v_2008_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2028_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Lean_instBEqMVarId_beq(v_x_1995_, v_key_2017_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_del_object(v___x_2020_);
v___x_2023_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2017_, v_val_2018_, v_x_1995_, v_x_1996_);
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
v___y_2012_ = v___x_2024_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2026_; 
lean_dec(v_val_2018_);
lean_dec(v_key_2017_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v_x_1996_);
lean_ctor_set(v___x_2020_, 0, v_x_1995_);
v___x_2026_ = v___x_2020_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_x_1995_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_x_1996_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
v___y_2012_ = v___x_2026_;
goto v___jp_2011_;
}
}
}
}
case 1:
{
lean_object* v_node_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2039_; 
v_node_2029_ = lean_ctor_get(v_v_2008_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_v_2008_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2031_ = v_v_2008_;
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_node_2029_);
lean_dec(v_v_2008_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
size_t v___x_2033_; size_t v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2033_ = lean_usize_shift_right(v_x_1993_, v___x_1998_);
v___x_2034_ = lean_usize_add(v_x_1994_, v___x_1999_);
v___x_2035_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_node_2029_, v___x_2033_, v___x_2034_, v_x_1995_, v_x_1996_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2035_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v___y_2012_ = v___x_2037_;
goto v___jp_2011_;
}
}
}
default: 
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2040_, 0, v_x_1995_);
lean_ctor_set(v___x_2040_, 1, v_x_1996_);
v___y_2012_ = v___x_2040_;
goto v___jp_2011_;
}
}
v___jp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = lean_array_fset(v_xs_x27_2010_, v_j_2002_, v___y_2012_);
lean_dec(v_j_2002_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2013_);
v___x_2015_ = v___x_2006_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
else
{
lean_object* v_ks_2043_; lean_object* v_vs_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2064_; 
v_ks_2043_ = lean_ctor_get(v_x_1992_, 0);
v_vs_2044_ = lean_ctor_get(v_x_1992_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2046_ = v_x_1992_;
v_isShared_2047_ = v_isSharedCheck_2064_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_vs_2044_);
lean_inc(v_ks_2043_);
lean_dec(v_x_1992_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2064_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_ks_2043_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_vs_2044_);
v___x_2049_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v_newNode_2050_; uint8_t v___y_2052_; size_t v___x_2058_; uint8_t v___x_2059_; 
v_newNode_2050_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v___x_2049_, v_x_1995_, v_x_1996_);
v___x_2058_ = ((size_t)7ULL);
v___x_2059_ = lean_usize_dec_le(v___x_2058_, v_x_1994_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2060_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2050_);
v___x_2061_ = lean_unsigned_to_nat(4u);
v___x_2062_ = lean_nat_dec_lt(v___x_2060_, v___x_2061_);
lean_dec(v___x_2060_);
v___y_2052_ = v___x_2062_;
goto v___jp_2051_;
}
else
{
v___y_2052_ = v___x_2059_;
goto v___jp_2051_;
}
v___jp_2051_:
{
if (v___y_2052_ == 0)
{
lean_object* v_ks_2053_; lean_object* v_vs_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_ks_2053_ = lean_ctor_get(v_newNode_2050_, 0);
lean_inc_ref(v_ks_2053_);
v_vs_2054_ = lean_ctor_get(v_newNode_2050_, 1);
lean_inc_ref(v_vs_2054_);
lean_dec_ref(v_newNode_2050_);
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_2057_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1994_, v_ks_2053_, v_vs_2054_, v___x_2055_, v___x_2056_);
lean_dec_ref(v_vs_2054_);
lean_dec_ref(v_ks_2053_);
return v___x_2057_;
}
else
{
return v_newNode_2050_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(size_t v_depth_2065_, lean_object* v_keys_2066_, lean_object* v_vals_2067_, lean_object* v_i_2068_, lean_object* v_entries_2069_){
_start:
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = lean_array_get_size(v_keys_2066_);
v___x_2071_ = lean_nat_dec_lt(v_i_2068_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_dec(v_i_2068_);
return v_entries_2069_;
}
else
{
lean_object* v_k_2072_; lean_object* v_v_2073_; uint64_t v___x_2074_; size_t v_h_2075_; size_t v___x_2076_; lean_object* v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; size_t v___x_2080_; size_t v_h_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_k_2072_ = lean_array_fget_borrowed(v_keys_2066_, v_i_2068_);
v_v_2073_ = lean_array_fget_borrowed(v_vals_2067_, v_i_2068_);
v___x_2074_ = l_Lean_instHashableMVarId_hash(v_k_2072_);
v_h_2075_ = lean_uint64_to_usize(v___x_2074_);
v___x_2076_ = ((size_t)5ULL);
v___x_2077_ = lean_unsigned_to_nat(1u);
v___x_2078_ = ((size_t)1ULL);
v___x_2079_ = lean_usize_sub(v_depth_2065_, v___x_2078_);
v___x_2080_ = lean_usize_mul(v___x_2076_, v___x_2079_);
v_h_2081_ = lean_usize_shift_right(v_h_2075_, v___x_2080_);
v___x_2082_ = lean_nat_add(v_i_2068_, v___x_2077_);
lean_dec(v_i_2068_);
lean_inc(v_v_2073_);
lean_inc(v_k_2072_);
v___x_2083_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_entries_2069_, v_h_2081_, v_depth_2065_, v_k_2072_, v_v_2073_);
v_i_2068_ = v___x_2082_;
v_entries_2069_ = v___x_2083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_depth_2085_, lean_object* v_keys_2086_, lean_object* v_vals_2087_, lean_object* v_i_2088_, lean_object* v_entries_2089_){
_start:
{
size_t v_depth_boxed_2090_; lean_object* v_res_2091_; 
v_depth_boxed_2090_ = lean_unbox_usize(v_depth_2085_);
lean_dec(v_depth_2085_);
v_res_2091_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_boxed_2090_, v_keys_2086_, v_vals_2087_, v_i_2088_, v_entries_2089_);
lean_dec_ref(v_vals_2087_);
lean_dec_ref(v_keys_2086_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_){
_start:
{
size_t v_x_3854__boxed_2097_; size_t v_x_3855__boxed_2098_; lean_object* v_res_2099_; 
v_x_3854__boxed_2097_ = lean_unbox_usize(v_x_2093_);
lean_dec(v_x_2093_);
v_x_3855__boxed_2098_ = lean_unbox_usize(v_x_2094_);
lean_dec(v_x_2094_);
v_res_2099_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2092_, v_x_3854__boxed_2097_, v_x_3855__boxed_2098_, v_x_2095_, v_x_2096_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_){
_start:
{
uint64_t v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v___x_2103_ = l_Lean_instHashableMVarId_hash(v_x_2101_);
v___x_2104_ = lean_uint64_to_usize(v___x_2103_);
v___x_2105_ = ((size_t)1ULL);
v___x_2106_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2100_, v___x_2104_, v___x_2105_, v_x_2101_, v_x_2102_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object* v_mvarId_2107_, lean_object* v_val_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v_mctx_2112_; lean_object* v_cache_2113_; lean_object* v_zetaDeltaFVarIds_2114_; lean_object* v_postponed_2115_; lean_object* v_diag_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2144_; 
v___x_2111_ = lean_st_ref_take(v___y_2109_);
v_mctx_2112_ = lean_ctor_get(v___x_2111_, 0);
v_cache_2113_ = lean_ctor_get(v___x_2111_, 1);
v_zetaDeltaFVarIds_2114_ = lean_ctor_get(v___x_2111_, 2);
v_postponed_2115_ = lean_ctor_get(v___x_2111_, 3);
v_diag_2116_ = lean_ctor_get(v___x_2111_, 4);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2118_ = v___x_2111_;
v_isShared_2119_ = v_isSharedCheck_2144_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_diag_2116_);
lean_inc(v_postponed_2115_);
lean_inc(v_zetaDeltaFVarIds_2114_);
lean_inc(v_cache_2113_);
lean_inc(v_mctx_2112_);
lean_dec(v___x_2111_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2144_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_depth_2120_; lean_object* v_levelAssignDepth_2121_; lean_object* v_lmvarCounter_2122_; lean_object* v_mvarCounter_2123_; lean_object* v_lDecls_2124_; lean_object* v_decls_2125_; lean_object* v_userNames_2126_; lean_object* v_lAssignment_2127_; lean_object* v_eAssignment_2128_; lean_object* v_dAssignment_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2143_; 
v_depth_2120_ = lean_ctor_get(v_mctx_2112_, 0);
v_levelAssignDepth_2121_ = lean_ctor_get(v_mctx_2112_, 1);
v_lmvarCounter_2122_ = lean_ctor_get(v_mctx_2112_, 2);
v_mvarCounter_2123_ = lean_ctor_get(v_mctx_2112_, 3);
v_lDecls_2124_ = lean_ctor_get(v_mctx_2112_, 4);
v_decls_2125_ = lean_ctor_get(v_mctx_2112_, 5);
v_userNames_2126_ = lean_ctor_get(v_mctx_2112_, 6);
v_lAssignment_2127_ = lean_ctor_get(v_mctx_2112_, 7);
v_eAssignment_2128_ = lean_ctor_get(v_mctx_2112_, 8);
v_dAssignment_2129_ = lean_ctor_get(v_mctx_2112_, 9);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_mctx_2112_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2131_ = v_mctx_2112_;
v_isShared_2132_ = v_isSharedCheck_2143_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_dAssignment_2129_);
lean_inc(v_eAssignment_2128_);
lean_inc(v_lAssignment_2127_);
lean_inc(v_userNames_2126_);
lean_inc(v_decls_2125_);
lean_inc(v_lDecls_2124_);
lean_inc(v_mvarCounter_2123_);
lean_inc(v_lmvarCounter_2122_);
lean_inc(v_levelAssignDepth_2121_);
lean_inc(v_depth_2120_);
lean_dec(v_mctx_2112_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2143_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2133_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_eAssignment_2128_, v_mvarId_2107_, v_val_2108_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 8, v___x_2133_);
v___x_2135_ = v___x_2131_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_depth_2120_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_levelAssignDepth_2121_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v_lmvarCounter_2122_);
lean_ctor_set(v_reuseFailAlloc_2142_, 3, v_mvarCounter_2123_);
lean_ctor_set(v_reuseFailAlloc_2142_, 4, v_lDecls_2124_);
lean_ctor_set(v_reuseFailAlloc_2142_, 5, v_decls_2125_);
lean_ctor_set(v_reuseFailAlloc_2142_, 6, v_userNames_2126_);
lean_ctor_set(v_reuseFailAlloc_2142_, 7, v_lAssignment_2127_);
lean_ctor_set(v_reuseFailAlloc_2142_, 8, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2142_, 9, v_dAssignment_2129_);
v___x_2135_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2135_);
v___x_2137_ = v___x_2118_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_cache_2113_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_zetaDeltaFVarIds_2114_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_postponed_2115_);
lean_ctor_set(v_reuseFailAlloc_2141_, 4, v_diag_2116_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_st_ref_set(v___y_2109_, v___x_2137_);
v___x_2139_ = lean_box(0);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg___boxed(lean_object* v_mvarId_2145_, lean_object* v_val_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_mvarId_2145_, v_val_2146_, v___y_2147_);
lean_dec(v___y_2147_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(lean_object* v_msgData_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; lean_object* v_env_2157_; lean_object* v___x_2158_; lean_object* v_mctx_2159_; lean_object* v_lctx_2160_; lean_object* v_options_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2156_ = lean_st_ref_get(v___y_2154_);
v_env_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc_ref(v_env_2157_);
lean_dec(v___x_2156_);
v___x_2158_ = lean_st_ref_get(v___y_2152_);
v_mctx_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc_ref(v_mctx_2159_);
lean_dec(v___x_2158_);
v_lctx_2160_ = lean_ctor_get(v___y_2151_, 2);
v_options_2161_ = lean_ctor_get(v___y_2153_, 2);
lean_inc_ref(v_options_2161_);
lean_inc_ref(v_lctx_2160_);
v___x_2162_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2162_, 0, v_env_2157_);
lean_ctor_set(v___x_2162_, 1, v_mctx_2159_);
lean_ctor_set(v___x_2162_, 2, v_lctx_2160_);
lean_ctor_set(v___x_2162_, 3, v_options_2161_);
v___x_2163_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v_msgData_2150_);
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2___boxed(lean_object* v_msgData_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msgData_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(lean_object* v_msg_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_ref_2178_; lean_object* v___x_2179_; lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2188_; 
v_ref_2178_ = lean_ctor_get(v___y_2175_, 5);
v___x_2179_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1_spec__2(v_msg_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_inc(v_ref_2178_);
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v_ref_2178_);
lean_ctor_set(v___x_2184_, 1, v_a_2180_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 1);
lean_ctor_set(v___x_2182_, 0, v___x_2184_);
v___x_2186_ = v___x_2182_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg___boxed(lean_object* v_msg_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2195_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__0));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__2));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l_Lean_Elab_Tactic_refineCore___lam__1___closed__4));
v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1(lean_object* v_stx_2205_, lean_object* v_tagSuffix_2206_, uint8_t v_allowNaturalHoles_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Elab_Tactic_getMainTarget(v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref(v___x_2217_);
v___x_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_a_2218_);
v___x_2220_ = lean_box(0);
v___x_2221_ = l_Lean_Elab_Tactic_elabTermWithHoles(v_stx_2205_, v___x_2219_, v_tagSuffix_2206_, v_allowNaturalHoles_2207_, v___x_2220_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v_fst_2223_; lean_object* v_snd_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2270_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___x_2221_);
v_fst_2223_ = lean_ctor_get(v_a_2222_, 0);
v_snd_2224_ = lean_ctor_get(v_a_2222_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_a_2222_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2226_ = v_a_2222_;
v_isShared_2227_ = v_isSharedCheck_2270_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_snd_2224_);
lean_inc(v_fst_2223_);
lean_dec(v_a_2222_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2270_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2209_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; lean_object* v_a_2231_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___x_2243_; uint8_t v___x_2257_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_n(v_a_2229_, 2);
lean_dec_ref(v___x_2228_);
v___x_2230_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_fst_2223_, v___y_2213_);
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref(v___x_2230_);
v___x_2243_ = l_Lean_mkMVar(v_a_2229_);
v___x_2257_ = lean_expr_eqv(v_a_2231_, v___x_2243_);
if (v___x_2257_ == 0)
{
lean_object* v___f_2258_; lean_object* v___x_2259_; 
lean_inc(v_a_2229_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2258_, 0, v_a_2229_);
lean_inc(v_a_2231_);
v___x_2259_ = l_Lean_FindMVar_main(v___f_2258_, v_a_2231_, v___x_2220_);
if (lean_obj_tag(v___x_2259_) == 1)
{
lean_dec_ref(v___x_2259_);
lean_dec(v_a_2229_);
lean_dec(v_snd_2224_);
goto v___jp_2244_;
}
else
{
lean_dec(v___x_2259_);
if (v___x_2257_ == 0)
{
lean_dec_ref(v___x_2243_);
lean_del_object(v___x_2226_);
v___y_2233_ = v___y_2208_;
v___y_2234_ = v___y_2209_;
v___y_2235_ = v___y_2210_;
v___y_2236_ = v___y_2211_;
v___y_2237_ = v___y_2212_;
v___y_2238_ = v___y_2213_;
v___y_2239_ = v___y_2214_;
v___y_2240_ = v___y_2215_;
goto v___jp_2232_;
}
else
{
lean_dec(v_a_2229_);
lean_dec(v_snd_2224_);
goto v___jp_2244_;
}
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v___x_2243_);
lean_dec(v_a_2231_);
lean_del_object(v___x_2226_);
v___x_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2260_, 0, v_a_2229_);
lean_ctor_set(v___x_2260_, 1, v_snd_2224_);
v___x_2261_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2260_, v___y_2209_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2261_;
}
v___jp_2232_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_a_2229_, v_a_2231_, v___y_2238_);
lean_dec_ref(v___x_2241_);
v___x_2242_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_snd_2224_, v___y_2234_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
return v___x_2242_;
}
v___jp_2244_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2245_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__1, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1);
v___x_2246_ = l_Lean_indentExpr(v_a_2231_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set_tag(v___x_2226_, 7);
lean_ctor_set(v___x_2226_, 1, v___x_2246_);
lean_ctor_set(v___x_2226_, 0, v___x_2245_);
v___x_2248_ = v___x_2226_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2249_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__3, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3);
v___x_2250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = l_Lean_MessageData_ofExpr(v___x_2243_);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2254_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2255_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_del_object(v___x_2226_);
lean_dec(v_snd_2224_);
lean_dec(v_fst_2223_);
v_a_2262_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2228_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2228_);
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
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
v_a_2271_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2221_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2221_);
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
lean_dec(v_tagSuffix_2206_);
lean_dec(v_stx_2205_);
v_a_2279_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2217_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2217_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___boxed(lean_object* v_stx_2287_, lean_object* v_tagSuffix_2288_, lean_object* v_allowNaturalHoles_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_2299_; lean_object* v_res_2300_; 
v_allowNaturalHoles_boxed_2299_ = lean_unbox(v_allowNaturalHoles_2289_);
v_res_2300_ = l_Lean_Elab_Tactic_refineCore___lam__1(v_stx_2287_, v_tagSuffix_2288_, v_allowNaturalHoles_boxed_2299_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object* v_stx_2301_, lean_object* v_tagSuffix_2302_, uint8_t v_allowNaturalHoles_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v___x_2313_; lean_object* v___f_2314_; lean_object* v___x_2315_; 
v___x_2313_ = lean_box(v_allowNaturalHoles_2303_);
v___f_2314_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__1___boxed), 12, 3);
lean_closure_set(v___f_2314_, 0, v_stx_2301_);
lean_closure_set(v___f_2314_, 1, v_tagSuffix_2302_);
lean_closure_set(v___f_2314_, 2, v___x_2313_);
v___x_2315_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2314_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object* v_stx_2316_, lean_object* v_tagSuffix_2317_, lean_object* v_allowNaturalHoles_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
uint8_t v_allowNaturalHoles_boxed_2328_; lean_object* v_res_2329_; 
v_allowNaturalHoles_boxed_2328_ = lean_unbox(v_allowNaturalHoles_2318_);
v_res_2329_ = l_Lean_Elab_Tactic_refineCore(v_stx_2316_, v_tagSuffix_2317_, v_allowNaturalHoles_boxed_2328_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(lean_object* v_mvarId_2330_, lean_object* v_val_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___redArg(v_mvarId_2330_, v_val_2331_, v___y_2337_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0___boxed(lean_object* v_mvarId_2342_, lean_object* v_val_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0(v_mvarId_2342_, v_val_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(lean_object* v_00_u03b1_2354_, lean_object* v_msg_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v_msg_2355_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___boxed(lean_object* v_00_u03b1_2366_, lean_object* v_msg_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1(v_00_u03b1_2366_, v_msg_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0(lean_object* v_00_u03b2_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0___redArg(v_x_2379_, v_x_2380_, v_x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2383_, lean_object* v_x_2384_, size_t v_x_2385_, size_t v_x_2386_, lean_object* v_x_2387_, lean_object* v_x_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___redArg(v_x_2384_, v_x_2385_, v_x_2386_, v_x_2387_, v_x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_, lean_object* v_x_2394_, lean_object* v_x_2395_){
_start:
{
size_t v_x_4410__boxed_2396_; size_t v_x_4411__boxed_2397_; lean_object* v_res_2398_; 
v_x_4410__boxed_2396_ = lean_unbox_usize(v_x_2392_);
lean_dec(v_x_2392_);
v_x_4411__boxed_2397_ = lean_unbox_usize(v_x_2393_);
lean_dec(v_x_2393_);
v_res_2398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1(v_00_u03b2_2390_, v_x_2391_, v_x_4410__boxed_2396_, v_x_4411__boxed_2397_, v_x_2394_, v_x_2395_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2399_, lean_object* v_n_2400_, lean_object* v_k_2401_, lean_object* v_v_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4___redArg(v_n_2400_, v_k_2401_, v_v_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2404_, size_t v_depth_2405_, lean_object* v_keys_2406_, lean_object* v_vals_2407_, lean_object* v_heq_2408_, lean_object* v_i_2409_, lean_object* v_entries_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___redArg(v_depth_2405_, v_keys_2406_, v_vals_2407_, v_i_2409_, v_entries_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2412_, lean_object* v_depth_2413_, lean_object* v_keys_2414_, lean_object* v_vals_2415_, lean_object* v_heq_2416_, lean_object* v_i_2417_, lean_object* v_entries_2418_){
_start:
{
size_t v_depth_boxed_2419_; lean_object* v_res_2420_; 
v_depth_boxed_2419_ = lean_unbox_usize(v_depth_2413_);
lean_dec(v_depth_2413_);
v_res_2420_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_2412_, v_depth_boxed_2419_, v_keys_2414_, v_vals_2415_, v_heq_2416_, v_i_2417_, v_entries_2418_);
lean_dec_ref(v_vals_2415_);
lean_dec_ref(v_keys_2414_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_2421_, lean_object* v_x_2422_, lean_object* v_x_2423_, lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_refineCore_spec__0_spec__0_spec__1_spec__4_spec__5___redArg(v_x_2422_, v_x_2423_, v_x_2424_, v_x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object* v_stx_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2445_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__1));
lean_inc(v_stx_2435_);
v___x_2446_ = l_Lean_Syntax_isOfKind(v_stx_2435_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; 
lean_dec(v_stx_2435_);
v___x_2447_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2447_;
}
else
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2448_ = lean_unsigned_to_nat(1u);
v___x_2449_ = l_Lean_Syntax_getArg(v_stx_2435_, v___x_2448_);
lean_dec(v_stx_2435_);
v___x_2450_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__2));
v___x_2451_ = 0;
v___x_2452_ = l_Lean_Elab_Tactic_refineCore(v___x_2449_, v___x_2450_, v___x_2451_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
return v___x_2452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___boxed(lean_object* v_stx_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Elab_Tactic_evalRefine(v_stx_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1(){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2471_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2472_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine___closed__1));
v___x_2473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1));
v___x_2474_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine___boxed), 10, 0);
v___x_2475_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2471_, v___x_2472_, v___x_2473_, v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___boxed(lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1();
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3(){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1));
v___x_2505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6));
v___x_2506_ = l_Lean_addBuiltinDeclarationRanges(v___x_2504_, v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___boxed(lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3();
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object* v_stx_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__1));
lean_inc(v_stx_2517_);
v___x_2528_ = l_Lean_Syntax_isOfKind(v_stx_2517_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; 
lean_dec(v_stx_2517_);
v___x_2529_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2529_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2530_ = lean_unsigned_to_nat(1u);
v___x_2531_ = l_Lean_Syntax_getArg(v_stx_2517_, v___x_2530_);
lean_dec(v_stx_2517_);
v___x_2532_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__2));
v___x_2533_ = l_Lean_Elab_Tactic_refineCore(v___x_2531_, v___x_2532_, v___x_2528_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___boxed(lean_object* v_stx_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Elab_Tactic_evalRefine_x27(v_stx_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2552_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2553_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRefine_x27___closed__1));
v___x_2554_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1));
v___x_2555_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine_x27___boxed), 10, 0);
v___x_2556_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2552_, v___x_2553_, v___x_2554_, v___x_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___boxed(lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1();
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3(){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1));
v___x_2586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6));
v___x_2587_ = l_Lean_addBuiltinDeclarationRanges(v___x_2585_, v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___boxed(lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3();
return v_res_2589_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0));
v___x_2592_ = l_Lean_stringToMessageData(v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0(uint8_t v___x_2593_, lean_object* v_stx_2594_, lean_object* v___x_2595_, uint8_t v___x_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
if (v___x_2593_ == 0)
{
lean_object* v___x_2606_; 
lean_dec_ref(v___x_2595_);
v___x_2606_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_2606_;
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2607_ = lean_unsigned_to_nat(1u);
v___x_2608_ = l_Lean_Syntax_getArg(v_stx_2594_, v___x_2607_);
v___x_2609_ = lean_box(0);
v___x_2610_ = l_Lean_Name_mkStr1(v___x_2595_);
v___x_2611_ = l_Lean_Elab_Tactic_elabTermWithHoles(v___x_2608_, v___x_2609_, v___x_2610_, v___x_2596_, v___x_2609_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v_fst_2613_; lean_object* v_snd_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2662_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref(v___x_2611_);
v_fst_2613_ = lean_ctor_get(v_a_2612_, 0);
v_snd_2614_ = lean_ctor_get(v_a_2612_, 1);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_a_2612_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2616_ = v_a_2612_;
v_isShared_2617_ = v_isSharedCheck_2662_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_snd_2614_);
lean_inc(v_fst_2613_);
lean_dec(v_a_2612_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2662_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = l_Lean_Expr_getLambdaBody(v_fst_2613_);
v___x_2619_ = l_Lean_Expr_getAppFn(v___x_2618_);
lean_dec_ref(v___x_2618_);
if (lean_obj_tag(v___x_2619_) == 1)
{
lean_object* v_fvarId_2620_; lean_object* v___x_2621_; 
v_fvarId_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_fvarId_2620_);
lean_dec_ref(v___x_2619_);
v___x_2621_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2598_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2623_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref(v___x_2621_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc(v_fst_2613_);
v___x_2623_ = lean_infer_type(v_fst_2613_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref(v___x_2623_);
v___x_2625_ = l_Lean_Expr_headBeta(v_a_2624_);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
v___x_2627_ = l_Lean_MVarId_replace(v_a_2622_, v_fvarId_2620_, v_fst_2613_, v___x_2626_, v___x_2609_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v_mvarId_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v_mvarId_2629_ = lean_ctor_get(v_a_2628_, 1);
lean_inc(v_mvarId_2629_);
lean_dec(v_a_2628_);
v___x_2630_ = lean_box(0);
if (v_isShared_2617_ == 0)
{
lean_ctor_set_tag(v___x_2616_, 1);
lean_ctor_set(v___x_2616_, 1, v___x_2630_);
lean_ctor_set(v___x_2616_, 0, v_mvarId_2629_);
v___x_2632_ = v___x_2616_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_mvarId_2629_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = l_List_appendTR___redArg(v_snd_2614_, v___x_2632_);
v___x_2634_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2633_, v___y_2598_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2634_;
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_del_object(v___x_2616_);
lean_dec(v_snd_2614_);
v_a_2636_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2627_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2627_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_a_2622_);
lean_dec(v_fvarId_2620_);
lean_del_object(v___x_2616_);
lean_dec(v_snd_2614_);
lean_dec(v_fst_2613_);
v_a_2644_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2623_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2623_);
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
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v_fvarId_2620_);
lean_del_object(v___x_2616_);
lean_dec(v_snd_2614_);
lean_dec(v_fst_2613_);
v_a_2652_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2621_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2621_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2616_);
lean_dec(v_snd_2614_);
lean_dec(v_fst_2613_);
v___x_2660_ = lean_obj_once(&l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1, &l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1);
v___x_2661_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2660_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2661_;
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
v_a_2663_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2611_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2611_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed(lean_object* v___x_2671_, lean_object* v_stx_2672_, lean_object* v___x_2673_, lean_object* v___x_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v___x_1129__boxed_2684_; uint8_t v___x_1131__boxed_2685_; lean_object* v_res_2686_; 
v___x_1129__boxed_2684_ = lean_unbox(v___x_2671_);
v___x_1131__boxed_2685_ = lean_unbox(v___x_2674_);
v_res_2686_ = l_Lean_Elab_Tactic_evalSpecialize___lam__0(v___x_1129__boxed_2684_, v_stx_2672_, v___x_2673_, v___x_1131__boxed_2685_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v_stx_2672_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object* v_stx_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___y_2709_; lean_object* v___x_2710_; 
v___x_2703_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__0));
v___x_2704_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__1));
lean_inc(v_stx_2693_);
v___x_2705_ = l_Lean_Syntax_isOfKind(v_stx_2693_, v___x_2704_);
v___x_2706_ = 1;
v___x_2707_ = lean_box(v___x_2705_);
v___x_2708_ = lean_box(v___x_2706_);
v___y_2709_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed), 13, 4);
lean_closure_set(v___y_2709_, 0, v___x_2707_);
lean_closure_set(v___y_2709_, 1, v_stx_2693_);
lean_closure_set(v___y_2709_, 2, v___x_2703_);
lean_closure_set(v___y_2709_, 3, v___x_2708_);
v___x_2710_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_2709_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___boxed(lean_object* v_stx_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_Elab_Tactic_evalSpecialize(v_stx_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2729_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2730_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSpecialize___closed__1));
v___x_2731_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1));
v___x_2732_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___boxed), 10, 0);
v___x_2733_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2729_, v___x_2730_, v___x_2731_, v___x_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___boxed(lean_object* v_a_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1();
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3(){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1));
v___x_2762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6));
v___x_2763_ = l_Lean_addBuiltinDeclarationRanges(v___x_2761_, v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___boxed(lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3();
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object* v_stx_2767_, uint8_t v_mayPostpone_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; uint8_t v___x_2789_; 
v___x_2789_ = l_Lean_Syntax_isIdent(v_stx_2767_);
if (v___x_2789_ == 0)
{
v___y_2779_ = v_a_2769_;
v___y_2780_ = v_a_2770_;
v___y_2781_ = v_a_2771_;
v___y_2782_ = v_a_2772_;
v___y_2783_ = v_a_2773_;
v___y_2784_ = v_a_2774_;
v___y_2785_ = v_a_2775_;
v___y_2786_ = v_a_2776_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = ((lean_object*)(l_Lean_Elab_Tactic_elabTermForApply___closed__0));
lean_inc(v_stx_2767_);
v___x_2791_ = l_Lean_Elab_Term_resolveId_x3f(v_stx_2767_, v___x_2790_, v___x_2789_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2800_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
if (lean_obj_tag(v_a_2792_) == 1)
{
lean_object* v_val_2796_; lean_object* v___x_2798_; 
lean_dec(v_stx_2767_);
v_val_2796_ = lean_ctor_get(v_a_2792_, 0);
lean_inc(v_val_2796_);
lean_dec_ref(v_a_2792_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v_val_2796_);
v___x_2798_ = v___x_2794_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_val_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
else
{
lean_del_object(v___x_2794_);
lean_dec(v_a_2792_);
v___y_2779_ = v_a_2769_;
v___y_2780_ = v_a_2770_;
v___y_2781_ = v_a_2771_;
v___y_2782_ = v_a_2772_;
v___y_2783_ = v_a_2773_;
v___y_2784_ = v_a_2774_;
v___y_2785_ = v_a_2775_;
v___y_2786_ = v_a_2776_;
goto v___jp_2778_;
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_stx_2767_);
v_a_2801_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2791_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2791_);
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
v___jp_2778_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_box(0);
v___x_2788_ = l_Lean_Elab_Tactic_elabTerm(v_stx_2767_, v___x_2787_, v_mayPostpone_2768_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object* v_stx_2809_, lean_object* v_mayPostpone_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
uint8_t v_mayPostpone_boxed_2820_; lean_object* v_res_2821_; 
v_mayPostpone_boxed_2820_ = lean_unbox(v_mayPostpone_2810_);
v_res_2821_ = l_Lean_Elab_Tactic_elabTermForApply(v_stx_2809_, v_mayPostpone_boxed_2820_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
return v_res_2821_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0));
v___x_2824_ = l_Lean_stringToMessageData(v___x_2823_);
return v___x_2824_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2));
v___x_2827_ = l_Lean_stringToMessageData(v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0(lean_object* v___x_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2853_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2853_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2853_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
if (lean_obj_tag(v_a_2839_) == 1)
{
lean_object* v_fvarId_2843_; lean_object* v___x_2845_; 
v_fvarId_2843_ = lean_ctor_get(v_a_2839_, 0);
lean_inc(v_fvarId_2843_);
lean_dec_ref(v_a_2839_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v_fvarId_2843_);
v___x_2845_ = v___x_2841_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_fvarId_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
lean_del_object(v___x_2841_);
v___x_2847_ = lean_obj_once(&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1, &l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1);
v___x_2848_ = l_Lean_MessageData_ofExpr(v_a_2839_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_obj_once(&l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3, &l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_2851_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
return v___x_2852_;
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
v_a_2854_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2838_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2838_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___boxed(lean_object* v___x_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Elab_Tactic_getFVarId___lam__0(v___x_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object* v_id_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_fileName_2883_; lean_object* v_fileMap_2884_; lean_object* v_options_2885_; lean_object* v_currRecDepth_2886_; lean_object* v_maxRecDepth_2887_; lean_object* v_ref_2888_; lean_object* v_currNamespace_2889_; lean_object* v_openDecls_2890_; lean_object* v_initHeartbeats_2891_; lean_object* v_maxHeartbeats_2892_; lean_object* v_quotContext_2893_; lean_object* v_currMacroScope_2894_; uint8_t v_diag_2895_; lean_object* v_cancelTk_x3f_2896_; uint8_t v_suppressElabErrors_2897_; lean_object* v_inheritedTraceOptions_2898_; uint8_t v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___f_2902_; lean_object* v_ref_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_fileName_2883_ = lean_ctor_get(v_a_2880_, 0);
v_fileMap_2884_ = lean_ctor_get(v_a_2880_, 1);
v_options_2885_ = lean_ctor_get(v_a_2880_, 2);
v_currRecDepth_2886_ = lean_ctor_get(v_a_2880_, 3);
v_maxRecDepth_2887_ = lean_ctor_get(v_a_2880_, 4);
v_ref_2888_ = lean_ctor_get(v_a_2880_, 5);
v_currNamespace_2889_ = lean_ctor_get(v_a_2880_, 6);
v_openDecls_2890_ = lean_ctor_get(v_a_2880_, 7);
v_initHeartbeats_2891_ = lean_ctor_get(v_a_2880_, 8);
v_maxHeartbeats_2892_ = lean_ctor_get(v_a_2880_, 9);
v_quotContext_2893_ = lean_ctor_get(v_a_2880_, 10);
v_currMacroScope_2894_ = lean_ctor_get(v_a_2880_, 11);
v_diag_2895_ = lean_ctor_get_uint8(v_a_2880_, sizeof(void*)*14);
v_cancelTk_x3f_2896_ = lean_ctor_get(v_a_2880_, 12);
v_suppressElabErrors_2897_ = lean_ctor_get_uint8(v_a_2880_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2898_ = lean_ctor_get(v_a_2880_, 13);
v___x_2899_ = 0;
v___x_2900_ = lean_box(v___x_2899_);
lean_inc(v_id_2873_);
v___x_2901_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(v___x_2901_, 0, v_id_2873_);
lean_closure_set(v___x_2901_, 1, v___x_2900_);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2902_, 0, v___x_2901_);
v_ref_2903_ = l_Lean_replaceRef(v_id_2873_, v_ref_2888_);
lean_dec(v_id_2873_);
lean_inc_ref(v_inheritedTraceOptions_2898_);
lean_inc(v_cancelTk_x3f_2896_);
lean_inc(v_currMacroScope_2894_);
lean_inc(v_quotContext_2893_);
lean_inc(v_maxHeartbeats_2892_);
lean_inc(v_initHeartbeats_2891_);
lean_inc(v_openDecls_2890_);
lean_inc(v_currNamespace_2889_);
lean_inc(v_maxRecDepth_2887_);
lean_inc(v_currRecDepth_2886_);
lean_inc_ref(v_options_2885_);
lean_inc_ref(v_fileMap_2884_);
lean_inc_ref(v_fileName_2883_);
v___x_2904_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2904_, 0, v_fileName_2883_);
lean_ctor_set(v___x_2904_, 1, v_fileMap_2884_);
lean_ctor_set(v___x_2904_, 2, v_options_2885_);
lean_ctor_set(v___x_2904_, 3, v_currRecDepth_2886_);
lean_ctor_set(v___x_2904_, 4, v_maxRecDepth_2887_);
lean_ctor_set(v___x_2904_, 5, v_ref_2903_);
lean_ctor_set(v___x_2904_, 6, v_currNamespace_2889_);
lean_ctor_set(v___x_2904_, 7, v_openDecls_2890_);
lean_ctor_set(v___x_2904_, 8, v_initHeartbeats_2891_);
lean_ctor_set(v___x_2904_, 9, v_maxHeartbeats_2892_);
lean_ctor_set(v___x_2904_, 10, v_quotContext_2893_);
lean_ctor_set(v___x_2904_, 11, v_currMacroScope_2894_);
lean_ctor_set(v___x_2904_, 12, v_cancelTk_x3f_2896_);
lean_ctor_set(v___x_2904_, 13, v_inheritedTraceOptions_2898_);
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*14, v_diag_2895_);
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*14 + 1, v_suppressElabErrors_2897_);
v___x_2905_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2902_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v___x_2904_, v_a_2881_);
lean_dec_ref(v___x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object* v_id_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_Elab_Tactic_getFVarId(v_id_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(size_t v_sz_2917_, size_t v_i_2918_, lean_object* v_bs_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v___x_2929_; 
v___x_2929_ = lean_usize_dec_lt(v_i_2918_, v_sz_2917_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v_bs_2919_);
return v___x_2930_;
}
else
{
lean_object* v_v_2931_; lean_object* v___x_2932_; 
v_v_2931_ = lean_array_uget_borrowed(v_bs_2919_, v_i_2918_);
lean_inc(v_v_2931_);
v___x_2932_ = l_Lean_Elab_Tactic_getFVarId(v_v_2931_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v_bs_x27_2935_; size_t v___x_2936_; size_t v___x_2937_; lean_object* v___x_2938_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2932_);
v___x_2934_ = lean_unsigned_to_nat(0u);
v_bs_x27_2935_ = lean_array_uset(v_bs_2919_, v_i_2918_, v___x_2934_);
v___x_2936_ = ((size_t)1ULL);
v___x_2937_ = lean_usize_add(v_i_2918_, v___x_2936_);
v___x_2938_ = lean_array_uset(v_bs_x27_2935_, v_i_2918_, v_a_2933_);
v_i_2918_ = v___x_2937_;
v_bs_2919_ = v___x_2938_;
goto _start;
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec_ref(v_bs_2919_);
v_a_2940_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2932_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2932_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed(lean_object* v_sz_2948_, lean_object* v_i_2949_, lean_object* v_bs_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
size_t v_sz_boxed_2960_; size_t v_i_boxed_2961_; lean_object* v_res_2962_; 
v_sz_boxed_2960_ = lean_unbox_usize(v_sz_2948_);
lean_dec(v_sz_2948_);
v_i_boxed_2961_ = lean_unbox_usize(v_i_2949_);
lean_dec(v_i_2949_);
v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0(v_sz_boxed_2960_, v_i_boxed_2961_, v_bs_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object* v_ids_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
size_t v_sz_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_sz_2975_ = lean_array_size(v_ids_2965_);
v___x_2976_ = lean_box_usize(v_sz_2975_);
v___x_2977_ = ((lean_object*)(l_Lean_Elab_Tactic_getFVarIds___boxed__const__1));
v___x_2978_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_getFVarIds_spec__0___boxed), 12, 3);
lean_closure_set(v___x_2978_, 0, v___x_2976_);
lean_closure_set(v___x_2978_, 1, v___x_2977_);
lean_closure_set(v___x_2978_, 2, v_ids_2965_);
v___x_2979_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2978_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed(lean_object* v_ids_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_Elab_Tactic_getFVarIds(v_ids_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object* v_e_2991_, uint8_t v___x_2992_, lean_object* v_tac_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v_val_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Elab_Tactic_elabTermForApply(v_e_2991_, v___x_2992_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; lean_object* v_a_3038_; uint8_t v___x_3039_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref(v___x_3035_);
v___x_3037_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_3036_, v___y_2999_);
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref(v___x_3037_);
v___x_3039_ = l_Lean_Expr_isMVar(v_a_3038_);
if (v___x_3039_ == 0)
{
v_val_3004_ = v_a_3038_;
v___y_3005_ = v___y_2995_;
v___y_3006_ = v___y_2996_;
v___y_3007_ = v___y_2997_;
v___y_3008_ = v___y_2998_;
v___y_3009_ = v___y_2999_;
v___y_3010_ = v___y_3000_;
v___y_3011_ = v___y_3001_;
goto v___jp_3003_;
}
else
{
uint8_t v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = 0;
v___x_3041_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_3040_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v___x_3042_; lean_object* v_a_3043_; 
lean_dec_ref(v___x_3041_);
v___x_3042_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabTerm_spec__0___redArg(v_a_3038_, v___y_2999_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v_val_3004_ = v_a_3043_;
v___y_3005_ = v___y_2995_;
v___y_3006_ = v___y_2996_;
v___y_3007_ = v___y_2997_;
v___y_3008_ = v___y_2998_;
v___y_3009_ = v___y_2999_;
v___y_3010_ = v___y_3000_;
v___y_3011_ = v___y_3001_;
goto v___jp_3003_;
}
else
{
lean_dec(v_a_3038_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v_tac_2993_);
return v___x_3041_;
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v_tac_2993_);
v_a_3044_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3035_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3035_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
v___jp_3003_:
{
lean_object* v___x_3012_; 
v___x_3012_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3005_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref(v___x_3012_);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
lean_inc(v___y_3009_);
lean_inc_ref(v___y_3008_);
v___x_3014_ = lean_apply_7(v_tac_2993_, v_a_3013_, v_val_3004_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, lean_box(0));
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = 0;
v___x_3017_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_3016_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v___x_3018_; 
lean_dec_ref(v___x_3017_);
v___x_3018_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3015_, v___y_3005_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
return v___x_3018_;
}
else
{
lean_dec(v_a_3015_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
return v___x_3017_;
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
v_a_3019_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3014_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3014_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec_ref(v_val_3004_);
lean_dec_ref(v_tac_2993_);
v_a_3027_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3012_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3012_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(lean_object* v_e_3052_, lean_object* v___x_3053_, lean_object* v_tac_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
uint8_t v___x_977__boxed_3064_; lean_object* v_res_3065_; 
v___x_977__boxed_3064_ = lean_unbox(v___x_3053_);
v_res_3065_ = l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(v_e_3052_, v___x_977__boxed_3064_, v_tac_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object* v_tac_3066_, lean_object* v_e_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___f_3079_; lean_object* v___x_3080_; 
v___x_3077_ = 1;
v___x_3078_ = lean_box(v___x_3077_);
v___f_3079_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3079_, 0, v_e_3067_);
lean_closure_set(v___f_3079_, 1, v___x_3078_);
lean_closure_set(v___f_3079_, 2, v_tac_3066_);
v___x_3080_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3079_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___boxed(lean_object* v_tac_3081_, lean_object* v_e_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v_tac_3081_, v_e_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0(uint8_t v___x_3093_, lean_object* v_g_3094_, lean_object* v_e_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
uint8_t v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3101_ = 0;
v___x_3102_ = 0;
v___x_3103_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3103_, 0, v___x_3101_);
lean_ctor_set_uint8(v___x_3103_, 1, v___x_3093_);
lean_ctor_set_uint8(v___x_3103_, 2, v___x_3102_);
lean_ctor_set_uint8(v___x_3103_, 3, v___x_3093_);
v___x_3104_ = lean_obj_once(&l_Lean_Elab_Tactic_refineCore___lam__1___closed__5, &l_Lean_Elab_Tactic_refineCore___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
lean_inc_ref(v_e_3095_);
v___x_3105_ = l_Lean_MessageData_ofExpr(v_e_3095_);
v___x_3106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3104_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v___x_3104_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v___x_3109_ = l_Lean_MVarId_apply(v_g_3094_, v_e_3095_, v___x_3103_, v___x_3108_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___boxed(lean_object* v___x_3110_, lean_object* v_g_3111_, lean_object* v_e_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
uint8_t v___x_233__boxed_3118_; lean_object* v_res_3119_; 
v___x_233__boxed_3118_ = lean_unbox(v___x_3110_);
v_res_3119_ = l_Lean_Elab_Tactic_evalApply___lam__0(v___x_233__boxed_3118_, v_g_3111_, v_e_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object* v_stx_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
lean_inc(v_stx_3126_);
v___x_3137_ = l_Lean_Syntax_isOfKind(v_stx_3126_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; 
lean_dec(v_stx_3126_);
v___x_3138_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; lean_object* v___f_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3139_ = lean_box(v___x_3137_);
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3140_, 0, v___x_3139_);
v___x_3141_ = lean_unsigned_to_nat(1u);
v___x_3142_ = l_Lean_Syntax_getArg(v_stx_3126_, v___x_3141_);
lean_dec(v_stx_3126_);
v___x_3143_ = l_Lean_Elab_Tactic_evalApplyLikeTactic(v___f_3140_, v___x_3142_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___boxed(lean_object* v_stx_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_Elab_Tactic_evalApply(v_stx_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1(){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3162_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3163_ = ((lean_object*)(l_Lean_Elab_Tactic_evalApply___closed__1));
v___x_3164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3165_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___boxed), 10, 0);
v___x_3166_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3162_, v___x_3163_, v___x_3164_, v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___boxed(lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1();
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3(){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1));
v___x_3196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6));
v___x_3197_ = l_Lean_addBuiltinDeclarationRanges(v___x_3195_, v___x_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___boxed(lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3();
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3205_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref(v___x_3213_);
v___x_3215_ = 0;
v___x_3216_ = ((lean_object*)(l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0));
v___x_3217_ = l_Lean_MVarId_constructor(v_a_3214_, v___x_3216_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref(v___x_3217_);
v___x_3219_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_3215_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v___x_3220_; 
lean_dec_ref(v___x_3219_);
v___x_3220_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3218_, v___y_3205_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3220_;
}
else
{
lean_dec(v_a_3218_);
return v___x_3219_;
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
v_a_3221_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3217_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3217_);
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
v_a_3229_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3213_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3213_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___boxed(lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg(lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v___f_3257_; lean_object* v___x_3258_; 
v___f_3257_ = ((lean_object*)(l_Lean_Elab_Tactic_evalConstructor___redArg___closed__0));
v___x_3258_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3257_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___boxed(lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Lean_Elab_Tactic_evalConstructor___redArg(v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object* v_x_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_Elab_Tactic_evalConstructor___redArg(v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object* v_x_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_Elab_Tactic_evalConstructor(v_x_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_x_3280_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3304_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1));
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_3307_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___boxed), 10, 0);
v___x_3308_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3304_, v___x_3305_, v___x_3306_, v___x_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___boxed(lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1();
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3(){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3));
v___x_3338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6));
v___x_3339_ = l_Lean_addBuiltinDeclarationRanges(v___x_3337_, v___x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___boxed(lean_object* v_a_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3();
return v_res_3341_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithReducible___closed__0(void){
_start:
{
uint8_t v___x_3342_; uint64_t v___x_3343_; 
v___x_3342_ = 2;
v___x_3343_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object* v_stx_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v___x_3354_; uint8_t v_foApprox_3355_; uint8_t v_ctxApprox_3356_; uint8_t v_quasiPatternApprox_3357_; uint8_t v_constApprox_3358_; uint8_t v_isDefEqStuckEx_3359_; uint8_t v_unificationHints_3360_; uint8_t v_proofIrrelevance_3361_; uint8_t v_assignSyntheticOpaque_3362_; uint8_t v_offsetCnstrs_3363_; uint8_t v_etaStruct_3364_; uint8_t v_univApprox_3365_; uint8_t v_iota_3366_; uint8_t v_beta_3367_; uint8_t v_proj_3368_; uint8_t v_zeta_3369_; uint8_t v_zetaDelta_3370_; uint8_t v_zetaUnused_3371_; uint8_t v_zetaHave_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3409_; 
v___x_3354_ = l_Lean_Meta_Context_config(v_a_3349_);
v_foApprox_3355_ = lean_ctor_get_uint8(v___x_3354_, 0);
v_ctxApprox_3356_ = lean_ctor_get_uint8(v___x_3354_, 1);
v_quasiPatternApprox_3357_ = lean_ctor_get_uint8(v___x_3354_, 2);
v_constApprox_3358_ = lean_ctor_get_uint8(v___x_3354_, 3);
v_isDefEqStuckEx_3359_ = lean_ctor_get_uint8(v___x_3354_, 4);
v_unificationHints_3360_ = lean_ctor_get_uint8(v___x_3354_, 5);
v_proofIrrelevance_3361_ = lean_ctor_get_uint8(v___x_3354_, 6);
v_assignSyntheticOpaque_3362_ = lean_ctor_get_uint8(v___x_3354_, 7);
v_offsetCnstrs_3363_ = lean_ctor_get_uint8(v___x_3354_, 8);
v_etaStruct_3364_ = lean_ctor_get_uint8(v___x_3354_, 10);
v_univApprox_3365_ = lean_ctor_get_uint8(v___x_3354_, 11);
v_iota_3366_ = lean_ctor_get_uint8(v___x_3354_, 12);
v_beta_3367_ = lean_ctor_get_uint8(v___x_3354_, 13);
v_proj_3368_ = lean_ctor_get_uint8(v___x_3354_, 14);
v_zeta_3369_ = lean_ctor_get_uint8(v___x_3354_, 15);
v_zetaDelta_3370_ = lean_ctor_get_uint8(v___x_3354_, 16);
v_zetaUnused_3371_ = lean_ctor_get_uint8(v___x_3354_, 17);
v_zetaHave_3372_ = lean_ctor_get_uint8(v___x_3354_, 18);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3374_ = v___x_3354_;
v_isShared_3375_ = v_isSharedCheck_3409_;
goto v_resetjp_3373_;
}
else
{
lean_dec(v___x_3354_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3409_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
uint8_t v_trackZetaDelta_3376_; lean_object* v_zetaDeltaSet_3377_; lean_object* v_lctx_3378_; lean_object* v_localInstances_3379_; lean_object* v_defEqCtx_x3f_3380_; lean_object* v_synthPendingDepth_3381_; lean_object* v_canUnfold_x3f_3382_; uint8_t v_univApprox_3383_; uint8_t v_inTypeClassResolution_3384_; uint8_t v_cacheInferType_3385_; uint8_t v___x_3386_; lean_object* v_config_3388_; 
v_trackZetaDelta_3376_ = lean_ctor_get_uint8(v_a_3349_, sizeof(void*)*7);
v_zetaDeltaSet_3377_ = lean_ctor_get(v_a_3349_, 1);
v_lctx_3378_ = lean_ctor_get(v_a_3349_, 2);
v_localInstances_3379_ = lean_ctor_get(v_a_3349_, 3);
v_defEqCtx_x3f_3380_ = lean_ctor_get(v_a_3349_, 4);
v_synthPendingDepth_3381_ = lean_ctor_get(v_a_3349_, 5);
v_canUnfold_x3f_3382_ = lean_ctor_get(v_a_3349_, 6);
v_univApprox_3383_ = lean_ctor_get_uint8(v_a_3349_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3384_ = lean_ctor_get_uint8(v_a_3349_, sizeof(void*)*7 + 2);
v_cacheInferType_3385_ = lean_ctor_get_uint8(v_a_3349_, sizeof(void*)*7 + 3);
v___x_3386_ = 2;
if (v_isShared_3375_ == 0)
{
v_config_3388_ = v___x_3374_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 0, v_foApprox_3355_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 1, v_ctxApprox_3356_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 2, v_quasiPatternApprox_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 3, v_constApprox_3358_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 4, v_isDefEqStuckEx_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 5, v_unificationHints_3360_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 6, v_proofIrrelevance_3361_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 7, v_assignSyntheticOpaque_3362_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 8, v_offsetCnstrs_3363_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 10, v_etaStruct_3364_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 11, v_univApprox_3365_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 12, v_iota_3366_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 13, v_beta_3367_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 14, v_proj_3368_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 15, v_zeta_3369_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 16, v_zetaDelta_3370_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 17, v_zetaUnused_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3408_, 18, v_zetaHave_3372_);
v_config_3388_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
uint64_t v___x_3389_; uint64_t v___x_3390_; uint64_t v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; uint64_t v___x_3394_; uint64_t v___x_3395_; uint64_t v_key_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
lean_ctor_set_uint8(v_config_3388_, 9, v___x_3386_);
v___x_3389_ = l_Lean_Meta_Context_configKey(v_a_3349_);
v___x_3390_ = 2ULL;
v___x_3391_ = lean_uint64_shift_right(v___x_3389_, v___x_3390_);
v___x_3392_ = lean_unsigned_to_nat(1u);
v___x_3393_ = l_Lean_Syntax_getArg(v_stx_3344_, v___x_3392_);
v___x_3394_ = lean_uint64_shift_left(v___x_3391_, v___x_3390_);
v___x_3395_ = lean_uint64_once(&l_Lean_Elab_Tactic_evalWithReducible___closed__0, &l_Lean_Elab_Tactic_evalWithReducible___closed__0_once, _init_l_Lean_Elab_Tactic_evalWithReducible___closed__0);
v_key_3396_ = lean_uint64_lor(v___x_3394_, v___x_3395_);
v___x_3397_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3397_, 0, v_config_3388_);
lean_ctor_set_uint64(v___x_3397_, sizeof(void*)*1, v_key_3396_);
lean_inc(v_canUnfold_x3f_3382_);
lean_inc(v_synthPendingDepth_3381_);
lean_inc(v_defEqCtx_x3f_3380_);
lean_inc_ref(v_localInstances_3379_);
lean_inc_ref(v_lctx_3378_);
lean_inc(v_zetaDeltaSet_3377_);
v___x_3398_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v_zetaDeltaSet_3377_);
lean_ctor_set(v___x_3398_, 2, v_lctx_3378_);
lean_ctor_set(v___x_3398_, 3, v_localInstances_3379_);
lean_ctor_set(v___x_3398_, 4, v_defEqCtx_x3f_3380_);
lean_ctor_set(v___x_3398_, 5, v_synthPendingDepth_3381_);
lean_ctor_set(v___x_3398_, 6, v_canUnfold_x3f_3382_);
lean_ctor_set_uint8(v___x_3398_, sizeof(void*)*7, v_trackZetaDelta_3376_);
lean_ctor_set_uint8(v___x_3398_, sizeof(void*)*7 + 1, v_univApprox_3383_);
lean_ctor_set_uint8(v___x_3398_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3384_);
lean_ctor_set_uint8(v___x_3398_, sizeof(void*)*7 + 3, v_cacheInferType_3385_);
v___x_3399_ = l_Lean_Elab_Tactic_evalTactic(v___x_3393_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v___x_3398_, v_a_3350_, v_a_3351_, v_a_3352_);
lean_dec_ref(v___x_3398_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
return v___x_3399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object* v_stx_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Elab_Tactic_evalWithReducible(v_stx_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
lean_dec(v_stx_3410_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3434_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1));
v___x_3436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_3437_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducible___boxed), 10, 0);
v___x_3438_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3434_, v___x_3435_, v___x_3436_, v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___boxed(lean_object* v_a_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1();
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3(){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3));
v___x_3468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6));
v___x_3469_ = l_Lean_addBuiltinDeclarationRanges(v___x_3467_, v___x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___boxed(lean_object* v_a_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3();
return v_res_3471_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0(void){
_start:
{
uint8_t v___x_3472_; uint64_t v___x_3473_; 
v___x_3472_ = 3;
v___x_3473_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object* v_stx_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v___x_3484_; uint8_t v_foApprox_3485_; uint8_t v_ctxApprox_3486_; uint8_t v_quasiPatternApprox_3487_; uint8_t v_constApprox_3488_; uint8_t v_isDefEqStuckEx_3489_; uint8_t v_unificationHints_3490_; uint8_t v_proofIrrelevance_3491_; uint8_t v_assignSyntheticOpaque_3492_; uint8_t v_offsetCnstrs_3493_; uint8_t v_etaStruct_3494_; uint8_t v_univApprox_3495_; uint8_t v_iota_3496_; uint8_t v_beta_3497_; uint8_t v_proj_3498_; uint8_t v_zeta_3499_; uint8_t v_zetaDelta_3500_; uint8_t v_zetaUnused_3501_; uint8_t v_zetaHave_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3539_; 
v___x_3484_ = l_Lean_Meta_Context_config(v_a_3479_);
v_foApprox_3485_ = lean_ctor_get_uint8(v___x_3484_, 0);
v_ctxApprox_3486_ = lean_ctor_get_uint8(v___x_3484_, 1);
v_quasiPatternApprox_3487_ = lean_ctor_get_uint8(v___x_3484_, 2);
v_constApprox_3488_ = lean_ctor_get_uint8(v___x_3484_, 3);
v_isDefEqStuckEx_3489_ = lean_ctor_get_uint8(v___x_3484_, 4);
v_unificationHints_3490_ = lean_ctor_get_uint8(v___x_3484_, 5);
v_proofIrrelevance_3491_ = lean_ctor_get_uint8(v___x_3484_, 6);
v_assignSyntheticOpaque_3492_ = lean_ctor_get_uint8(v___x_3484_, 7);
v_offsetCnstrs_3493_ = lean_ctor_get_uint8(v___x_3484_, 8);
v_etaStruct_3494_ = lean_ctor_get_uint8(v___x_3484_, 10);
v_univApprox_3495_ = lean_ctor_get_uint8(v___x_3484_, 11);
v_iota_3496_ = lean_ctor_get_uint8(v___x_3484_, 12);
v_beta_3497_ = lean_ctor_get_uint8(v___x_3484_, 13);
v_proj_3498_ = lean_ctor_get_uint8(v___x_3484_, 14);
v_zeta_3499_ = lean_ctor_get_uint8(v___x_3484_, 15);
v_zetaDelta_3500_ = lean_ctor_get_uint8(v___x_3484_, 16);
v_zetaUnused_3501_ = lean_ctor_get_uint8(v___x_3484_, 17);
v_zetaHave_3502_ = lean_ctor_get_uint8(v___x_3484_, 18);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3504_ = v___x_3484_;
v_isShared_3505_ = v_isSharedCheck_3539_;
goto v_resetjp_3503_;
}
else
{
lean_dec(v___x_3484_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3539_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
uint8_t v_trackZetaDelta_3506_; lean_object* v_zetaDeltaSet_3507_; lean_object* v_lctx_3508_; lean_object* v_localInstances_3509_; lean_object* v_defEqCtx_x3f_3510_; lean_object* v_synthPendingDepth_3511_; lean_object* v_canUnfold_x3f_3512_; uint8_t v_univApprox_3513_; uint8_t v_inTypeClassResolution_3514_; uint8_t v_cacheInferType_3515_; uint8_t v___x_3516_; lean_object* v_config_3518_; 
v_trackZetaDelta_3506_ = lean_ctor_get_uint8(v_a_3479_, sizeof(void*)*7);
v_zetaDeltaSet_3507_ = lean_ctor_get(v_a_3479_, 1);
v_lctx_3508_ = lean_ctor_get(v_a_3479_, 2);
v_localInstances_3509_ = lean_ctor_get(v_a_3479_, 3);
v_defEqCtx_x3f_3510_ = lean_ctor_get(v_a_3479_, 4);
v_synthPendingDepth_3511_ = lean_ctor_get(v_a_3479_, 5);
v_canUnfold_x3f_3512_ = lean_ctor_get(v_a_3479_, 6);
v_univApprox_3513_ = lean_ctor_get_uint8(v_a_3479_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3514_ = lean_ctor_get_uint8(v_a_3479_, sizeof(void*)*7 + 2);
v_cacheInferType_3515_ = lean_ctor_get_uint8(v_a_3479_, sizeof(void*)*7 + 3);
v___x_3516_ = 3;
if (v_isShared_3505_ == 0)
{
v_config_3518_ = v___x_3504_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 0, v_foApprox_3485_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 1, v_ctxApprox_3486_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 2, v_quasiPatternApprox_3487_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 3, v_constApprox_3488_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 4, v_isDefEqStuckEx_3489_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 5, v_unificationHints_3490_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 6, v_proofIrrelevance_3491_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 7, v_assignSyntheticOpaque_3492_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 8, v_offsetCnstrs_3493_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 10, v_etaStruct_3494_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 11, v_univApprox_3495_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 12, v_iota_3496_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 13, v_beta_3497_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 14, v_proj_3498_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 15, v_zeta_3499_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 16, v_zetaDelta_3500_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 17, v_zetaUnused_3501_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 18, v_zetaHave_3502_);
v_config_3518_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
uint64_t v___x_3519_; uint64_t v___x_3520_; uint64_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint64_t v___x_3524_; uint64_t v___x_3525_; uint64_t v_key_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
lean_ctor_set_uint8(v_config_3518_, 9, v___x_3516_);
v___x_3519_ = l_Lean_Meta_Context_configKey(v_a_3479_);
v___x_3520_ = 2ULL;
v___x_3521_ = lean_uint64_shift_right(v___x_3519_, v___x_3520_);
v___x_3522_ = lean_unsigned_to_nat(1u);
v___x_3523_ = l_Lean_Syntax_getArg(v_stx_3474_, v___x_3522_);
v___x_3524_ = lean_uint64_shift_left(v___x_3521_, v___x_3520_);
v___x_3525_ = lean_uint64_once(&l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0, &l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0_once, _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0);
v_key_3526_ = lean_uint64_lor(v___x_3524_, v___x_3525_);
v___x_3527_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3527_, 0, v_config_3518_);
lean_ctor_set_uint64(v___x_3527_, sizeof(void*)*1, v_key_3526_);
lean_inc(v_canUnfold_x3f_3512_);
lean_inc(v_synthPendingDepth_3511_);
lean_inc(v_defEqCtx_x3f_3510_);
lean_inc_ref(v_localInstances_3509_);
lean_inc_ref(v_lctx_3508_);
lean_inc(v_zetaDeltaSet_3507_);
v___x_3528_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
lean_ctor_set(v___x_3528_, 1, v_zetaDeltaSet_3507_);
lean_ctor_set(v___x_3528_, 2, v_lctx_3508_);
lean_ctor_set(v___x_3528_, 3, v_localInstances_3509_);
lean_ctor_set(v___x_3528_, 4, v_defEqCtx_x3f_3510_);
lean_ctor_set(v___x_3528_, 5, v_synthPendingDepth_3511_);
lean_ctor_set(v___x_3528_, 6, v_canUnfold_x3f_3512_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*7, v_trackZetaDelta_3506_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*7 + 1, v_univApprox_3513_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3514_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*7 + 3, v_cacheInferType_3515_);
v___x_3529_ = l_Lean_Elab_Tactic_evalTactic(v___x_3523_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v___x_3528_, v_a_3480_, v_a_3481_, v_a_3482_);
lean_dec_ref(v___x_3528_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3529_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3529_);
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
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
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
else
{
return v___x_3529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object* v_stx_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_Elab_Tactic_evalWithReducibleAndInstances(v_stx_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_stx_3540_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3564_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1));
v___x_3566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_3567_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed), 10, 0);
v___x_3568_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3564_, v___x_3565_, v___x_3566_, v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___boxed(lean_object* v_a_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1();
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3(){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3));
v___x_3598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6));
v___x_3599_ = l_Lean_addBuiltinDeclarationRanges(v___x_3597_, v___x_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___boxed(lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3();
return v_res_3601_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0(void){
_start:
{
uint8_t v___x_3602_; uint64_t v___x_3603_; 
v___x_3602_ = 0;
v___x_3603_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object* v_stx_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v___x_3614_; uint8_t v_foApprox_3615_; uint8_t v_ctxApprox_3616_; uint8_t v_quasiPatternApprox_3617_; uint8_t v_constApprox_3618_; uint8_t v_isDefEqStuckEx_3619_; uint8_t v_unificationHints_3620_; uint8_t v_proofIrrelevance_3621_; uint8_t v_assignSyntheticOpaque_3622_; uint8_t v_offsetCnstrs_3623_; uint8_t v_etaStruct_3624_; uint8_t v_univApprox_3625_; uint8_t v_iota_3626_; uint8_t v_beta_3627_; uint8_t v_proj_3628_; uint8_t v_zeta_3629_; uint8_t v_zetaDelta_3630_; uint8_t v_zetaUnused_3631_; uint8_t v_zetaHave_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3669_; 
v___x_3614_ = l_Lean_Meta_Context_config(v_a_3609_);
v_foApprox_3615_ = lean_ctor_get_uint8(v___x_3614_, 0);
v_ctxApprox_3616_ = lean_ctor_get_uint8(v___x_3614_, 1);
v_quasiPatternApprox_3617_ = lean_ctor_get_uint8(v___x_3614_, 2);
v_constApprox_3618_ = lean_ctor_get_uint8(v___x_3614_, 3);
v_isDefEqStuckEx_3619_ = lean_ctor_get_uint8(v___x_3614_, 4);
v_unificationHints_3620_ = lean_ctor_get_uint8(v___x_3614_, 5);
v_proofIrrelevance_3621_ = lean_ctor_get_uint8(v___x_3614_, 6);
v_assignSyntheticOpaque_3622_ = lean_ctor_get_uint8(v___x_3614_, 7);
v_offsetCnstrs_3623_ = lean_ctor_get_uint8(v___x_3614_, 8);
v_etaStruct_3624_ = lean_ctor_get_uint8(v___x_3614_, 10);
v_univApprox_3625_ = lean_ctor_get_uint8(v___x_3614_, 11);
v_iota_3626_ = lean_ctor_get_uint8(v___x_3614_, 12);
v_beta_3627_ = lean_ctor_get_uint8(v___x_3614_, 13);
v_proj_3628_ = lean_ctor_get_uint8(v___x_3614_, 14);
v_zeta_3629_ = lean_ctor_get_uint8(v___x_3614_, 15);
v_zetaDelta_3630_ = lean_ctor_get_uint8(v___x_3614_, 16);
v_zetaUnused_3631_ = lean_ctor_get_uint8(v___x_3614_, 17);
v_zetaHave_3632_ = lean_ctor_get_uint8(v___x_3614_, 18);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3634_ = v___x_3614_;
v_isShared_3635_ = v_isSharedCheck_3669_;
goto v_resetjp_3633_;
}
else
{
lean_dec(v___x_3614_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3669_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
uint8_t v_trackZetaDelta_3636_; lean_object* v_zetaDeltaSet_3637_; lean_object* v_lctx_3638_; lean_object* v_localInstances_3639_; lean_object* v_defEqCtx_x3f_3640_; lean_object* v_synthPendingDepth_3641_; lean_object* v_canUnfold_x3f_3642_; uint8_t v_univApprox_3643_; uint8_t v_inTypeClassResolution_3644_; uint8_t v_cacheInferType_3645_; uint8_t v___x_3646_; lean_object* v_config_3648_; 
v_trackZetaDelta_3636_ = lean_ctor_get_uint8(v_a_3609_, sizeof(void*)*7);
v_zetaDeltaSet_3637_ = lean_ctor_get(v_a_3609_, 1);
v_lctx_3638_ = lean_ctor_get(v_a_3609_, 2);
v_localInstances_3639_ = lean_ctor_get(v_a_3609_, 3);
v_defEqCtx_x3f_3640_ = lean_ctor_get(v_a_3609_, 4);
v_synthPendingDepth_3641_ = lean_ctor_get(v_a_3609_, 5);
v_canUnfold_x3f_3642_ = lean_ctor_get(v_a_3609_, 6);
v_univApprox_3643_ = lean_ctor_get_uint8(v_a_3609_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3644_ = lean_ctor_get_uint8(v_a_3609_, sizeof(void*)*7 + 2);
v_cacheInferType_3645_ = lean_ctor_get_uint8(v_a_3609_, sizeof(void*)*7 + 3);
v___x_3646_ = 0;
if (v_isShared_3635_ == 0)
{
v_config_3648_ = v___x_3634_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 0, v_foApprox_3615_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 1, v_ctxApprox_3616_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 2, v_quasiPatternApprox_3617_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 3, v_constApprox_3618_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 4, v_isDefEqStuckEx_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 5, v_unificationHints_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 6, v_proofIrrelevance_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 7, v_assignSyntheticOpaque_3622_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 8, v_offsetCnstrs_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 10, v_etaStruct_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 11, v_univApprox_3625_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 12, v_iota_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 13, v_beta_3627_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 14, v_proj_3628_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 15, v_zeta_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 16, v_zetaDelta_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 17, v_zetaUnused_3631_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, 18, v_zetaHave_3632_);
v_config_3648_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
uint64_t v___x_3649_; uint64_t v___x_3650_; uint64_t v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; uint64_t v___x_3654_; uint64_t v___x_3655_; uint64_t v_key_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_ctor_set_uint8(v_config_3648_, 9, v___x_3646_);
v___x_3649_ = l_Lean_Meta_Context_configKey(v_a_3609_);
v___x_3650_ = 2ULL;
v___x_3651_ = lean_uint64_shift_right(v___x_3649_, v___x_3650_);
v___x_3652_ = lean_unsigned_to_nat(1u);
v___x_3653_ = l_Lean_Syntax_getArg(v_stx_3604_, v___x_3652_);
v___x_3654_ = lean_uint64_shift_left(v___x_3651_, v___x_3650_);
v___x_3655_ = lean_uint64_once(&l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0, &l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0_once, _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0);
v_key_3656_ = lean_uint64_lor(v___x_3654_, v___x_3655_);
v___x_3657_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3657_, 0, v_config_3648_);
lean_ctor_set_uint64(v___x_3657_, sizeof(void*)*1, v_key_3656_);
lean_inc(v_canUnfold_x3f_3642_);
lean_inc(v_synthPendingDepth_3641_);
lean_inc(v_defEqCtx_x3f_3640_);
lean_inc_ref(v_localInstances_3639_);
lean_inc_ref(v_lctx_3638_);
lean_inc(v_zetaDeltaSet_3637_);
v___x_3658_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
lean_ctor_set(v___x_3658_, 1, v_zetaDeltaSet_3637_);
lean_ctor_set(v___x_3658_, 2, v_lctx_3638_);
lean_ctor_set(v___x_3658_, 3, v_localInstances_3639_);
lean_ctor_set(v___x_3658_, 4, v_defEqCtx_x3f_3640_);
lean_ctor_set(v___x_3658_, 5, v_synthPendingDepth_3641_);
lean_ctor_set(v___x_3658_, 6, v_canUnfold_x3f_3642_);
lean_ctor_set_uint8(v___x_3658_, sizeof(void*)*7, v_trackZetaDelta_3636_);
lean_ctor_set_uint8(v___x_3658_, sizeof(void*)*7 + 1, v_univApprox_3643_);
lean_ctor_set_uint8(v___x_3658_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3644_);
lean_ctor_set_uint8(v___x_3658_, sizeof(void*)*7 + 3, v_cacheInferType_3645_);
v___x_3659_ = l_Lean_Elab_Tactic_evalTactic(v___x_3653_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v___x_3658_, v_a_3610_, v_a_3611_, v_a_3612_);
lean_dec_ref(v___x_3658_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
else
{
return v___x_3659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object* v_stx_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Elab_Tactic_evalWithUnfoldingAll(v_stx_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_stx_3670_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3694_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1));
v___x_3696_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_3697_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed), 10, 0);
v___x_3698_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3694_, v___x_3695_, v___x_3696_, v___x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___boxed(lean_object* v_a_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1();
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3(){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3));
v___x_3728_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6));
v___x_3729_ = l_Lean_addBuiltinDeclarationRanges(v___x_3727_, v___x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___boxed(lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3();
return v_res_3731_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0(void){
_start:
{
uint8_t v___x_3732_; uint64_t v___x_3733_; 
v___x_3732_ = 4;
v___x_3733_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone(lean_object* v_stx_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v___x_3744_; uint8_t v_foApprox_3745_; uint8_t v_ctxApprox_3746_; uint8_t v_quasiPatternApprox_3747_; uint8_t v_constApprox_3748_; uint8_t v_isDefEqStuckEx_3749_; uint8_t v_unificationHints_3750_; uint8_t v_proofIrrelevance_3751_; uint8_t v_assignSyntheticOpaque_3752_; uint8_t v_offsetCnstrs_3753_; uint8_t v_etaStruct_3754_; uint8_t v_univApprox_3755_; uint8_t v_iota_3756_; uint8_t v_beta_3757_; uint8_t v_proj_3758_; uint8_t v_zeta_3759_; uint8_t v_zetaDelta_3760_; uint8_t v_zetaUnused_3761_; uint8_t v_zetaHave_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3799_; 
v___x_3744_ = l_Lean_Meta_Context_config(v_a_3739_);
v_foApprox_3745_ = lean_ctor_get_uint8(v___x_3744_, 0);
v_ctxApprox_3746_ = lean_ctor_get_uint8(v___x_3744_, 1);
v_quasiPatternApprox_3747_ = lean_ctor_get_uint8(v___x_3744_, 2);
v_constApprox_3748_ = lean_ctor_get_uint8(v___x_3744_, 3);
v_isDefEqStuckEx_3749_ = lean_ctor_get_uint8(v___x_3744_, 4);
v_unificationHints_3750_ = lean_ctor_get_uint8(v___x_3744_, 5);
v_proofIrrelevance_3751_ = lean_ctor_get_uint8(v___x_3744_, 6);
v_assignSyntheticOpaque_3752_ = lean_ctor_get_uint8(v___x_3744_, 7);
v_offsetCnstrs_3753_ = lean_ctor_get_uint8(v___x_3744_, 8);
v_etaStruct_3754_ = lean_ctor_get_uint8(v___x_3744_, 10);
v_univApprox_3755_ = lean_ctor_get_uint8(v___x_3744_, 11);
v_iota_3756_ = lean_ctor_get_uint8(v___x_3744_, 12);
v_beta_3757_ = lean_ctor_get_uint8(v___x_3744_, 13);
v_proj_3758_ = lean_ctor_get_uint8(v___x_3744_, 14);
v_zeta_3759_ = lean_ctor_get_uint8(v___x_3744_, 15);
v_zetaDelta_3760_ = lean_ctor_get_uint8(v___x_3744_, 16);
v_zetaUnused_3761_ = lean_ctor_get_uint8(v___x_3744_, 17);
v_zetaHave_3762_ = lean_ctor_get_uint8(v___x_3744_, 18);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3764_ = v___x_3744_;
v_isShared_3765_ = v_isSharedCheck_3799_;
goto v_resetjp_3763_;
}
else
{
lean_dec(v___x_3744_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3799_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
uint8_t v_trackZetaDelta_3766_; lean_object* v_zetaDeltaSet_3767_; lean_object* v_lctx_3768_; lean_object* v_localInstances_3769_; lean_object* v_defEqCtx_x3f_3770_; lean_object* v_synthPendingDepth_3771_; lean_object* v_canUnfold_x3f_3772_; uint8_t v_univApprox_3773_; uint8_t v_inTypeClassResolution_3774_; uint8_t v_cacheInferType_3775_; uint8_t v___x_3776_; lean_object* v_config_3778_; 
v_trackZetaDelta_3766_ = lean_ctor_get_uint8(v_a_3739_, sizeof(void*)*7);
v_zetaDeltaSet_3767_ = lean_ctor_get(v_a_3739_, 1);
v_lctx_3768_ = lean_ctor_get(v_a_3739_, 2);
v_localInstances_3769_ = lean_ctor_get(v_a_3739_, 3);
v_defEqCtx_x3f_3770_ = lean_ctor_get(v_a_3739_, 4);
v_synthPendingDepth_3771_ = lean_ctor_get(v_a_3739_, 5);
v_canUnfold_x3f_3772_ = lean_ctor_get(v_a_3739_, 6);
v_univApprox_3773_ = lean_ctor_get_uint8(v_a_3739_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3774_ = lean_ctor_get_uint8(v_a_3739_, sizeof(void*)*7 + 2);
v_cacheInferType_3775_ = lean_ctor_get_uint8(v_a_3739_, sizeof(void*)*7 + 3);
v___x_3776_ = 4;
if (v_isShared_3765_ == 0)
{
v_config_3778_ = v___x_3764_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 0, v_foApprox_3745_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 1, v_ctxApprox_3746_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 2, v_quasiPatternApprox_3747_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 3, v_constApprox_3748_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 4, v_isDefEqStuckEx_3749_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 5, v_unificationHints_3750_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 6, v_proofIrrelevance_3751_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 7, v_assignSyntheticOpaque_3752_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 8, v_offsetCnstrs_3753_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 10, v_etaStruct_3754_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 11, v_univApprox_3755_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 12, v_iota_3756_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 13, v_beta_3757_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 14, v_proj_3758_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 15, v_zeta_3759_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 16, v_zetaDelta_3760_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 17, v_zetaUnused_3761_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, 18, v_zetaHave_3762_);
v_config_3778_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
uint64_t v___x_3779_; uint64_t v___x_3780_; uint64_t v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; uint64_t v___x_3784_; uint64_t v___x_3785_; uint64_t v_key_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
lean_ctor_set_uint8(v_config_3778_, 9, v___x_3776_);
v___x_3779_ = l_Lean_Meta_Context_configKey(v_a_3739_);
v___x_3780_ = 2ULL;
v___x_3781_ = lean_uint64_shift_right(v___x_3779_, v___x_3780_);
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = l_Lean_Syntax_getArg(v_stx_3734_, v___x_3782_);
v___x_3784_ = lean_uint64_shift_left(v___x_3781_, v___x_3780_);
v___x_3785_ = lean_uint64_once(&l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0, &l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0_once, _init_l_Lean_Elab_Tactic_evalWithUnfoldingNone___closed__0);
v_key_3786_ = lean_uint64_lor(v___x_3784_, v___x_3785_);
v___x_3787_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3787_, 0, v_config_3778_);
lean_ctor_set_uint64(v___x_3787_, sizeof(void*)*1, v_key_3786_);
lean_inc(v_canUnfold_x3f_3772_);
lean_inc(v_synthPendingDepth_3771_);
lean_inc(v_defEqCtx_x3f_3770_);
lean_inc_ref(v_localInstances_3769_);
lean_inc_ref(v_lctx_3768_);
lean_inc(v_zetaDeltaSet_3767_);
v___x_3788_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
lean_ctor_set(v___x_3788_, 1, v_zetaDeltaSet_3767_);
lean_ctor_set(v___x_3788_, 2, v_lctx_3768_);
lean_ctor_set(v___x_3788_, 3, v_localInstances_3769_);
lean_ctor_set(v___x_3788_, 4, v_defEqCtx_x3f_3770_);
lean_ctor_set(v___x_3788_, 5, v_synthPendingDepth_3771_);
lean_ctor_set(v___x_3788_, 6, v_canUnfold_x3f_3772_);
lean_ctor_set_uint8(v___x_3788_, sizeof(void*)*7, v_trackZetaDelta_3766_);
lean_ctor_set_uint8(v___x_3788_, sizeof(void*)*7 + 1, v_univApprox_3773_);
lean_ctor_set_uint8(v___x_3788_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3774_);
lean_ctor_set_uint8(v___x_3788_, sizeof(void*)*7 + 3, v_cacheInferType_3775_);
v___x_3789_ = l_Lean_Elab_Tactic_evalTactic(v___x_3783_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v___x_3788_, v_a_3740_, v_a_3741_, v_a_3742_);
lean_dec_ref(v___x_3788_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3789_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3789_);
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
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
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
else
{
return v___x_3789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed(lean_object* v_stx_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_Elab_Tactic_evalWithUnfoldingNone(v_stx_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_);
lean_dec(v_a_3808_);
lean_dec_ref(v_a_3807_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec(v_stx_3800_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1(){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3824_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__1));
v___x_3826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___closed__3));
v___x_3827_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingNone___boxed), 10, 0);
v___x_3828_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3824_, v___x_3825_, v___x_3826_, v___x_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1___boxed(lean_object* v_a_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalWithUnfoldingNone___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingNone__1();
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0(lean_object* v_stx_3834_, lean_object* v___x_3835_, uint8_t v___x_3836_, lean_object* v_userName_x3f_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_Elab_Tactic_elabTerm(v_stx_3834_, v___x_3835_, v___x_3836_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3934_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3850_ = v___x_3847_;
v_isShared_3851_ = v_isSharedCheck_3934_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3847_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3934_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
if (lean_obj_tag(v_a_3848_) == 1)
{
lean_object* v_fvarId_3852_; lean_object* v___x_3854_; 
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v_userName_x3f_3837_);
v_fvarId_3852_ = lean_ctor_get(v_a_3848_, 0);
lean_inc(v_fvarId_3852_);
lean_dec_ref(v_a_3848_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 0, v_fvarId_3852_);
v___x_3854_ = v___x_3850_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_fvarId_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
else
{
lean_object* v___x_3856_; 
lean_del_object(v___x_3850_);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3844_);
lean_inc(v___y_3843_);
lean_inc_ref(v___y_3842_);
lean_inc(v_a_3848_);
v___x_3856_ = lean_infer_type(v_a_3848_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v_userName_3859_; uint8_t v_preserveBinderNames_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___x_3856_);
if (lean_obj_tag(v_userName_x3f_3837_) == 0)
{
lean_object* v___x_3923_; 
v___x_3923_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1));
v_userName_3859_ = v___x_3923_;
v_preserveBinderNames_3860_ = v___x_3836_;
v___y_3861_ = v___y_3839_;
v___y_3862_ = v___y_3842_;
v___y_3863_ = v___y_3843_;
v___y_3864_ = v___y_3844_;
v___y_3865_ = v___y_3845_;
goto v___jp_3858_;
}
else
{
lean_object* v_val_3924_; uint8_t v___x_3925_; 
v_val_3924_ = lean_ctor_get(v_userName_x3f_3837_, 0);
lean_inc(v_val_3924_);
lean_dec_ref(v_userName_x3f_3837_);
v___x_3925_ = 1;
v_userName_3859_ = v_val_3924_;
v_preserveBinderNames_3860_ = v___x_3925_;
v___y_3861_ = v___y_3839_;
v___y_3862_ = v___y_3842_;
v___y_3863_ = v___y_3843_;
v___y_3864_ = v___y_3844_;
v___y_3865_ = v___y_3845_;
goto v___jp_3858_;
}
v___jp_3858_:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3868_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3866_);
v___x_3868_ = l_Lean_MVarId_assert(v_a_3867_, v_userName_3859_, v_a_3857_, v_a_3848_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v___x_3870_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref(v___x_3868_);
v___x_3870_ = l_Lean_Meta_intro1Core(v_a_3869_, v_preserveBinderNames_3860_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v_fst_3872_; lean_object* v_snd_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3898_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3870_);
v_fst_3872_ = lean_ctor_get(v_a_3871_, 0);
v_snd_3873_ = lean_ctor_get(v_a_3871_, 1);
v_isSharedCheck_3898_ = !lean_is_exclusive(v_a_3871_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3875_ = v_a_3871_;
v_isShared_3876_ = v_isSharedCheck_3898_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_snd_3873_);
lean_inc(v_fst_3872_);
lean_dec(v_a_3871_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3898_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3877_ = lean_box(0);
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 1);
lean_ctor_set(v___x_3875_, 1, v___x_3877_);
lean_ctor_set(v___x_3875_, 0, v_snd_3873_);
v___x_3879_ = v___x_3875_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_snd_3873_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3879_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; 
v_unused_3888_ = lean_ctor_get(v___x_3880_, 0);
lean_dec(v_unused_3888_);
v___x_3882_ = v___x_3880_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_dec(v___x_3880_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v_fst_3872_);
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_fst_3872_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec(v_fst_3872_);
v_a_3889_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3880_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3880_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
v_a_3899_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3870_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3870_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
v_a_3907_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3868_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3868_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v_userName_3859_);
lean_dec(v_a_3857_);
lean_dec(v_a_3848_);
v_a_3915_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3866_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3866_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_a_3848_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v_userName_x3f_3837_);
v_a_3926_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3856_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3856_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v_userName_x3f_3837_);
v_a_3935_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3847_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3847_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(lean_object* v_stx_3943_, lean_object* v___x_3944_, lean_object* v___x_3945_, lean_object* v_userName_x3f_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
uint8_t v___x_1473__boxed_3956_; lean_object* v_res_3957_; 
v___x_1473__boxed_3956_ = lean_unbox(v___x_3945_);
v_res_3957_ = l_Lean_Elab_Tactic_elabAsFVar___lam__0(v_stx_3943_, v___x_3944_, v___x_1473__boxed_3956_, v_userName_x3f_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object* v_stx_3958_, lean_object* v_userName_x3f_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v___x_3969_; uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___f_3972_; lean_object* v___x_3973_; 
v___x_3969_ = lean_box(0);
v___x_3970_ = 0;
v___x_3971_ = lean_box(v___x_3970_);
v___f_3972_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed), 13, 4);
lean_closure_set(v___f_3972_, 0, v_stx_3958_);
lean_closure_set(v___f_3972_, 1, v___x_3969_);
lean_closure_set(v___f_3972_, 2, v___x_3971_);
lean_closure_set(v___f_3972_, 3, v_userName_x3f_3959_);
v___x_3973_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3972_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___boxed(lean_object* v_stx_3974_, lean_object* v_userName_x3f_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Lean_Elab_Tactic_elabAsFVar(v_stx_3974_, v_userName_x3f_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(lean_object* v_k_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; 
lean_inc(v___y_3990_);
lean_inc_ref(v___y_3989_);
lean_inc(v___y_3988_);
lean_inc_ref(v___y_3987_);
v___x_3996_ = lean_apply_9(v_k_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, lean_box(0));
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed(lean_object* v_k_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0(v_k_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(lean_object* v_k_4008_, uint8_t v_allowLevelAssignments_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v___f_4019_; lean_object* v___x_4020_; 
lean_inc(v___y_4013_);
lean_inc_ref(v___y_4012_);
lean_inc(v___y_4011_);
lean_inc_ref(v___y_4010_);
v___f_4019_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4019_, 0, v_k_4008_);
lean_closure_set(v___f_4019_, 1, v___y_4010_);
lean_closure_set(v___f_4019_, 2, v___y_4011_);
lean_closure_set(v___f_4019_, 3, v___y_4012_);
lean_closure_set(v___f_4019_, 4, v___y_4013_);
v___x_4020_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_4009_, v___f_4019_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4020_) == 0)
{
return v___x_4020_;
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4020_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4020_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg___boxed(lean_object* v_k_4029_, lean_object* v_allowLevelAssignments_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4040_; lean_object* v_res_4041_; 
v_allowLevelAssignments_boxed_4040_ = lean_unbox(v_allowLevelAssignments_4030_);
v_res_4041_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_4029_, v_allowLevelAssignments_boxed_4040_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(lean_object* v_00_u03b1_4042_, lean_object* v_k_4043_, uint8_t v_allowLevelAssignments_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___redArg(v_k_4043_, v_allowLevelAssignments_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed(lean_object* v_00_u03b1_4055_, lean_object* v_k_4056_, lean_object* v_allowLevelAssignments_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_4067_; lean_object* v_res_4068_; 
v_allowLevelAssignments_boxed_4067_ = lean_unbox(v_allowLevelAssignments_4057_);
v_res_4068_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1(v_00_u03b1_4055_, v_k_4056_, v_allowLevelAssignments_boxed_4067_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(lean_object* v_a_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v_a_x3f_4077_){
_start:
{
uint8_t v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = 0;
v___x_4080_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_4069_, v___x_4079_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0___boxed(lean_object* v_a_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v_a_x3f_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v_a_x3f_4089_);
lean_dec(v_a_x3f_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(lean_object* v_x_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_4094_, v___y_4096_, v___y_4098_, v___y_4100_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v_r_4104_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref(v___x_4102_);
lean_inc(v___y_4100_);
lean_inc_ref(v___y_4099_);
lean_inc(v___y_4098_);
lean_inc_ref(v___y_4097_);
lean_inc(v___y_4096_);
lean_inc_ref(v___y_4095_);
lean_inc(v___y_4094_);
lean_inc_ref(v___y_4093_);
v_r_4104_ = lean_apply_9(v_x_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, lean_box(0));
if (lean_obj_tag(v_r_4104_) == 0)
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4129_; 
v_a_4105_ = lean_ctor_get(v_r_4104_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v_r_4104_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4107_ = v_r_4104_;
v_isShared_4108_ = v_isSharedCheck_4129_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v_r_4104_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4129_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
lean_inc(v_a_4105_);
if (v_isShared_4108_ == 0)
{
lean_ctor_set_tag(v___x_4107_, 1);
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_4103_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___x_4110_);
lean_dec_ref(v___x_4110_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4118_ == 0)
{
lean_object* v_unused_4119_; 
v_unused_4119_ = lean_ctor_get(v___x_4111_, 0);
lean_dec(v_unused_4119_);
v___x_4113_ = v___x_4111_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_dec(v___x_4111_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 0, v_a_4105_);
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4105_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec(v_a_4105_);
v_a_4120_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4111_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4111_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v_a_4130_ = lean_ctor_get(v_r_4104_, 0);
lean_inc(v_a_4130_);
lean_dec_ref(v_r_4104_);
v___x_4131_ = lean_box(0);
v___x_4132_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___lam__0(v_a_4103_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___x_4131_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4139_ == 0)
{
lean_object* v_unused_4140_; 
v_unused_4140_ = lean_ctor_get(v___x_4132_, 0);
lean_dec(v_unused_4140_);
v___x_4134_ = v___x_4132_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_dec(v___x_4132_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 1);
lean_ctor_set(v___x_4134_, 0, v_a_4130_);
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4130_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec(v_a_4130_);
v_a_4141_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4132_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4132_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec_ref(v_x_4092_);
v_a_4149_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4102_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4102_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg___boxed(lean_object* v_x_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(lean_object* v_00_u03b1_4168_, lean_object* v_x_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v_x_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___boxed(lean_object* v_00_u03b1_4180_, lean_object* v_x_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2(v_00_u03b1_4180_, v_x_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(lean_object* v_a_4192_, uint8_t v___x_4193_, lean_object* v_as_4194_, lean_object* v_i_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_zero_4201_; uint8_t v_isZero_4202_; 
v_zero_4201_ = lean_unsigned_to_nat(0u);
v_isZero_4202_ = lean_nat_dec_eq(v_i_4195_, v_zero_4201_);
if (v_isZero_4202_ == 1)
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_dec(v_i_4195_);
lean_dec_ref(v_a_4192_);
v___x_4203_ = lean_box(0);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
else
{
lean_object* v_one_4205_; lean_object* v_n_4206_; lean_object* v___x_4207_; 
v_one_4205_ = lean_unsigned_to_nat(1u);
v_n_4206_ = lean_nat_sub(v_i_4195_, v_one_4205_);
lean_dec(v_i_4195_);
v___x_4207_ = lean_array_fget(v_as_4194_, v_n_4206_);
if (lean_obj_tag(v___x_4207_) == 0)
{
v_i_4195_ = v_n_4206_;
goto _start;
}
else
{
lean_object* v_val_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4240_; 
v_val_4209_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4211_ = v___x_4207_;
v_isShared_4212_ = v_isSharedCheck_4240_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_val_4209_);
lean_dec(v___x_4207_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4240_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = l_Lean_LocalDecl_type(v_val_4209_);
lean_inc_ref(v_a_4192_);
v___x_4214_ = l_Lean_Meta_isExprDefEq(v_a_4192_, v___x_4213_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4231_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4217_ = v___x_4214_;
v_isShared_4218_ = v_isSharedCheck_4231_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4214_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4231_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
uint8_t v___x_4219_; 
v___x_4219_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4209_);
if (v___x_4219_ == 0)
{
if (v___x_4193_ == 0)
{
lean_del_object(v___x_4217_);
lean_dec(v_a_4215_);
lean_del_object(v___x_4211_);
lean_dec(v_val_4209_);
v_i_4195_ = v_n_4206_;
goto _start;
}
else
{
uint8_t v___x_4221_; 
v___x_4221_ = lean_unbox(v_a_4215_);
lean_dec(v_a_4215_);
if (v___x_4221_ == 0)
{
lean_del_object(v___x_4217_);
lean_del_object(v___x_4211_);
lean_dec(v_val_4209_);
v_i_4195_ = v_n_4206_;
goto _start;
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4225_; 
lean_dec(v_n_4206_);
lean_dec_ref(v_a_4192_);
v___x_4223_ = l_Lean_LocalDecl_fvarId(v_val_4209_);
lean_dec(v_val_4209_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v___x_4223_);
v___x_4225_ = v___x_4211_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
lean_object* v___x_4227_; 
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 0, v___x_4225_);
v___x_4227_ = v___x_4217_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4225_);
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
}
else
{
lean_del_object(v___x_4217_);
lean_dec(v_a_4215_);
lean_del_object(v___x_4211_);
lean_dec(v_val_4209_);
v_i_4195_ = v_n_4206_;
goto _start;
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
lean_del_object(v___x_4211_);
lean_dec(v_val_4209_);
lean_dec(v_n_4206_);
lean_dec_ref(v_a_4192_);
v_a_4232_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4214_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4214_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_a_4241_, lean_object* v___x_4242_, lean_object* v_as_4243_, lean_object* v_i_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
uint8_t v___x_7239__boxed_4250_; lean_object* v_res_4251_; 
v___x_7239__boxed_4250_ = lean_unbox(v___x_4242_);
v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_4241_, v___x_7239__boxed_4250_, v_as_4243_, v_i_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec_ref(v_as_4243_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_4252_, uint8_t v___x_4253_, lean_object* v_as_4254_, lean_object* v_i_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_zero_4265_; uint8_t v_isZero_4266_; 
v_zero_4265_ = lean_unsigned_to_nat(0u);
v_isZero_4266_ = lean_nat_dec_eq(v_i_4255_, v_zero_4265_);
if (v_isZero_4266_ == 1)
{
lean_object* v___x_4267_; lean_object* v___x_4268_; 
lean_dec(v_i_4255_);
lean_dec_ref(v_a_4252_);
v___x_4267_ = lean_box(0);
v___x_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
return v___x_4268_;
}
else
{
lean_object* v_one_4269_; lean_object* v_n_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v_one_4269_ = lean_unsigned_to_nat(1u);
v_n_4270_ = lean_nat_sub(v_i_4255_, v_one_4269_);
lean_dec(v_i_4255_);
v___x_4271_ = lean_array_fget_borrowed(v_as_4254_, v_n_4270_);
lean_inc_ref(v_a_4252_);
v___x_4272_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_4252_, v___x_4253_, v___x_4271_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
if (lean_obj_tag(v_a_4273_) == 0)
{
lean_dec_ref(v___x_4272_);
v_i_4255_ = v_n_4270_;
goto _start;
}
else
{
lean_dec_ref(v_a_4273_);
lean_dec(v_n_4270_);
lean_dec_ref(v_a_4252_);
return v___x_4272_;
}
}
else
{
lean_dec(v_n_4270_);
lean_dec_ref(v_a_4252_);
return v___x_4272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(lean_object* v_a_4275_, uint8_t v___x_4276_, lean_object* v_x_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
if (lean_obj_tag(v_x_4277_) == 0)
{
lean_object* v_cs_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v_cs_4287_ = lean_ctor_get(v_x_4277_, 0);
v___x_4288_ = lean_array_get_size(v_cs_4287_);
v___x_4289_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_4275_, v___x_4276_, v_cs_4287_, v___x_4288_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
return v___x_4289_;
}
else
{
lean_object* v_vs_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v_vs_4290_ = lean_ctor_get(v_x_4277_, 0);
v___x_4291_ = lean_array_get_size(v_vs_4290_);
v___x_4292_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_4275_, v___x_4276_, v_vs_4290_, v___x_4291_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
return v___x_4292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4___boxed(lean_object* v_a_4293_, lean_object* v___x_4294_, lean_object* v_x_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
uint8_t v___x_7334__boxed_4305_; lean_object* v_res_4306_; 
v___x_7334__boxed_4305_ = lean_unbox(v___x_4294_);
v_res_4306_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_4293_, v___x_7334__boxed_4305_, v_x_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec_ref(v_x_4295_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_4307_, lean_object* v___x_4308_, lean_object* v_as_4309_, lean_object* v_i_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
uint8_t v___x_7352__boxed_4320_; lean_object* v_res_4321_; 
v___x_7352__boxed_4320_ = lean_unbox(v___x_4308_);
v_res_4321_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_4307_, v___x_7352__boxed_4320_, v_as_4309_, v_i_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec_ref(v_as_4309_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object* v_a_4322_, uint8_t v___x_4323_, lean_object* v_t_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v_root_4334_; lean_object* v_tail_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v_root_4334_ = lean_ctor_get(v_t_4324_, 0);
v_tail_4335_ = lean_ctor_get(v_t_4324_, 1);
v___x_4336_ = lean_array_get_size(v_tail_4335_);
lean_inc_ref(v_a_4322_);
v___x_4337_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_4322_, v___x_4323_, v_tail_4335_, v___x_4336_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
lean_inc(v_a_4338_);
if (lean_obj_tag(v_a_4338_) == 0)
{
lean_object* v___x_4339_; 
lean_dec_ref(v___x_4337_);
v___x_4339_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4(v_a_4322_, v___x_4323_, v_root_4334_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
return v___x_4339_;
}
else
{
lean_dec_ref(v_a_4338_);
lean_dec_ref(v_a_4322_);
return v___x_4337_;
}
}
else
{
lean_dec_ref(v_a_4322_);
return v___x_4337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object* v_a_4340_, lean_object* v___x_4341_, lean_object* v_t_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
uint8_t v___x_7431__boxed_4352_; lean_object* v_res_4353_; 
v___x_7431__boxed_4352_ = lean_unbox(v___x_4341_);
v_res_4353_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_4340_, v___x_7431__boxed_4352_, v_t_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec_ref(v_t_4342_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(lean_object* v_a_4354_, uint8_t v___x_4355_, lean_object* v_lctx_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_decls_4366_; lean_object* v___x_4367_; 
v_decls_4366_ = lean_ctor_get(v_lctx_4356_, 1);
v___x_4367_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0(v_a_4354_, v___x_4355_, v_decls_4366_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object* v_a_4368_, lean_object* v___x_4369_, lean_object* v_lctx_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
uint8_t v___x_7474__boxed_4380_; lean_object* v_res_4381_; 
v___x_7474__boxed_4380_ = lean_unbox(v___x_4369_);
v_res_4381_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_4368_, v___x_7474__boxed_4380_, v_lctx_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec_ref(v_lctx_4370_);
return v_res_4381_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___lam__0___closed__0));
v___x_4384_ = l_Lean_stringToMessageData(v___x_4383_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object* v___x_4385_, lean_object* v___x_4386_, uint8_t v___x_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_Elab_Tactic_elabTerm(v___x_4385_, v___x_4386_, v___x_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v_lctx_4399_; lean_object* v___x_4400_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc_n(v_a_4398_, 2);
lean_dec_ref(v___x_4397_);
v_lctx_4399_ = lean_ctor_get(v___y_4392_, 2);
v___x_4400_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0(v_a_4398_, v___x_4387_, v_lctx_4399_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4413_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4403_ = v___x_4400_;
v_isShared_4404_ = v_isSharedCheck_4413_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4400_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4413_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
if (lean_obj_tag(v_a_4401_) == 0)
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
lean_del_object(v___x_4403_);
v___x_4405_ = lean_obj_once(&l_Lean_Elab_Tactic_evalRename___lam__0___closed__1, &l_Lean_Elab_Tactic_evalRename___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1);
v___x_4406_ = l_Lean_indentExpr(v_a_4398_);
v___x_4407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4405_);
lean_ctor_set(v___x_4407_, 1, v___x_4406_);
v___x_4408_ = l_Lean_throwError___at___00Lean_Elab_Tactic_refineCore_spec__1___redArg(v___x_4407_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
return v___x_4408_;
}
else
{
lean_object* v_val_4409_; lean_object* v___x_4411_; 
lean_dec(v_a_4398_);
v_val_4409_ = lean_ctor_get(v_a_4401_, 0);
lean_inc(v_val_4409_);
lean_dec_ref(v_a_4401_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v_val_4409_);
v___x_4411_ = v___x_4403_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_val_4409_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
lean_dec(v_a_4398_);
v_a_4414_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___x_4400_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4400_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
v_a_4422_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4397_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4397_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object* v___x_4430_, lean_object* v___x_4431_, lean_object* v___x_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
uint8_t v___x_7516__boxed_4442_; lean_object* v_res_4443_; 
v___x_7516__boxed_4442_ = lean_unbox(v___x_4432_);
v_res_4443_ = l_Lean_Elab_Tactic_evalRename___lam__0(v___x_4430_, v___x_4431_, v___x_7516__boxed_4442_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1(lean_object* v___x_4444_, lean_object* v_h_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_evalRename_spec__2___redArg(v___x_4444_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4457_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref(v___x_4455_);
v___x_4457_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_4447_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_a_4458_);
lean_dec_ref(v___x_4457_);
v___x_4459_ = l_Lean_TSyntax_getId(v_h_4445_);
v___x_4460_ = l_Lean_MVarId_rename(v_a_4458_, v_a_4456_, v___x_4459_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref(v___x_4460_);
v___x_4462_ = lean_box(0);
v___x_4463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4463_, 0, v_a_4461_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
v___x_4464_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_4463_, v___y_4447_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
return v___x_4464_;
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
v_a_4465_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4460_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4460_);
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
lean_dec(v_a_4456_);
v_a_4473_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4457_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4457_);
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
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
v_a_4481_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4455_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4455_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1___boxed(lean_object* v___x_4489_, lean_object* v_h_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Lean_Elab_Tactic_evalRename___lam__1(v___x_4489_, v_h_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v_h_4490_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object* v_stx_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4520_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
lean_inc(v_stx_4510_);
v___x_4521_ = l_Lean_Syntax_isOfKind(v_stx_4510_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; 
lean_dec(v_stx_4510_);
v___x_4522_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_4522_;
}
else
{
lean_object* v___x_4523_; lean_object* v_h_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4523_ = lean_unsigned_to_nat(3u);
v_h_4524_ = l_Lean_Syntax_getArg(v_stx_4510_, v___x_4523_);
v___x_4525_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__3));
lean_inc(v_h_4524_);
v___x_4526_ = l_Lean_Syntax_isOfKind(v_h_4524_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
lean_dec(v_h_4524_);
lean_dec(v_stx_4510_);
v___x_4527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExact_spec__0___redArg();
return v___x_4527_;
}
else
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___f_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___f_4537_; lean_object* v___x_4538_; 
v___x_4528_ = lean_unsigned_to_nat(1u);
v___x_4529_ = l_Lean_Syntax_getArg(v_stx_4510_, v___x_4528_);
lean_dec(v_stx_4510_);
v___x_4530_ = lean_box(0);
v___x_4531_ = lean_box(v___x_4526_);
v___f_4532_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__0___boxed), 12, 3);
lean_closure_set(v___f_4532_, 0, v___x_4529_);
lean_closure_set(v___f_4532_, 1, v___x_4530_);
lean_closure_set(v___f_4532_, 2, v___x_4531_);
v___x_4533_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(v___x_4533_, 0, lean_box(0));
lean_closure_set(v___x_4533_, 1, v___f_4532_);
v___x_4534_ = 0;
v___x_4535_ = lean_box(v___x_4534_);
v___x_4536_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_evalRename_spec__1___boxed), 12, 3);
lean_closure_set(v___x_4536_, 0, lean_box(0));
lean_closure_set(v___x_4536_, 1, v___x_4533_);
lean_closure_set(v___x_4536_, 2, v___x_4535_);
v___f_4537_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__1___boxed), 11, 2);
lean_closure_set(v___f_4537_, 0, v___x_4536_);
lean_closure_set(v___f_4537_, 1, v_h_4524_);
v___x_4538_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_4537_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
return v___x_4538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___boxed(lean_object* v_stx_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_Elab_Tactic_evalRename(v_stx_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(lean_object* v_a_4550_, uint8_t v___x_4551_, lean_object* v_as_4552_, lean_object* v_i_4553_, lean_object* v_a_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___redArg(v_a_4550_, v___x_4551_, v_as_4552_, v_i_4553_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3___boxed(lean_object* v_a_4565_, lean_object* v___x_4566_, lean_object* v_as_4567_, lean_object* v_i_4568_, lean_object* v_a_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v___x_7785__boxed_4579_; lean_object* v_res_4580_; 
v___x_7785__boxed_4579_ = lean_unbox(v___x_4566_);
v_res_4580_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__3(v_a_4565_, v___x_7785__boxed_4579_, v_as_4567_, v_i_4568_, v_a_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec_ref(v_as_4567_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(lean_object* v_a_4581_, uint8_t v___x_4582_, lean_object* v_as_4583_, lean_object* v_i_4584_, lean_object* v_a_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___redArg(v_a_4581_, v___x_4582_, v_as_4583_, v_i_4584_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_a_4596_, lean_object* v___x_4597_, lean_object* v_as_4598_, lean_object* v_i_4599_, lean_object* v_a_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
uint8_t v___x_7823__boxed_4610_; lean_object* v_res_4611_; 
v___x_7823__boxed_4610_ = lean_unbox(v___x_4597_);
v_res_4611_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__4_spec__5(v_a_4596_, v___x_7823__boxed_4610_, v_as_4598_, v_i_4599_, v_a_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec_ref(v_as_4598_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1(){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4619_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4620_ = ((lean_object*)(l_Lean_Elab_Tactic_evalRename___closed__1));
v___x_4621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_4622_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___boxed), 10, 0);
v___x_4623_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4619_, v___x_4620_, v___x_4621_, v___x_4622_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___boxed(lean_object* v_a_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1();
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3(){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4652_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1));
v___x_4653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6));
v___x_4654_ = l_Lean_addBuiltinDeclarationRanges(v___x_4652_, v___x_4653_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___boxed(lean_object* v_a_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3();
return v_res_4656_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rename(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Config(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_Tactic_Config(builtin);
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
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin);
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
res = initialize_Lean_Elab_Tactic_Config(builtin);
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
