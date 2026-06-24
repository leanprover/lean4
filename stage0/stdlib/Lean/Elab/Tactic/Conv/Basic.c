// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Basic
// Imports: public import Lean.Meta.Tactic.Replace public import Lean.Elab.Tactic.BuiltinTactic
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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLHSGoalRaw(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_zetaReduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_sortFVarIds___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_convert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Tactic `conv` failed: There are unsolved goals\n"};
static const lean_object* l_Lean_Elab_Tactic_Conv_convert___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_convert___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_convert___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_convert___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "Internal error: Conversion-mode tactic found an invalid `conv` goal"};
static const lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "whnf"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 111, 86, 148, 119, 255, 116, 73)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalWhnf"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(6, 30, 125, 115, 1, 6, 125, 181)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(91) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reduce"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 127, 28, 249, 1, 118, 43, 106)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalReduce"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 147, 193, 102, 100, 242, 130, 81)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__0_value),((lean_object*)(((size_t)(49) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__1_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(93) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__3_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__4_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 143, 59, 185, 170, 152, 3, 30)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalZeta"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(119, 15, 219, 249, 19, 201, 139, 5)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(99) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__1_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalClear___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 78, 175, 7, 2, 107, 214, 173)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalClear___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalClear___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalClear"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 199, 47, 127, 237, 69, 197, 255)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 35, 202, 76, 198, 168, 114, 30)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalConvSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 70, 8, 168, 147, 123, 69)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(110) << 1) | 1)),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__0_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__1_value),((lean_object*)(((size_t)(28) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(109) << 1) | 1)),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__3_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__4_value),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__15_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__18_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "convSeqBracketed"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 46, 60, 206, 104, 220, 125, 67)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalConvSeqBracketed"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(96, 134, 88, 86, 62, 164, 138, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(118) << 1) | 1)),((lean_object*)(((size_t)(64) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__0_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__1_value),((lean_object*)(((size_t)(64) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__3_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__4_value),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "nestedConv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 174, 232, 149, 164, 188, 109, 191)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalNestedConv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 69, 109, 55, 136, 241, 183, 112)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(120) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(121) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__0_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__1_value),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(120) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(120) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__3_value),((lean_object*)(((size_t)(57) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "convSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 81, 30, 13, 252, 23, 29, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalConvSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 255, 126, 12, 172, 125, 122, 148)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(124) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__0_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__1_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__3_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__4_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "convConvSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 85, 97, 250, 95, 212, 248, 253)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalConvConvSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 199, 138, 122, 156, 99, 134, 63)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(129) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__0_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__1_value),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__3_value),((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__4_value),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(4, 172, 52, 155, 88, 222, 189, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalParen"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 44, 38, 199, 32, 20, 2, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(132) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__1_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__4_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nestedTacticCore"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 23, 62, 30, 134, 160, 158, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "evalNestedTacticCore"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 57, 78, 97, 88, 231, 178, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(149) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__0_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__1_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__3_value),((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__4_value),((lean_object*)(((size_t)(83) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 28, 213, 2, 207, 8, 223, 137)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalNestedTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(119, 223, 79, 147, 100, 241, 140, 72)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(55) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(157) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(55) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(151) << 1) | 1)),((lean_object*)(((size_t)(75) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(59) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(75) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "convTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 239, 251, 250, 179, 30, 250, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalConvTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 197, 60, 184, 130, 138, 183, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(159) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(160) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__0_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__1_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(159) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(159) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__3_value),((lean_object*)(((size_t)(57) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 39, 103, 162, 58, 5, 181, 114)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pattern"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__4_value),LEAN_SCALAR_PTR_LITERAL(59, 139, 144, 223, 221, 17, 152, 53)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__5_value;
static const lean_array_object l_Lean_Elab_Tactic_Conv_evalConv___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalConv___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalConv___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalConv___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalConv___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalConv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 46, 136, 31, 44, 193, 131, 251)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(185) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(174) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalFirst___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 113, 181, 219, 229, 158, 34, 244)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalFirst"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 17, 248, 44, 249, 130, 220, 46)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(187) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(188) << 1) | 1)),((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__0_value),((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__1_value),((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(187) << 1) | 1)),((lean_object*)(((size_t)(60) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(187) << 1) | 1)),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__3_value),((lean_object*)(((size_t)(60) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__4_value),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal(lean_object* v_e_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_10_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_mkLHSGoal___closed__1));
v___x_11_ = lean_unsigned_to_nat(3u);
v___x_12_ = l_Lean_Expr_isAppOfArity(v_e_4_, v___x_10_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
v___x_13_ = lean_whnf(v_e_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_22_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_22_ == 0)
{
v___x_16_ = v___x_13_;
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_18_ = l_Lean_mkLHSGoalRaw(v_a_14_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_18_);
v___x_20_ = v___x_16_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
else
{
return v___x_13_;
}
}
else
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = l_Lean_mkLHSGoalRaw(v_e_4_);
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkLHSGoal___boxed(lean_object* v_e_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(v_e_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object* v_lhs_32_, lean_object* v_tag_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_39_; 
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc_ref(v_lhs_32_);
v___x_39_ = lean_infer_type(v_lhs_32_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_40_);
lean_dec_ref_known(v___x_39_, 1);
v___x_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_41_, 0, v_a_40_);
v___x_42_ = 0;
v___x_43_ = lean_box(0);
v___x_44_ = l_Lean_Meta_mkFreshExprMVar(v___x_41_, v___x_42_, v___x_43_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_n(v_a_45_, 2);
lean_dec_ref_known(v___x_44_, 1);
v___x_46_ = l_Lean_Meta_mkEq(v_lhs_32_, v_a_45_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_46_, 1);
v___x_48_ = l_Lean_mkLHSGoalRaw(v_a_47_);
v___x_49_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_48_, v_tag_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_58_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_58_ == 0)
{
v___x_52_ = v___x_49_;
v_isShared_53_ = v_isSharedCheck_58_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_49_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_58_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_56_; 
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v_a_45_);
lean_ctor_set(v___x_54_, 1, v_a_50_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_54_);
v___x_56_ = v___x_52_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_54_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
else
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
lean_dec(v_a_45_);
v_a_59_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_49_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_49_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v_a_45_);
lean_dec(v_tag_33_);
v_a_67_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_46_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_46_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec(v_tag_33_);
lean_dec_ref(v_lhs_32_);
v_a_75_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_44_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_44_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
lean_dec(v_tag_33_);
lean_dec_ref(v_lhs_32_);
v_a_83_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_39_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_39_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor___boxed(lean_object* v_lhs_91_, lean_object* v_tag_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_lhs_91_, v_tag_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal(lean_object* v_mvarId_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; 
lean_inc(v_mvarId_99_);
v___x_105_ = l_Lean_MVarId_getType(v_mvarId_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_135_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_135_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_135_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_135_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_isLHSGoal_x3f(v_a_106_);
lean_dec(v_a_106_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v___x_111_; 
lean_del_object(v___x_108_);
lean_inc(v_mvarId_99_);
v___x_111_ = l_Lean_MVarId_getType(v_mvarId_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v___x_111_, 1);
v___x_113_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(v_a_112_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_113_, 1);
v___x_115_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_99_, v_a_114_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
return v___x_115_;
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec(v_mvarId_99_);
v_a_116_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_113_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_mvarId_99_);
v_a_124_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_111_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_111_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v___x_133_; 
lean_dec_ref_known(v___x_110_, 1);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v_mvarId_99_);
v___x_133_ = v___x_108_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_mvarId_99_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec(v_mvarId_99_);
v_a_136_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_105_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_105_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal___boxed(lean_object* v_mvarId_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_mvarId_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(lean_object* v_e_151_, lean_object* v___y_152_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = l_Lean_Expr_hasMVar(v_e_151_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v_e_151_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v_mctx_157_; lean_object* v___x_158_; lean_object* v_fst_159_; lean_object* v_snd_160_; lean_object* v___x_161_; lean_object* v_cache_162_; lean_object* v_zetaDeltaFVarIds_163_; lean_object* v_postponed_164_; lean_object* v_diag_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_174_; 
v___x_156_ = lean_st_ref_get(v___y_152_);
v_mctx_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc_ref(v_mctx_157_);
lean_dec(v___x_156_);
v___x_158_ = l_Lean_instantiateMVarsCore(v_mctx_157_, v_e_151_);
v_fst_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_fst_159_);
v_snd_160_ = lean_ctor_get(v___x_158_, 1);
lean_inc(v_snd_160_);
lean_dec_ref(v___x_158_);
v___x_161_ = lean_st_ref_take(v___y_152_);
v_cache_162_ = lean_ctor_get(v___x_161_, 1);
v_zetaDeltaFVarIds_163_ = lean_ctor_get(v___x_161_, 2);
v_postponed_164_ = lean_ctor_get(v___x_161_, 3);
v_diag_165_ = lean_ctor_get(v___x_161_, 4);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v___x_161_, 0);
lean_dec(v_unused_175_);
v___x_167_ = v___x_161_;
v_isShared_168_ = v_isSharedCheck_174_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_diag_165_);
lean_inc(v_postponed_164_);
lean_inc(v_zetaDeltaFVarIds_163_);
lean_inc(v_cache_162_);
lean_dec(v___x_161_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_174_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v_snd_160_);
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_snd_160_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_cache_162_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_zetaDeltaFVarIds_163_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_postponed_164_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v_diag_165_);
v___x_170_ = v_reuseFailAlloc_173_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_st_ref_set(v___y_152_, v___x_170_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v_fst_159_);
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg___boxed(lean_object* v_e_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_e_176_, v___y_177_);
lean_dec(v___y_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0(lean_object* v_e_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_e_180_, v___y_186_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___boxed(lean_object* v_e_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0(v_e_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lam__0(lean_object* v_____r_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_box(0);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___lam__0___boxed(lean_object* v_____r_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Elab_Tactic_Conv_convert___lam__0(v_____r_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(lean_object* v_as_x27_225_, lean_object* v_b_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
if (lean_obj_tag(v_as_x27_225_) == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v_b_226_);
return v___x_232_;
}
else
{
lean_object* v_head_233_; lean_object* v_tail_234_; lean_object* v___x_235_; 
v_head_233_ = lean_ctor_get(v_as_x27_225_, 0);
v_tail_234_ = lean_ctor_get(v_as_x27_225_, 1);
v___x_235_ = l_Lean_Meta_saveState___redArg(v___y_228_, v___y_230_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; lean_object* v___y_239_; lean_object* v___y_242_; lean_object* v___y_243_; uint8_t v___y_244_; uint8_t v___x_247_; lean_object* v___x_248_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = lean_box(0);
v___x_247_ = 1;
lean_inc(v_head_233_);
v___x_248_ = l_Lean_MVarId_refl(v_head_233_, v___x_247_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_dec(v_a_236_);
v___y_239_ = v___x_248_;
goto v___jp_238_;
}
else
{
lean_object* v_a_249_; uint8_t v___y_251_; uint8_t v___x_267_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
v___x_267_ = l_Lean_Exception_isInterrupt(v_a_249_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
v___x_268_ = l_Lean_Exception_isRuntime(v_a_249_);
v___y_251_ = v___x_268_;
goto v___jp_250_;
}
else
{
lean_dec(v_a_249_);
v___y_251_ = v___x_267_;
goto v___jp_250_;
}
v___jp_250_:
{
if (v___y_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref_known(v___x_248_, 1);
v___x_252_ = l_Lean_Meta_SavedState_restore___redArg(v_a_236_, v___y_228_, v___y_230_);
lean_dec(v_a_236_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; 
lean_dec_ref_known(v___x_252_, 1);
v___x_253_ = l_Lean_Meta_saveState___redArg(v___y_228_, v___y_230_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_255_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
lean_inc(v_head_233_);
v___x_255_ = l_Lean_MVarId_inferInstance(v_head_233_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_dec(v_a_254_);
v___y_239_ = v___x_255_;
goto v___jp_238_;
}
else
{
lean_object* v_a_256_; uint8_t v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
v___x_257_ = l_Lean_Exception_isInterrupt(v_a_256_);
if (v___x_257_ == 0)
{
uint8_t v___x_258_; 
v___x_258_ = l_Lean_Exception_isRuntime(v_a_256_);
v___y_242_ = v_a_254_;
v___y_243_ = v___x_255_;
v___y_244_ = v___x_258_;
goto v___jp_241_;
}
else
{
lean_dec(v_a_256_);
v___y_242_ = v_a_254_;
v___y_243_ = v___x_255_;
v___y_244_ = v___x_257_;
goto v___jp_241_;
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
v_a_259_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_253_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_253_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
v___y_239_ = v___x_252_;
goto v___jp_238_;
}
}
else
{
lean_dec(v_a_236_);
v___y_239_ = v___x_248_;
goto v___jp_238_;
}
}
}
v___jp_238_:
{
if (lean_obj_tag(v___y_239_) == 0)
{
lean_dec_ref_known(v___y_239_, 1);
v_as_x27_225_ = v_tail_234_;
v_b_226_ = v___x_237_;
goto _start;
}
else
{
return v___y_239_;
}
}
v___jp_241_:
{
if (v___y_244_ == 0)
{
lean_object* v___x_245_; 
lean_dec_ref(v___y_243_);
v___x_245_ = l_Lean_Meta_SavedState_restore___redArg(v___y_242_, v___y_228_, v___y_230_);
lean_dec_ref(v___y_242_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_dec_ref_known(v___x_245_, 1);
v_as_x27_225_ = v_tail_234_;
v_b_226_ = v___x_237_;
goto _start;
}
else
{
v___y_239_ = v___x_245_;
goto v___jp_238_;
}
}
else
{
lean_dec_ref(v___y_242_);
v___y_239_ = v___y_243_;
goto v___jp_238_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_235_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_235_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg___boxed(lean_object* v_as_x27_277_, lean_object* v_b_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_as_x27_277_, v_b_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v_as_x27_277_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(lean_object* v_msgData_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; lean_object* v_env_292_; lean_object* v___x_293_; lean_object* v_mctx_294_; lean_object* v_lctx_295_; lean_object* v_options_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_291_ = lean_st_ref_get(v___y_289_);
v_env_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc_ref(v_env_292_);
lean_dec(v___x_291_);
v___x_293_ = lean_st_ref_get(v___y_287_);
v_mctx_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_ref(v_mctx_294_);
lean_dec(v___x_293_);
v_lctx_295_ = lean_ctor_get(v___y_286_, 2);
v_options_296_ = lean_ctor_get(v___y_288_, 2);
lean_inc_ref(v_options_296_);
lean_inc_ref(v_lctx_295_);
v___x_297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_297_, 0, v_env_292_);
lean_ctor_set(v___x_297_, 1, v_mctx_294_);
lean_ctor_set(v___x_297_, 2, v_lctx_295_);
lean_ctor_set(v___x_297_, 3, v_options_296_);
v___x_298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_msgData_285_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2___boxed(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msgData_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_ref_313_; lean_object* v___x_314_; lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_323_; 
v_ref_313_ = lean_ctor_get(v___y_310_, 5);
v___x_314_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msg_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_323_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_inc(v_ref_313_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_ref_313_);
lean_ctor_set(v___x_319_, 1, v_a_315_);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 1);
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_321_ = v___x_317_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg___boxed(lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v_msg_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_convert___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_convert___closed__0));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert(lean_object* v_lhs_334_, lean_object* v_conv_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_box(0);
v___x_346_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_lhs_334_, v___x_345_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v_fst_348_; lean_object* v_snd_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_432_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v_fst_348_ = lean_ctor_get(v_a_347_, 0);
v_snd_349_ = lean_ctor_get(v_a_347_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_a_347_);
if (v_isSharedCheck_432_ == 0)
{
v___x_351_ = v_a_347_;
v_isShared_352_ = v_isSharedCheck_432_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_snd_349_);
lean_inc(v_fst_348_);
lean_dec(v_a_347_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_432_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_337_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v_a_356_; lean_object* v___y_375_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
v___x_400_ = l_Lean_Expr_mvarId_x21(v_snd_349_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_402_, v_a_337_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_404_; 
lean_dec_ref_known(v___x_403_, 1);
lean_inc(v_a_343_);
lean_inc_ref(v_a_342_);
lean_inc(v_a_341_);
lean_inc_ref(v_a_340_);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
v___x_404_ = lean_apply_9(v_conv_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, lean_box(0));
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; 
lean_dec_ref_known(v___x_404_, 1);
v___x_405_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_337_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = lean_box(0);
v___x_408_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_a_406_, v___x_407_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec(v_a_406_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_409_; 
lean_dec_ref_known(v___x_408_, 1);
v___x_409_ = l_Lean_Elab_Tactic_pruneSolvedGoals(v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; 
lean_dec_ref_known(v___x_409_, 1);
v___x_410_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_337_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; uint8_t v___x_412_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v___x_412_ = l_List_isEmpty___redArg(v_a_411_);
lean_dec(v_a_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_337_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_convert___closed__1, &l_Lean_Elab_Tactic_Conv_convert___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_convert___closed__1);
v___x_416_ = l_Lean_Elab_goalsToMessageData(v_a_414_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v___x_417_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
v___y_375_ = v___x_418_;
goto v___jp_374_;
}
else
{
lean_object* v_a_419_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_419_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_413_, 1);
v_a_356_ = v_a_419_;
goto v___jp_355_;
}
}
else
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Elab_Tactic_Conv_convert___lam__0(v___x_407_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
v___y_375_ = v___x_420_;
goto v___jp_374_;
}
}
else
{
lean_object* v_a_421_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_421_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_410_, 1);
v_a_356_ = v_a_421_;
goto v___jp_355_;
}
}
else
{
v___y_375_ = v___x_409_;
goto v___jp_374_;
}
}
else
{
v___y_375_ = v___x_408_;
goto v___jp_374_;
}
}
else
{
lean_object* v_a_422_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_422_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_405_, 1);
v_a_356_ = v_a_422_;
goto v___jp_355_;
}
}
else
{
lean_object* v_a_423_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_423_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_404_, 1);
v_a_356_ = v_a_423_;
goto v___jp_355_;
}
}
else
{
lean_dec_ref(v_conv_335_);
v___y_375_ = v___x_403_;
goto v___jp_374_;
}
v___jp_355_:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_354_, v_a_337_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_365_);
v___x_359_ = v___x_357_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_dec(v___x_357_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 1);
lean_ctor_set(v___x_359_, 0, v_a_356_);
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_356_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_a_356_);
v_a_366_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_357_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_357_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
v___jp_374_:
{
if (lean_obj_tag(v___y_375_) == 0)
{
lean_object* v___x_376_; 
lean_dec_ref_known(v___y_375_, 1);
v___x_376_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_354_, v_a_337_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; lean_object* v_a_378_; lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_390_; 
lean_dec_ref_known(v___x_376_, 1);
v___x_377_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_fst_348_, v_a_341_);
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref(v___x_377_);
v___x_379_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_snd_349_, v_a_341_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_390_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v_a_380_);
lean_ctor_set(v___x_351_, 0, v_a_378_);
v___x_385_ = v___x_351_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_378_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_a_380_);
v___x_385_ = v_reuseFailAlloc_389_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_387_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_385_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
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
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_391_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_376_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_376_);
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
}
else
{
lean_object* v_a_399_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_399_ = lean_ctor_get(v___y_375_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___y_375_, 1);
v_a_356_ = v_a_399_;
goto v___jp_355_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_del_object(v___x_351_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
lean_dec_ref(v_conv_335_);
v_a_424_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_353_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_353_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
else
{
lean_dec_ref(v_conv_335_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___boxed(lean_object* v_lhs_433_, lean_object* v_conv_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Elab_Tactic_Conv_convert(v_lhs_433_, v_conv_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(lean_object* v_as_445_, lean_object* v_as_x27_446_, lean_object* v_b_447_, lean_object* v_a_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_as_x27_446_, v_b_447_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___boxed(lean_object* v_as_459_, lean_object* v_as_x27_460_, lean_object* v_b_461_, lean_object* v_a_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(v_as_459_, v_as_x27_460_, v_b_461_, v_a_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v_as_x27_460_);
lean_dec(v_as_459_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(lean_object* v_00_u03b1_473_, lean_object* v_msg_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v_msg_474_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___boxed(lean_object* v_00_u03b1_485_, lean_object* v_msg_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(v_00_u03b1_485_, v_msg_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(lean_object* v_mvarId_497_, lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_497_, v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
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
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_a_513_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_504_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_504_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg___boxed(lean_object* v_mvarId_521_, lean_object* v_x_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_mvarId_521_, v_x_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(lean_object* v_00_u03b1_529_, lean_object* v_mvarId_530_, lean_object* v_x_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_mvarId_530_, v_x_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___boxed(lean_object* v_00_u03b1_538_, lean_object* v_mvarId_539_, lean_object* v_x_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(v_00_u03b1_538_, v_mvarId_539_, v_x_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_ref_553_; lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_ref_553_ = lean_ctor_get(v___y_550_, 5);
v___x_554_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
lean_inc(v_ref_553_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v_ref_553_);
lean_ctor_set(v___x_559_, 1, v_a_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 1);
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg___boxed(lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v_msg_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
return v_res_570_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(lean_object* v_mvarId_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_MVarId_getType(v_mvarId_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = l_Lean_Meta_matchEq_x3f(v_a_581_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_594_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_594_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_594_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_594_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
if (lean_obj_tag(v_a_583_) == 1)
{
lean_object* v_val_587_; lean_object* v_snd_588_; lean_object* v___x_590_; 
v_val_587_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v_a_583_, 1);
v_snd_588_ = lean_ctor_get(v_val_587_, 1);
lean_inc(v_snd_588_);
lean_dec(v_val_587_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v_snd_588_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_snd_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; 
lean_del_object(v___x_585_);
lean_dec(v_a_583_);
v___x_592_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1);
v___x_593_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v___x_592_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_593_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_595_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_582_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_582_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_580_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_580_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed(lean_object* v_mvarId_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(v_mvarId_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore(lean_object* v_mvarId_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___f_624_; lean_object* v___x_625_; 
lean_inc(v_mvarId_618_);
v___f_624_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_624_, 0, v_mvarId_618_);
v___x_625_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_mvarId_618_, v___f_624_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___boxed(lean_object* v_mvarId_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(lean_object* v_00_u03b1_633_, lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v_msg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___boxed(lean_object* v_00_u03b1_641_, lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(v_00_u03b1_641_, v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_a_656_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
return v___x_657_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_a_658_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_655_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_655_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg___boxed(lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs(lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_674_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___boxed(lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Elab_Tactic_Conv_getLhsRhs(v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_708_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_fst_704_; lean_object* v___x_706_; 
v_fst_704_ = lean_ctor_get(v_a_700_, 0);
lean_inc(v_fst_704_);
lean_dec(v_a_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v_fst_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_fst_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_699_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_699_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg___boxed(lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v_a_725_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___boxed(lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Elab_Tactic_Conv_getLhs(v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg(lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_759_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_759_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_snd_755_; lean_object* v___x_757_; 
v_snd_755_ = lean_ctor_get(v_a_751_, 1);
lean_inc(v_snd_755_);
lean_dec(v_a_751_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_snd_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_snd_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_760_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_750_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_750_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg___boxed(lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs(lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_776_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___boxed(lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Elab_Tactic_Conv_getRhs(v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v_ks_799_; lean_object* v_vs_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_824_; 
v_ks_799_ = lean_ctor_get(v_x_795_, 0);
v_vs_800_ = lean_ctor_get(v_x_795_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_824_ == 0)
{
v___x_802_ = v_x_795_;
v_isShared_803_ = v_isSharedCheck_824_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_vs_800_);
lean_inc(v_ks_799_);
lean_dec(v_x_795_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_824_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = lean_array_get_size(v_ks_799_);
v___x_805_ = lean_nat_dec_lt(v_x_796_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
lean_dec(v_x_796_);
v___x_806_ = lean_array_push(v_ks_799_, v_x_797_);
v___x_807_ = lean_array_push(v_vs_800_, v_x_798_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_807_);
lean_ctor_set(v___x_802_, 0, v___x_806_);
v___x_809_ = v___x_802_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v_k_x27_811_; uint8_t v___x_812_; 
v_k_x27_811_ = lean_array_fget_borrowed(v_ks_799_, v_x_796_);
v___x_812_ = l_Lean_instBEqMVarId_beq(v_x_797_, v_k_x27_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_814_; 
if (v_isShared_803_ == 0)
{
v___x_814_ = v___x_802_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_ks_799_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_vs_800_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_x_796_, v___x_815_);
lean_dec(v_x_796_);
v_x_795_ = v___x_814_;
v_x_796_ = v___x_816_;
goto _start;
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_819_ = lean_array_fset(v_ks_799_, v_x_796_, v_x_797_);
v___x_820_ = lean_array_fset(v_vs_800_, v_x_796_, v_x_798_);
lean_dec(v_x_796_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_820_);
lean_ctor_set(v___x_802_, 0, v___x_819_);
v___x_822_ = v___x_802_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_820_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_825_, lean_object* v_k_826_, lean_object* v_v_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_825_, v___x_828_, v_k_826_, v_v_827_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(lean_object* v_x_831_, size_t v_x_832_, size_t v_x_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_831_) == 0)
{
lean_object* v_es_836_; size_t v___x_837_; size_t v___x_838_; lean_object* v_j_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_es_836_ = lean_ctor_get(v_x_831_, 0);
v___x_837_ = ((size_t)31ULL);
v___x_838_ = lean_usize_land(v_x_832_, v___x_837_);
v_j_839_ = lean_usize_to_nat(v___x_838_);
v___x_840_ = lean_array_get_size(v_es_836_);
v___x_841_ = lean_nat_dec_lt(v_j_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_dec(v_j_839_);
lean_dec(v_x_835_);
lean_dec(v_x_834_);
return v_x_831_;
}
else
{
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_880_; 
lean_inc_ref(v_es_836_);
v_isSharedCheck_880_ = !lean_is_exclusive(v_x_831_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v_x_831_, 0);
lean_dec(v_unused_881_);
v___x_843_ = v_x_831_;
v_isShared_844_ = v_isSharedCheck_880_;
goto v_resetjp_842_;
}
else
{
lean_dec(v_x_831_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_880_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v_v_845_; lean_object* v___x_846_; lean_object* v_xs_x27_847_; lean_object* v___y_849_; 
v_v_845_ = lean_array_fget(v_es_836_, v_j_839_);
v___x_846_ = lean_box(0);
v_xs_x27_847_ = lean_array_fset(v_es_836_, v_j_839_, v___x_846_);
switch(lean_obj_tag(v_v_845_))
{
case 0:
{
lean_object* v_key_854_; lean_object* v_val_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v_key_854_ = lean_ctor_get(v_v_845_, 0);
v_val_855_ = lean_ctor_get(v_v_845_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_v_845_);
if (v_isSharedCheck_865_ == 0)
{
v___x_857_ = v_v_845_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_val_855_);
lean_inc(v_key_854_);
lean_dec(v_v_845_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
uint8_t v___x_859_; 
v___x_859_ = l_Lean_instBEqMVarId_beq(v_x_834_, v_key_854_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_del_object(v___x_857_);
v___x_860_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_854_, v_val_855_, v_x_834_, v_x_835_);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
v___y_849_ = v___x_861_;
goto v___jp_848_;
}
else
{
lean_object* v___x_863_; 
lean_dec(v_val_855_);
lean_dec(v_key_854_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v_x_835_);
lean_ctor_set(v___x_857_, 0, v_x_834_);
v___x_863_ = v___x_857_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_x_834_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_x_835_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
v___y_849_ = v___x_863_;
goto v___jp_848_;
}
}
}
}
case 1:
{
lean_object* v_node_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_878_; 
v_node_866_ = lean_ctor_get(v_v_845_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_v_845_);
if (v_isSharedCheck_878_ == 0)
{
v___x_868_ = v_v_845_;
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_node_866_);
lean_dec(v_v_845_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_870_ = ((size_t)5ULL);
v___x_871_ = lean_usize_shift_right(v_x_832_, v___x_870_);
v___x_872_ = ((size_t)1ULL);
v___x_873_ = lean_usize_add(v_x_833_, v___x_872_);
v___x_874_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_node_866_, v___x_871_, v___x_873_, v_x_834_, v_x_835_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_874_);
v___x_876_ = v___x_868_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
v___y_849_ = v___x_876_;
goto v___jp_848_;
}
}
}
default: 
{
lean_object* v___x_879_; 
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_x_834_);
lean_ctor_set(v___x_879_, 1, v_x_835_);
v___y_849_ = v___x_879_;
goto v___jp_848_;
}
}
v___jp_848_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_array_fset(v_xs_x27_847_, v_j_839_, v___y_849_);
lean_dec(v_j_839_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_850_);
v___x_852_ = v___x_843_;
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
}
}
else
{
lean_object* v_ks_882_; lean_object* v_vs_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_903_; 
v_ks_882_ = lean_ctor_get(v_x_831_, 0);
v_vs_883_ = lean_ctor_get(v_x_831_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_831_);
if (v_isSharedCheck_903_ == 0)
{
v___x_885_ = v_x_831_;
v_isShared_886_ = v_isSharedCheck_903_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_vs_883_);
lean_inc(v_ks_882_);
lean_dec(v_x_831_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_903_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_ks_882_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_vs_883_);
v___x_888_ = v_reuseFailAlloc_902_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v_newNode_889_; uint8_t v___y_891_; size_t v___x_897_; uint8_t v___x_898_; 
v_newNode_889_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(v___x_888_, v_x_834_, v_x_835_);
v___x_897_ = ((size_t)7ULL);
v___x_898_ = lean_usize_dec_le(v___x_897_, v_x_833_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_899_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_889_);
v___x_900_ = lean_unsigned_to_nat(4u);
v___x_901_ = lean_nat_dec_lt(v___x_899_, v___x_900_);
lean_dec(v___x_899_);
v___y_891_ = v___x_901_;
goto v___jp_890_;
}
else
{
v___y_891_ = v___x_898_;
goto v___jp_890_;
}
v___jp_890_:
{
if (v___y_891_ == 0)
{
lean_object* v_ks_892_; lean_object* v_vs_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_ks_892_ = lean_ctor_get(v_newNode_889_, 0);
lean_inc_ref(v_ks_892_);
v_vs_893_ = lean_ctor_get(v_newNode_889_, 1);
lean_inc_ref(v_vs_893_);
lean_dec_ref(v_newNode_889_);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_x_833_, v_ks_892_, v_vs_893_, v___x_894_, v___x_895_);
lean_dec_ref(v_vs_893_);
lean_dec_ref(v_ks_892_);
return v___x_896_;
}
else
{
return v_newNode_889_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_904_, lean_object* v_keys_905_, lean_object* v_vals_906_, lean_object* v_i_907_, lean_object* v_entries_908_){
_start:
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = lean_array_get_size(v_keys_905_);
v___x_910_ = lean_nat_dec_lt(v_i_907_, v___x_909_);
if (v___x_910_ == 0)
{
lean_dec(v_i_907_);
return v_entries_908_;
}
else
{
lean_object* v_k_911_; lean_object* v_v_912_; uint64_t v___x_913_; size_t v_h_914_; size_t v___x_915_; lean_object* v___x_916_; size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v_h_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_k_911_ = lean_array_fget_borrowed(v_keys_905_, v_i_907_);
v_v_912_ = lean_array_fget_borrowed(v_vals_906_, v_i_907_);
v___x_913_ = l_Lean_instHashableMVarId_hash(v_k_911_);
v_h_914_ = lean_uint64_to_usize(v___x_913_);
v___x_915_ = ((size_t)5ULL);
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_sub(v_depth_904_, v___x_917_);
v___x_919_ = lean_usize_mul(v___x_915_, v___x_918_);
v_h_920_ = lean_usize_shift_right(v_h_914_, v___x_919_);
v___x_921_ = lean_nat_add(v_i_907_, v___x_916_);
lean_dec(v_i_907_);
lean_inc(v_v_912_);
lean_inc(v_k_911_);
v___x_922_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_entries_908_, v_h_920_, v_depth_904_, v_k_911_, v_v_912_);
v_i_907_ = v___x_921_;
v_entries_908_ = v___x_922_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_924_, lean_object* v_keys_925_, lean_object* v_vals_926_, lean_object* v_i_927_, lean_object* v_entries_928_){
_start:
{
size_t v_depth_boxed_929_; lean_object* v_res_930_; 
v_depth_boxed_929_ = lean_unbox_usize(v_depth_924_);
lean_dec(v_depth_924_);
v_res_930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_929_, v_keys_925_, v_vals_926_, v_i_927_, v_entries_928_);
lean_dec_ref(v_vals_926_);
lean_dec_ref(v_keys_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
size_t v_x_1681__boxed_936_; size_t v_x_1682__boxed_937_; lean_object* v_res_938_; 
v_x_1681__boxed_936_ = lean_unbox_usize(v_x_932_);
lean_dec(v_x_932_);
v_x_1682__boxed_937_ = lean_unbox_usize(v_x_933_);
lean_dec(v_x_933_);
v_res_938_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_931_, v_x_1681__boxed_936_, v_x_1682__boxed_937_, v_x_934_, v_x_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
uint64_t v___x_942_; size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; 
v___x_942_ = l_Lean_instHashableMVarId_hash(v_x_940_);
v___x_943_ = lean_uint64_to_usize(v___x_942_);
v___x_944_ = ((size_t)1ULL);
v___x_945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_939_, v___x_943_, v___x_944_, v_x_940_, v_x_941_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(lean_object* v_mvarId_946_, lean_object* v_val_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; lean_object* v_mctx_951_; lean_object* v_cache_952_; lean_object* v_zetaDeltaFVarIds_953_; lean_object* v_postponed_954_; lean_object* v_diag_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_983_; 
v___x_950_ = lean_st_ref_take(v___y_948_);
v_mctx_951_ = lean_ctor_get(v___x_950_, 0);
v_cache_952_ = lean_ctor_get(v___x_950_, 1);
v_zetaDeltaFVarIds_953_ = lean_ctor_get(v___x_950_, 2);
v_postponed_954_ = lean_ctor_get(v___x_950_, 3);
v_diag_955_ = lean_ctor_get(v___x_950_, 4);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_983_ == 0)
{
v___x_957_ = v___x_950_;
v_isShared_958_ = v_isSharedCheck_983_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_diag_955_);
lean_inc(v_postponed_954_);
lean_inc(v_zetaDeltaFVarIds_953_);
lean_inc(v_cache_952_);
lean_inc(v_mctx_951_);
lean_dec(v___x_950_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_983_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_depth_959_; lean_object* v_levelAssignDepth_960_; lean_object* v_lmvarCounter_961_; lean_object* v_mvarCounter_962_; lean_object* v_lDecls_963_; lean_object* v_decls_964_; lean_object* v_userNames_965_; lean_object* v_lAssignment_966_; lean_object* v_eAssignment_967_; lean_object* v_dAssignment_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_982_; 
v_depth_959_ = lean_ctor_get(v_mctx_951_, 0);
v_levelAssignDepth_960_ = lean_ctor_get(v_mctx_951_, 1);
v_lmvarCounter_961_ = lean_ctor_get(v_mctx_951_, 2);
v_mvarCounter_962_ = lean_ctor_get(v_mctx_951_, 3);
v_lDecls_963_ = lean_ctor_get(v_mctx_951_, 4);
v_decls_964_ = lean_ctor_get(v_mctx_951_, 5);
v_userNames_965_ = lean_ctor_get(v_mctx_951_, 6);
v_lAssignment_966_ = lean_ctor_get(v_mctx_951_, 7);
v_eAssignment_967_ = lean_ctor_get(v_mctx_951_, 8);
v_dAssignment_968_ = lean_ctor_get(v_mctx_951_, 9);
v_isSharedCheck_982_ = !lean_is_exclusive(v_mctx_951_);
if (v_isSharedCheck_982_ == 0)
{
v___x_970_ = v_mctx_951_;
v_isShared_971_ = v_isSharedCheck_982_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_dAssignment_968_);
lean_inc(v_eAssignment_967_);
lean_inc(v_lAssignment_966_);
lean_inc(v_userNames_965_);
lean_inc(v_decls_964_);
lean_inc(v_lDecls_963_);
lean_inc(v_mvarCounter_962_);
lean_inc(v_lmvarCounter_961_);
lean_inc(v_levelAssignDepth_960_);
lean_inc(v_depth_959_);
lean_dec(v_mctx_951_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_982_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_eAssignment_967_, v_mvarId_946_, v_val_947_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 8, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_depth_959_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_levelAssignDepth_960_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_lmvarCounter_961_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_mvarCounter_962_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_lDecls_963_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v_decls_964_);
lean_ctor_set(v_reuseFailAlloc_981_, 6, v_userNames_965_);
lean_ctor_set(v_reuseFailAlloc_981_, 7, v_lAssignment_966_);
lean_ctor_set(v_reuseFailAlloc_981_, 8, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_981_, 9, v_dAssignment_968_);
v___x_974_ = v_reuseFailAlloc_981_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_974_);
v___x_976_ = v___x_957_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_cache_952_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_zetaDeltaFVarIds_953_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_postponed_954_);
lean_ctor_set(v_reuseFailAlloc_980_, 4, v_diag_955_);
v___x_976_ = v_reuseFailAlloc_980_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_st_ref_set(v___y_948_, v___x_976_);
v___x_978_ = lean_box(0);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg___boxed(lean_object* v_mvarId_984_, lean_object* v_val_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_mvarId_984_, v_val_985_, v___y_986_);
lean_dec(v___y_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object* v_lhs_x27_989_, lean_object* v_h_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_992_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_992_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = l_Lean_Meta_mkEq(v_lhs_x27_989_, v_a_1003_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
lean_inc(v_a_1001_);
v___x_1006_ = l_Lean_MVarId_getTag(v_a_1001_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = l_Lean_mkLHSGoalRaw(v_a_1005_);
v___x_1009_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1008_, v_a_1007_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc_n(v_a_1010_, 2);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = l_Lean_Meta_mkEqTrans(v_h_990_, v_a_1010_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_a_1001_, v_a_1012_, v_a_996_);
lean_dec_ref(v___x_1013_);
v___x_1014_ = l_Lean_Expr_mvarId_x21(v_a_1010_);
lean_dec(v_a_1010_);
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1016_, v_a_992_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
return v___x_1017_;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_a_1010_);
lean_dec(v_a_1001_);
v_a_1018_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1011_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1011_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_a_1001_);
lean_dec_ref(v_h_990_);
v_a_1026_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1009_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1009_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_a_1005_);
lean_dec(v_a_1001_);
lean_dec_ref(v_h_990_);
v_a_1034_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1006_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1006_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_a_1001_);
lean_dec_ref(v_h_990_);
v_a_1042_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1004_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1004_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1001_);
lean_dec_ref(v_h_990_);
lean_dec_ref(v_lhs_x27_989_);
v_a_1050_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1002_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1002_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v_h_990_);
lean_dec_ref(v_lhs_x27_989_);
v_a_1058_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1000_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1000_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs___boxed(lean_object* v_lhs_x27_1066_, lean_object* v_h_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_lhs_x27_1066_, v_h_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(lean_object* v_mvarId_1078_, lean_object* v_val_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_mvarId_1078_, v_val_1079_, v___y_1085_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___boxed(lean_object* v_mvarId_1090_, lean_object* v_val_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(v_mvarId_1090_, v_val_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0(lean_object* v_00_u03b2_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_x_1103_, v_x_1104_, v_x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, size_t v_x_1109_, size_t v_x_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_1108_, v_x_1109_, v_x_1110_, v_x_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
size_t v_x_2069__boxed_1120_; size_t v_x_2070__boxed_1121_; lean_object* v_res_1122_; 
v_x_2069__boxed_1120_ = lean_unbox_usize(v_x_1116_);
lean_dec(v_x_1116_);
v_x_2070__boxed_1121_ = lean_unbox_usize(v_x_1117_);
lean_dec(v_x_1117_);
v_res_1122_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(v_00_u03b2_1114_, v_x_1115_, v_x_2069__boxed_1120_, v_x_2070__boxed_1121_, v_x_1118_, v_x_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1123_, lean_object* v_n_1124_, lean_object* v_k_1125_, lean_object* v_v_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1124_, v_k_1125_, v_v_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1128_, size_t v_depth_1129_, lean_object* v_keys_1130_, lean_object* v_vals_1131_, lean_object* v_heq_1132_, lean_object* v_i_1133_, lean_object* v_entries_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1129_, v_keys_1130_, v_vals_1131_, v_i_1133_, v_entries_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1136_, lean_object* v_depth_1137_, lean_object* v_keys_1138_, lean_object* v_vals_1139_, lean_object* v_heq_1140_, lean_object* v_i_1141_, lean_object* v_entries_1142_){
_start:
{
size_t v_depth_boxed_1143_; lean_object* v_res_1144_; 
v_depth_boxed_1143_ = lean_unbox_usize(v_depth_1137_);
lean_dec(v_depth_1137_);
v_res_1144_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1136_, v_depth_boxed_1143_, v_keys_1138_, v_vals_1139_, v_heq_1140_, v_i_1141_, v_entries_1142_);
lean_dec_ref(v_vals_1139_);
lean_dec_ref(v_keys_1138_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1146_, v_x_1147_, v_x_1148_, v_x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(lean_object* v_lhs_x27_1151_, lean_object* v_a_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1154_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = l_Lean_Meta_mkEq(v_lhs_x27_1151_, v_a_1152_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1166_ = l_Lean_mkLHSGoalRaw(v_a_1165_);
v___x_1167_ = l_Lean_MVarId_replaceTargetDefEq(v_a_1163_, v___x_1166_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_a_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1170_, v___y_1154_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1171_;
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_a_1172_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1167_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1167_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_a_1163_);
v_a_1180_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1164_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1164_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_lhs_x27_1151_);
v_a_1188_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1162_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1162_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed(lean_object* v_lhs_x27_1196_, lean_object* v_a_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(v_lhs_x27_1196_, v_a_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object* v_lhs_x27_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_1210_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1220_, 0, v_lhs_x27_1208_);
lean_closure_set(v___f_1220_, 1, v_a_1219_);
v___x_1221_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1220_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
return v___x_1221_;
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref(v_lhs_x27_1208_);
v_a_1222_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1218_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1218_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___boxed(lean_object* v_lhs_x27_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_lhs_x27_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1242_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1252_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
v___x_1252_ = lean_whnf(v_a_1251_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1254_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1254_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1253_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v___x_1254_;
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
v_a_1255_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1252_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1252_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
v_a_1263_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1250_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1250_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed(lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___f_1291_; lean_object* v___x_1292_; 
v___f_1291_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0));
v___x_1292_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1291_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___boxed(lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf(lean_object* v_x_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___boxed(lean_object* v_x_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Elab_Tactic_Conv_evalWhnf(v_x_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_x_1314_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1(){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1345_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5));
v___x_1347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8));
v___x_1348_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalWhnf___boxed), 10, 0);
v___x_1349_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1345_, v___x_1346_, v___x_1347_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___boxed(lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3(){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8));
v___x_1379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6));
v___x_1380_ = l_Lean_addBuiltinDeclarationRanges(v___x_1378_, v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___boxed(lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1384_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1394_ = 1;
v___x_1395_ = l_Lean_Meta_reduce(v_a_1393_, v___x_1394_, v___x_1394_, v___x_1394_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1396_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
return v___x_1397_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_a_1398_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1395_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1395_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
v_a_1406_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1392_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1392_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed(lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg(lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___f_1434_; lean_object* v___x_1435_; 
v___f_1434_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0));
v___x_1435_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1434_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___boxed(lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce(lean_object* v_x_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___boxed(lean_object* v_x_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Elab_Tactic_Conv_evalReduce(v_x_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_x_1457_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1(){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1483_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1));
v___x_1485_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3));
v___x_1486_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalReduce___boxed), 10, 0);
v___x_1487_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1483_, v___x_1484_, v___x_1485_, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___boxed(lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3(){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3));
v___x_1517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6));
v___x_1518_ = l_Lean_addBuiltinDeclarationRanges(v___x_1516_, v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___boxed(lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1522_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = 1;
v___x_1533_ = l_Lean_Meta_zetaReduce(v_a_1531_, v___x_1532_, v___x_1532_, v___x_1532_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1534_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1535_;
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_a_1536_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1533_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1533_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
v_a_1544_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1530_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1530_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed(lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg(lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___f_1572_; lean_object* v___x_1573_; 
v___f_1572_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0));
v___x_1573_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1572_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___boxed(lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta(lean_object* v_x_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___boxed(lean_object* v_x_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Elab_Tactic_Conv_evalZeta(v_x_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_x_1595_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1(){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1621_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1));
v___x_1623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3));
v___x_1624_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalZeta___boxed), 10, 0);
v___x_1625_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1621_, v___x_1622_, v___x_1623_, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___boxed(lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3(){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3));
v___x_1655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6));
v___x_1656_ = l_Lean_addBuiltinDeclarationRanges(v___x_1654_, v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___boxed(lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(lean_object* v_e_1659_, lean_object* v___y_1660_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = l_Lean_Expr_hasMVar(v_e_1659_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_e_1659_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; lean_object* v_mctx_1665_; lean_object* v___x_1666_; lean_object* v_fst_1667_; lean_object* v_snd_1668_; lean_object* v___x_1669_; lean_object* v_cache_1670_; lean_object* v_zetaDeltaFVarIds_1671_; lean_object* v_postponed_1672_; lean_object* v_diag_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1682_; 
v___x_1664_ = lean_st_ref_get(v___y_1660_);
v_mctx_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc_ref(v_mctx_1665_);
lean_dec(v___x_1664_);
v___x_1666_ = l_Lean_instantiateMVarsCore(v_mctx_1665_, v_e_1659_);
v_fst_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_fst_1667_);
v_snd_1668_ = lean_ctor_get(v___x_1666_, 1);
lean_inc(v_snd_1668_);
lean_dec_ref(v___x_1666_);
v___x_1669_ = lean_st_ref_take(v___y_1660_);
v_cache_1670_ = lean_ctor_get(v___x_1669_, 1);
v_zetaDeltaFVarIds_1671_ = lean_ctor_get(v___x_1669_, 2);
v_postponed_1672_ = lean_ctor_get(v___x_1669_, 3);
v_diag_1673_ = lean_ctor_get(v___x_1669_, 4);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; 
v_unused_1683_ = lean_ctor_get(v___x_1669_, 0);
lean_dec(v_unused_1683_);
v___x_1675_ = v___x_1669_;
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_diag_1673_);
lean_inc(v_postponed_1672_);
lean_inc(v_zetaDeltaFVarIds_1671_);
lean_inc(v_cache_1670_);
lean_dec(v___x_1669_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v_snd_1668_);
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_snd_1668_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_cache_1670_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_zetaDeltaFVarIds_1671_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_postponed_1672_);
lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_diag_1673_);
v___x_1678_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_st_ref_set(v___y_1660_, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_fst_1667_);
return v___x_1680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg___boxed(lean_object* v_e_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_e_1684_, v___y_1685_);
lean_dec(v___y_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(lean_object* v_e_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_e_1688_, v___y_1690_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___boxed(lean_object* v_e_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(v_e_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear(lean_object* v_mvarId_1702_, lean_object* v_fvarId_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v___x_1709_; 
lean_inc(v_mvarId_1702_);
v___x_1709_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1702_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v_fst_1711_; lean_object* v_snd_1712_; lean_object* v___x_1713_; lean_object* v_a_1714_; uint8_t v___x_1715_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v_fst_1711_ = lean_ctor_get(v_a_1710_, 0);
lean_inc(v_fst_1711_);
v_snd_1712_ = lean_ctor_get(v_a_1710_, 1);
lean_inc(v_snd_1712_);
lean_dec(v_a_1710_);
v___x_1713_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_snd_1712_, v_a_1705_);
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = l_Lean_Expr_isMVar(v_a_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_dec(v_a_1714_);
lean_dec(v_fst_1711_);
v___x_1716_ = l_Lean_MVarId_clear(v_mvarId_1702_, v_fvarId_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = l_Lean_Expr_mvarId_x21(v_a_1714_);
lean_dec(v_a_1714_);
lean_inc(v___x_1717_);
v___x_1718_ = l_Lean_MVarId_getKind(v___x_1717_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
lean_inc(v_fvarId_1703_);
v___x_1720_ = l_Lean_MVarId_clear(v___x_1717_, v_fvarId_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc_n(v_a_1721_, 2);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = lean_unbox(v_a_1719_);
lean_dec(v_a_1719_);
v___x_1723_ = l_Lean_MVarId_setKind___redArg(v_a_1721_, v___x_1722_, v_a_1705_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec_ref_known(v___x_1723_, 1);
v___x_1724_ = l_Lean_mkMVar(v_a_1721_);
v___x_1725_ = l_Lean_Meta_mkEq(v_fst_1711_, v___x_1724_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l_Lean_mkLHSGoalRaw(v_a_1726_);
v___x_1728_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1702_, v___x_1727_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = l_Lean_MVarId_clear(v_a_1729_, v_fvarId_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
return v___x_1730_;
}
else
{
lean_dec(v_fvarId_1703_);
return v___x_1728_;
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_fvarId_1703_);
lean_dec(v_mvarId_1702_);
v_a_1731_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1725_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1725_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_a_1721_);
lean_dec(v_fst_1711_);
lean_dec(v_fvarId_1703_);
lean_dec(v_mvarId_1702_);
v_a_1739_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1723_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1723_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_dec(v_a_1719_);
lean_dec(v_fst_1711_);
lean_dec(v_fvarId_1703_);
lean_dec(v_mvarId_1702_);
return v___x_1720_;
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v___x_1717_);
lean_dec(v_fst_1711_);
lean_dec(v_fvarId_1703_);
lean_dec(v_mvarId_1702_);
v_a_1747_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1718_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1718_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_fvarId_1703_);
lean_dec(v_mvarId_1702_);
v_a_1755_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1709_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1709_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear___boxed(lean_object* v_mvarId_1763_, lean_object* v_fvarId_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Elab_Tactic_Conv_convClear(v_mvarId_1763_, v_fvarId_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
return v_res_1770_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_box(0);
v___x_1772_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___x_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg(){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0);
v___x_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___boxed(lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(lean_object* v_00_u03b1_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___boxed(lean_object* v_00_u03b1_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(v_00_u03b1_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0(lean_object* v_a_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Meta_sortFVarIds___redArg(v_a_1801_, v___y_1806_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed(lean_object* v_a_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Elab_Tactic_Conv_evalClear___lam__0(v_a_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(lean_object* v_a_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1825_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = l_Lean_Elab_Tactic_Conv_convClear(v_a_1834_, v_a_1823_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = lean_box(0);
v___x_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_a_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1838_, v___y_1825_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
return v___x_1839_;
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_a_1840_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1835_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1835_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1823_);
v_a_1848_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1833_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1833_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed(lean_object* v_a_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(v_a_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(lean_object* v_as_1867_, size_t v_sz_1868_, size_t v_i_1869_, lean_object* v_b_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_usize_dec_lt(v_i_1869_, v_sz_1868_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_b_1870_);
return v___x_1881_;
}
else
{
lean_object* v_a_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; 
v_a_1882_ = lean_array_uget_borrowed(v_as_1867_, v_i_1869_);
lean_inc(v_a_1882_);
v___f_1883_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1883_, 0, v_a_1882_);
v___x_1884_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1883_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; size_t v___x_1886_; size_t v___x_1887_; 
lean_dec_ref_known(v___x_1884_, 1);
v___x_1885_ = lean_box(0);
v___x_1886_ = ((size_t)1ULL);
v___x_1887_ = lean_usize_add(v_i_1869_, v___x_1886_);
v_i_1869_ = v___x_1887_;
v_b_1870_ = v___x_1885_;
goto _start;
}
else
{
return v___x_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___boxed(lean_object* v_as_1889_, lean_object* v_sz_1890_, lean_object* v_i_1891_, lean_object* v_b_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
size_t v_sz_boxed_1902_; size_t v_i_boxed_1903_; lean_object* v_res_1904_; 
v_sz_boxed_1902_ = lean_unbox_usize(v_sz_1890_);
lean_dec(v_sz_1890_);
v_i_boxed_1903_ = lean_unbox_usize(v_i_1891_);
lean_dec(v_i_1891_);
v_res_1904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v_as_1889_, v_sz_boxed_1902_, v_i_boxed_1903_, v_b_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec_ref(v_as_1889_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear(lean_object* v_stx_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalClear___closed__1));
lean_inc(v_stx_1912_);
v___x_1923_ = l_Lean_Syntax_isOfKind(v_stx_1912_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; 
lean_dec(v_stx_1912_);
v___x_1924_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_hs_1927_; lean_object* v___x_1928_; 
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = l_Lean_Syntax_getArg(v_stx_1912_, v___x_1925_);
lean_dec(v_stx_1912_);
v_hs_1927_ = l_Lean_Syntax_getArgs(v___x_1926_);
lean_dec(v___x_1926_);
v___x_1928_ = l_Lean_Elab_Tactic_getFVarIds(v_hs_1927_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___f_1930_; lean_object* v___x_1931_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___f_1930_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1930_, 0, v_a_1929_);
v___x_1931_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1930_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; size_t v_sz_1935_; size_t v___x_1936_; lean_object* v___x_1937_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Array_reverse___redArg(v_a_1932_);
v___x_1934_ = lean_box(0);
v_sz_1935_ = lean_array_size(v___x_1933_);
v___x_1936_ = ((size_t)0ULL);
v___x_1937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v___x_1933_, v_sz_1935_, v___x_1936_, v___x_1934_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
lean_dec_ref(v___x_1933_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v___x_1937_, 0);
lean_dec(v_unused_1945_);
v___x_1939_ = v___x_1937_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v___x_1937_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1934_);
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1934_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
return v___x_1937_;
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1931_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1931_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1928_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1928_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___boxed(lean_object* v_stx_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Elab_Tactic_Conv_evalClear(v_stx_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1(){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1981_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1982_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalClear___closed__1));
v___x_1983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1));
v___x_1984_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalClear___boxed), 10, 0);
v___x_1985_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1981_, v___x_1982_, v___x_1983_, v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___boxed(lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(lean_object* v_as_1988_, size_t v_sz_1989_, size_t v_i_1990_, lean_object* v_b_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_a_2002_; uint8_t v___x_2006_; 
v___x_2006_ = lean_usize_dec_lt(v_i_1990_, v_sz_1989_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_b_1991_);
return v___x_2007_;
}
else
{
lean_object* v_next_2008_; 
v_next_2008_ = lean_ctor_get(v_b_1991_, 0);
lean_inc(v_next_2008_);
if (lean_obj_tag(v_next_2008_) == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v_b_1991_);
return v___x_2009_;
}
else
{
lean_object* v_upperBound_2010_; lean_object* v_val_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2054_; 
v_upperBound_2010_ = lean_ctor_get(v_b_1991_, 1);
v_val_2011_ = lean_ctor_get(v_next_2008_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_next_2008_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2013_ = v_next_2008_;
v_isShared_2014_ = v_isSharedCheck_2054_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_val_2011_);
lean_dec(v_next_2008_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2054_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_nat_dec_lt(v_val_2011_, v_upperBound_2010_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_del_object(v___x_2013_);
lean_dec(v_val_2011_);
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_b_1991_);
return v___x_2016_;
}
else
{
lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2051_; 
lean_inc(v_upperBound_2010_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_b_1991_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; lean_object* v_unused_2053_; 
v_unused_2052_ = lean_ctor_get(v_b_1991_, 1);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_b_1991_, 0);
lean_dec(v_unused_2053_);
v___x_2018_ = v_b_1991_;
v_isShared_2019_ = v_isSharedCheck_2051_;
goto v_resetjp_2017_;
}
else
{
lean_dec(v_b_1991_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2051_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v_a_2020_ = lean_array_uget_borrowed(v_as_1988_, v_i_1990_);
v___x_2021_ = lean_unsigned_to_nat(1u);
v___x_2022_ = lean_nat_add(v_val_2011_, v___x_2021_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2022_);
v___x_2024_ = v___x_2013_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2024_);
v___x_2026_ = v___x_2018_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_upperBound_2010_);
v___x_2026_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2027_ = lean_unsigned_to_nat(2u);
v___x_2028_ = lean_nat_mod(v_val_2011_, v___x_2027_);
lean_dec(v_val_2011_);
v___x_2029_ = lean_unsigned_to_nat(0u);
v___x_2030_ = lean_nat_dec_eq(v___x_2028_, v___x_2029_);
lean_dec(v___x_2028_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_inc(v_a_2020_);
v___x_2031_ = l_Lean_Elab_Tactic_saveTacticInfoForToken(v_a_2020_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_dec_ref_known(v___x_2031_, 1);
v_a_2002_ = v___x_2026_;
goto v___jp_2001_;
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v___x_2026_);
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v___x_2040_; 
lean_inc(v_a_2020_);
v___x_2040_ = l_Lean_Elab_Tactic_evalTactic(v_a_2020_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_dec_ref_known(v___x_2040_, 1);
v_a_2002_ = v___x_2026_;
goto v___jp_2001_;
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v___x_2026_);
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
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
}
v___jp_2001_:
{
size_t v___x_2003_; size_t v___x_2004_; 
v___x_2003_ = ((size_t)1ULL);
v___x_2004_ = lean_usize_add(v_i_1990_, v___x_2003_);
v_i_1990_ = v___x_2004_;
v_b_1991_ = v_a_2002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0___boxed(lean_object* v_as_2055_, lean_object* v_sz_2056_, lean_object* v_i_2057_, lean_object* v_b_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
size_t v_sz_boxed_2068_; size_t v_i_boxed_2069_; lean_object* v_res_2070_; 
v_sz_boxed_2068_ = lean_unbox_usize(v_sz_2056_);
lean_dec(v_sz_2056_);
v_i_boxed_2069_ = lean_unbox_usize(v_i_2057_);
lean_dec(v_i_2057_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v_as_2055_, v_sz_boxed_2068_, v_i_boxed_2069_, v_b_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec_ref(v_as_2055_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(lean_object* v_stx_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; size_t v_sz_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
v___x_2083_ = l_Lean_Syntax_getArgs(v_stx_2073_);
v___x_2084_ = lean_array_get_size(v___x_2083_);
v___x_2085_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0));
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___x_2084_);
v_sz_2087_ = lean_array_size(v___x_2083_);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v___x_2083_, v_sz_2087_, v___x_2088_, v___x_2086_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
lean_dec_ref(v___x_2083_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2097_; 
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v___x_2089_, 0);
lean_dec(v_unused_2098_);
v___x_2091_ = v___x_2089_;
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
else
{
lean_dec(v___x_2089_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = lean_box(0);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2089_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2089_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(lean_object* v_stx_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v_stx_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_stx_2107_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(lean_object* v_stx_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = l_Lean_Syntax_getArg(v_stx_2118_, v___x_2128_);
v___x_2130_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v___x_2129_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec(v___x_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(lean_object* v_stx_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(v_stx_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
lean_dec(v_stx_2131_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1(){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2157_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1));
v___x_2159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3));
v___x_2160_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed), 10, 0);
v___x_2161_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2157_, v___x_2158_, v___x_2159_, v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___boxed(lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3(){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3));
v___x_2191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6));
v___x_2192_ = l_Lean_addBuiltinDeclarationRanges(v___x_2190_, v___x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___boxed(lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(lean_object* v_a_2195_, lean_object* v_trees_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
lean_inc(v___y_2200_);
lean_inc_ref(v___y_2199_);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
v___x_2206_ = lean_apply_9(v_a_2195_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, lean_box(0));
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2215_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_a_2207_);
lean_ctor_set(v___x_2211_, 1, v_trees_2196_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v_trees_2196_);
v_a_2216_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2206_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2206_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed(lean_object* v_a_2224_, lean_object* v_trees_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(v_a_2224_, v_trees_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(lean_object* v___x_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2236_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed(lean_object* v___x_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(v___x_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(lean_object* v___y_2258_, lean_object* v_mkInfoTree_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v_a_2267_, lean_object* v_a_x3f_2268_){
_start:
{
lean_object* v___x_2270_; lean_object* v_infoState_2271_; lean_object* v_trees_2272_; lean_object* v___x_2273_; 
v___x_2270_ = lean_st_ref_get(v___y_2258_);
v_infoState_2271_ = lean_ctor_get(v___x_2270_, 7);
lean_inc_ref(v_infoState_2271_);
lean_dec(v___x_2270_);
v_trees_2272_ = lean_ctor_get(v_infoState_2271_, 2);
lean_inc_ref(v_trees_2272_);
lean_dec_ref(v_infoState_2271_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2266_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc(v___y_2263_);
lean_inc_ref(v___y_2262_);
lean_inc(v___y_2261_);
lean_inc_ref(v___y_2260_);
v___x_2273_ = lean_apply_10(v_mkInfoTree_2259_, v_trees_2272_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2258_, lean_box(0));
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2312_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2312_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2312_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v_infoState_2279_; lean_object* v_env_2280_; lean_object* v_nextMacroScope_2281_; lean_object* v_ngen_2282_; lean_object* v_auxDeclNGen_2283_; lean_object* v_traceState_2284_; lean_object* v_cache_2285_; lean_object* v_messages_2286_; lean_object* v_snapshotTasks_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2311_; 
v___x_2278_ = lean_st_ref_take(v___y_2258_);
v_infoState_2279_ = lean_ctor_get(v___x_2278_, 7);
v_env_2280_ = lean_ctor_get(v___x_2278_, 0);
v_nextMacroScope_2281_ = lean_ctor_get(v___x_2278_, 1);
v_ngen_2282_ = lean_ctor_get(v___x_2278_, 2);
v_auxDeclNGen_2283_ = lean_ctor_get(v___x_2278_, 3);
v_traceState_2284_ = lean_ctor_get(v___x_2278_, 4);
v_cache_2285_ = lean_ctor_get(v___x_2278_, 5);
v_messages_2286_ = lean_ctor_get(v___x_2278_, 6);
v_snapshotTasks_2287_ = lean_ctor_get(v___x_2278_, 8);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2289_ = v___x_2278_;
v_isShared_2290_ = v_isSharedCheck_2311_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_snapshotTasks_2287_);
lean_inc(v_infoState_2279_);
lean_inc(v_messages_2286_);
lean_inc(v_cache_2285_);
lean_inc(v_traceState_2284_);
lean_inc(v_auxDeclNGen_2283_);
lean_inc(v_ngen_2282_);
lean_inc(v_nextMacroScope_2281_);
lean_inc(v_env_2280_);
lean_dec(v___x_2278_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2311_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
uint8_t v_enabled_2291_; lean_object* v_assignment_2292_; lean_object* v_lazyAssignment_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2309_; 
v_enabled_2291_ = lean_ctor_get_uint8(v_infoState_2279_, sizeof(void*)*3);
v_assignment_2292_ = lean_ctor_get(v_infoState_2279_, 0);
v_lazyAssignment_2293_ = lean_ctor_get(v_infoState_2279_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_infoState_2279_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v_infoState_2279_, 2);
lean_dec(v_unused_2310_);
v___x_2295_ = v_infoState_2279_;
v_isShared_2296_ = v_isSharedCheck_2309_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_lazyAssignment_2293_);
lean_inc(v_assignment_2292_);
lean_dec(v_infoState_2279_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2309_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = l_Lean_PersistentArray_push___redArg(v_a_2267_, v_a_2274_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 2, v___x_2297_);
v___x_2299_ = v___x_2295_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_assignment_2292_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_lazyAssignment_2293_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v___x_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2308_, sizeof(void*)*3, v_enabled_2291_);
v___x_2299_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2301_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 7, v___x_2299_);
v___x_2301_ = v___x_2289_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_env_2280_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_nextMacroScope_2281_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_ngen_2282_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_auxDeclNGen_2283_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_traceState_2284_);
lean_ctor_set(v_reuseFailAlloc_2307_, 5, v_cache_2285_);
lean_ctor_set(v_reuseFailAlloc_2307_, 6, v_messages_2286_);
lean_ctor_set(v_reuseFailAlloc_2307_, 7, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2307_, 8, v_snapshotTasks_2287_);
v___x_2301_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2302_ = lean_st_ref_set(v___y_2258_, v___x_2301_);
v___x_2303_ = lean_box(0);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2303_);
v___x_2305_ = v___x_2276_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
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
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v_a_2267_);
v_a_2313_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2273_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2273_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0___boxed(lean_object* v___y_2321_, lean_object* v_mkInfoTree_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v_a_2330_, lean_object* v_a_x3f_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2321_, v_mkInfoTree_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v_a_2330_, v_a_x3f_2331_);
lean_dec(v_a_x3f_2331_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2321_);
return v_res_2333_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = lean_unsigned_to_nat(32u);
v___x_2335_ = lean_mk_empty_array_with_capacity(v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2337_ = ((size_t)5ULL);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_unsigned_to_nat(32u);
v___x_2340_ = lean_mk_empty_array_with_capacity(v___x_2339_);
v___x_2341_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__0);
v___x_2342_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v___x_2340_);
lean_ctor_set(v___x_2342_, 2, v___x_2338_);
lean_ctor_set(v___x_2342_, 3, v___x_2338_);
lean_ctor_set_usize(v___x_2342_, 4, v___x_2337_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v_infoState_2346_; lean_object* v_trees_2347_; lean_object* v___x_2348_; lean_object* v_infoState_2349_; lean_object* v_env_2350_; lean_object* v_nextMacroScope_2351_; lean_object* v_ngen_2352_; lean_object* v_auxDeclNGen_2353_; lean_object* v_traceState_2354_; lean_object* v_cache_2355_; lean_object* v_messages_2356_; lean_object* v_snapshotTasks_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2378_; 
v___x_2345_ = lean_st_ref_get(v___y_2343_);
v_infoState_2346_ = lean_ctor_get(v___x_2345_, 7);
lean_inc_ref(v_infoState_2346_);
lean_dec(v___x_2345_);
v_trees_2347_ = lean_ctor_get(v_infoState_2346_, 2);
lean_inc_ref(v_trees_2347_);
lean_dec_ref(v_infoState_2346_);
v___x_2348_ = lean_st_ref_take(v___y_2343_);
v_infoState_2349_ = lean_ctor_get(v___x_2348_, 7);
v_env_2350_ = lean_ctor_get(v___x_2348_, 0);
v_nextMacroScope_2351_ = lean_ctor_get(v___x_2348_, 1);
v_ngen_2352_ = lean_ctor_get(v___x_2348_, 2);
v_auxDeclNGen_2353_ = lean_ctor_get(v___x_2348_, 3);
v_traceState_2354_ = lean_ctor_get(v___x_2348_, 4);
v_cache_2355_ = lean_ctor_get(v___x_2348_, 5);
v_messages_2356_ = lean_ctor_get(v___x_2348_, 6);
v_snapshotTasks_2357_ = lean_ctor_get(v___x_2348_, 8);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2359_ = v___x_2348_;
v_isShared_2360_ = v_isSharedCheck_2378_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_snapshotTasks_2357_);
lean_inc(v_infoState_2349_);
lean_inc(v_messages_2356_);
lean_inc(v_cache_2355_);
lean_inc(v_traceState_2354_);
lean_inc(v_auxDeclNGen_2353_);
lean_inc(v_ngen_2352_);
lean_inc(v_nextMacroScope_2351_);
lean_inc(v_env_2350_);
lean_dec(v___x_2348_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2378_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
uint8_t v_enabled_2361_; lean_object* v_assignment_2362_; lean_object* v_lazyAssignment_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2376_; 
v_enabled_2361_ = lean_ctor_get_uint8(v_infoState_2349_, sizeof(void*)*3);
v_assignment_2362_ = lean_ctor_get(v_infoState_2349_, 0);
v_lazyAssignment_2363_ = lean_ctor_get(v_infoState_2349_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_infoState_2349_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v_infoState_2349_, 2);
lean_dec(v_unused_2377_);
v___x_2365_ = v_infoState_2349_;
v_isShared_2366_ = v_isSharedCheck_2376_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_lazyAssignment_2363_);
lean_inc(v_assignment_2362_);
lean_dec(v_infoState_2349_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2376_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 2, v___x_2367_);
v___x_2369_ = v___x_2365_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_assignment_2362_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_lazyAssignment_2363_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v___x_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*3, v_enabled_2361_);
v___x_2369_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 7, v___x_2369_);
v___x_2371_ = v___x_2359_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_env_2350_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_nextMacroScope_2351_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_ngen_2352_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v_auxDeclNGen_2353_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v_traceState_2354_);
lean_ctor_set(v_reuseFailAlloc_2374_, 5, v_cache_2355_);
lean_ctor_set(v_reuseFailAlloc_2374_, 6, v_messages_2356_);
lean_ctor_set(v_reuseFailAlloc_2374_, 7, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2374_, 8, v_snapshotTasks_2357_);
v___x_2371_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_st_ref_set(v___y_2343_, v___x_2371_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v_trees_2347_);
return v___x_2373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___boxed(lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2379_);
lean_dec(v___y_2379_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(lean_object* v_x_2382_, lean_object* v_mkInfoTree_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2393_; lean_object* v_infoState_2394_; uint8_t v_enabled_2395_; 
v___x_2393_ = lean_st_ref_get(v___y_2391_);
v_infoState_2394_ = lean_ctor_get(v___x_2393_, 7);
lean_inc_ref(v_infoState_2394_);
lean_dec(v___x_2393_);
v_enabled_2395_ = lean_ctor_get_uint8(v_infoState_2394_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2394_);
if (v_enabled_2395_ == 0)
{
lean_object* v___x_2396_; 
lean_dec_ref(v_mkInfoTree_2383_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2388_);
lean_inc(v___y_2387_);
lean_inc_ref(v___y_2386_);
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
v___x_2396_ = lean_apply_9(v_x_2382_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, lean_box(0));
return v___x_2396_;
}
else
{
lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v_r_2399_; 
v___x_2397_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2391_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2388_);
lean_inc(v___y_2387_);
lean_inc_ref(v___y_2386_);
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
v_r_2399_ = lean_apply_9(v_x_2382_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, lean_box(0));
if (lean_obj_tag(v_r_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2424_; 
v_a_2400_ = lean_ctor_get(v_r_2399_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_r_2399_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2402_ = v_r_2399_;
v_isShared_2403_ = v_isSharedCheck_2424_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v_r_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2424_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
lean_inc(v_a_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set_tag(v___x_2402_, 1);
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2391_, v_mkInfoTree_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v_a_2398_, v___x_2405_);
lean_dec_ref(v___x_2405_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; 
v_unused_2414_ = lean_ctor_get(v___x_2406_, 0);
lean_dec(v_unused_2414_);
v___x_2408_ = v___x_2406_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_dec(v___x_2406_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v_a_2400_);
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2400_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_a_2400_);
v_a_2415_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2406_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2406_);
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
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_a_2425_ = lean_ctor_get(v_r_2399_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v_r_2399_, 1);
v___x_2426_ = lean_box(0);
v___x_2427_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2391_, v_mkInfoTree_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v_a_2398_, v___x_2426_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; 
v_unused_2435_ = lean_ctor_get(v___x_2427_, 0);
lean_dec(v_unused_2435_);
v___x_2429_ = v___x_2427_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_dec(v___x_2427_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set_tag(v___x_2429_, 1);
lean_ctor_set(v___x_2429_, 0, v_a_2425_);
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2425_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_a_2425_);
v_a_2436_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2427_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2427_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___boxed(lean_object* v_x_2444_, lean_object* v_mkInfoTree_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_2444_, v_mkInfoTree_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(lean_object* v___f_2507_, lean_object* v___f_2508_, lean_object* v_stx_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___f_2507_, v___f_2508_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec_ref_known(v___x_2519_, 1);
v___x_2520_ = lean_unsigned_to_nat(1u);
v___x_2521_ = l_Lean_Syntax_getArg(v_stx_2509_, v___x_2520_);
v___x_2522_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v___x_2521_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___x_2521_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_ref_2523_; uint8_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec_ref_known(v___x_2522_, 1);
v_ref_2523_ = lean_ctor_get(v___y_2516_, 5);
v___x_2524_ = 0;
v___x_2525_ = l_Lean_SourceInfo_fromRef(v_ref_2523_, v___x_2524_);
v___x_2526_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1));
v___x_2527_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2));
lean_inc_n(v___x_2525_, 22);
v___x_2528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2525_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4));
v___x_2530_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6));
v___x_2531_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_2532_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10));
v___x_2533_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11));
v___x_2534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2525_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13));
v___x_2536_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14));
v___x_2537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2525_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16));
v___x_2539_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17));
v___x_2540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2525_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19));
v___x_2542_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20));
v___x_2543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2525_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2541_, v___x_2543_);
v___x_2545_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2531_, v___x_2544_);
v___x_2546_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2530_, v___x_2545_);
v___x_2547_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2529_, v___x_2546_);
v___x_2548_ = l_Lean_Syntax_node2(v___x_2525_, v___x_2538_, v___x_2540_, v___x_2547_);
v___x_2549_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2531_, v___x_2548_);
v___x_2550_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2530_, v___x_2549_);
v___x_2551_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2529_, v___x_2550_);
v___x_2552_ = l_Lean_Syntax_node2(v___x_2525_, v___x_2535_, v___x_2537_, v___x_2551_);
v___x_2553_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2531_, v___x_2552_);
v___x_2554_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2530_, v___x_2553_);
v___x_2555_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2529_, v___x_2554_);
v___x_2556_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21));
v___x_2557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2525_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = l_Lean_Syntax_node3(v___x_2525_, v___x_2532_, v___x_2534_, v___x_2555_, v___x_2557_);
v___x_2559_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2531_, v___x_2558_);
v___x_2560_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2530_, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node1(v___x_2525_, v___x_2529_, v___x_2560_);
v___x_2562_ = l_Lean_Syntax_node2(v___x_2525_, v___x_2526_, v___x_2528_, v___x_2561_);
v___x_2563_ = l_Lean_Elab_Tactic_evalTactic(v___x_2562_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
return v___x_2563_;
}
else
{
return v___x_2522_;
}
}
else
{
return v___x_2519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed(lean_object* v___f_2564_, lean_object* v___f_2565_, lean_object* v_stx_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(v___f_2564_, v___f_2565_, v_stx_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v_stx_2566_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(lean_object* v_stx_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = l_Lean_Syntax_getArg(v_stx_2579_, v___x_2589_);
v___x_2591_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2590_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v_fileName_2593_; lean_object* v_fileMap_2594_; lean_object* v_options_2595_; lean_object* v_currRecDepth_2596_; lean_object* v_maxRecDepth_2597_; lean_object* v_ref_2598_; lean_object* v_currNamespace_2599_; lean_object* v_openDecls_2600_; lean_object* v_initHeartbeats_2601_; lean_object* v_maxHeartbeats_2602_; lean_object* v_quotContext_2603_; lean_object* v_currMacroScope_2604_; uint8_t v_diag_2605_; lean_object* v_cancelTk_x3f_2606_; uint8_t v_suppressElabErrors_2607_; lean_object* v_inheritedTraceOptions_2608_; lean_object* v___f_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___f_2612_; lean_object* v___f_2613_; lean_object* v_ref_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v_fileName_2593_ = lean_ctor_get(v_a_2586_, 0);
v_fileMap_2594_ = lean_ctor_get(v_a_2586_, 1);
v_options_2595_ = lean_ctor_get(v_a_2586_, 2);
v_currRecDepth_2596_ = lean_ctor_get(v_a_2586_, 3);
v_maxRecDepth_2597_ = lean_ctor_get(v_a_2586_, 4);
v_ref_2598_ = lean_ctor_get(v_a_2586_, 5);
v_currNamespace_2599_ = lean_ctor_get(v_a_2586_, 6);
v_openDecls_2600_ = lean_ctor_get(v_a_2586_, 7);
v_initHeartbeats_2601_ = lean_ctor_get(v_a_2586_, 8);
v_maxHeartbeats_2602_ = lean_ctor_get(v_a_2586_, 9);
v_quotContext_2603_ = lean_ctor_get(v_a_2586_, 10);
v_currMacroScope_2604_ = lean_ctor_get(v_a_2586_, 11);
v_diag_2605_ = lean_ctor_get_uint8(v_a_2586_, sizeof(void*)*14);
v_cancelTk_x3f_2606_ = lean_ctor_get(v_a_2586_, 12);
v_suppressElabErrors_2607_ = lean_ctor_get_uint8(v_a_2586_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2608_ = lean_ctor_get(v_a_2586_, 13);
v___f_2609_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2609_, 0, v_a_2592_);
v___x_2610_ = lean_unsigned_to_nat(2u);
v___x_2611_ = l_Lean_Syntax_getArg(v_stx_2579_, v___x_2610_);
v___f_2612_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0));
v___f_2613_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed), 12, 3);
lean_closure_set(v___f_2613_, 0, v___f_2612_);
lean_closure_set(v___f_2613_, 1, v___f_2609_);
lean_closure_set(v___f_2613_, 2, v_stx_2579_);
v_ref_2614_ = l_Lean_replaceRef(v___x_2611_, v_ref_2598_);
lean_dec(v___x_2611_);
lean_inc_ref(v_inheritedTraceOptions_2608_);
lean_inc(v_cancelTk_x3f_2606_);
lean_inc(v_currMacroScope_2604_);
lean_inc(v_quotContext_2603_);
lean_inc(v_maxHeartbeats_2602_);
lean_inc(v_initHeartbeats_2601_);
lean_inc(v_openDecls_2600_);
lean_inc(v_currNamespace_2599_);
lean_inc(v_maxRecDepth_2597_);
lean_inc(v_currRecDepth_2596_);
lean_inc_ref(v_options_2595_);
lean_inc_ref(v_fileMap_2594_);
lean_inc_ref(v_fileName_2593_);
v___x_2615_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2615_, 0, v_fileName_2593_);
lean_ctor_set(v___x_2615_, 1, v_fileMap_2594_);
lean_ctor_set(v___x_2615_, 2, v_options_2595_);
lean_ctor_set(v___x_2615_, 3, v_currRecDepth_2596_);
lean_ctor_set(v___x_2615_, 4, v_maxRecDepth_2597_);
lean_ctor_set(v___x_2615_, 5, v_ref_2614_);
lean_ctor_set(v___x_2615_, 6, v_currNamespace_2599_);
lean_ctor_set(v___x_2615_, 7, v_openDecls_2600_);
lean_ctor_set(v___x_2615_, 8, v_initHeartbeats_2601_);
lean_ctor_set(v___x_2615_, 9, v_maxHeartbeats_2602_);
lean_ctor_set(v___x_2615_, 10, v_quotContext_2603_);
lean_ctor_set(v___x_2615_, 11, v_currMacroScope_2604_);
lean_ctor_set(v___x_2615_, 12, v_cancelTk_x3f_2606_);
lean_ctor_set(v___x_2615_, 13, v_inheritedTraceOptions_2608_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*14, v_diag_2605_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*14 + 1, v_suppressElabErrors_2607_);
v___x_2616_ = l_Lean_Elab_Tactic_closeUsingOrAdmit(v___f_2613_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v___x_2615_, v_a_2587_);
lean_dec_ref_known(v___x_2615_, 14);
return v___x_2616_;
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_stx_2579_);
v_a_2617_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2591_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2591_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed(lean_object* v_stx_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(v_stx_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___boxed(lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(lean_object* v_00_u03b1_2656_, lean_object* v_x_2657_, lean_object* v_mkInfoTree_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_2657_, v_mkInfoTree_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___boxed(lean_object* v_00_u03b1_2669_, lean_object* v_x_2670_, lean_object* v_mkInfoTree_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(v_00_u03b1_2669_, v_x_2670_, v_mkInfoTree_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1(){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2697_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2698_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1));
v___x_2699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3));
v___x_2700_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed), 10, 0);
v___x_2701_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2697_, v___x_2698_, v___x_2699_, v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___boxed(lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3(){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3));
v___x_2731_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6));
v___x_2732_ = l_Lean_addBuiltinDeclarationRanges(v___x_2730_, v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___boxed(lean_object* v_a_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv(lean_object* v_stx_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = l_Lean_Syntax_getArg(v_stx_2735_, v___x_2745_);
v___x_2747_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(v___x_2746_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(lean_object* v_stx_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Elab_Tactic_Conv_evalNestedConv(v_stx_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_stx_2748_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1(){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2774_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1));
v___x_2776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3));
v___x_2777_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed), 10, 0);
v___x_2778_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2774_, v___x_2775_, v___x_2776_, v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___boxed(lean_object* v_a_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3(){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3));
v___x_2808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6));
v___x_2809_ = l_Lean_addBuiltinDeclarationRanges(v___x_2807_, v___x_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___boxed(lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq(lean_object* v_stx_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = lean_unsigned_to_nat(0u);
v___x_2823_ = l_Lean_Syntax_getArg(v_stx_2812_, v___x_2822_);
v___x_2824_ = l_Lean_Elab_Tactic_evalTactic(v___x_2823_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(lean_object* v_stx_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Elab_Tactic_Conv_evalConvSeq(v_stx_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_stx_2825_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1(){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2851_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1));
v___x_2853_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3));
v___x_2854_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed), 10, 0);
v___x_2855_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2851_, v___x_2852_, v___x_2853_, v___x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___boxed(lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3(){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3));
v___x_2885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6));
v___x_2886_ = l_Lean_addBuiltinDeclarationRanges(v___x_2884_, v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___boxed(lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(lean_object* v_stx_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_2891_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v___x_2901_ = lean_unsigned_to_nat(2u);
v___x_2902_ = l_Lean_Syntax_getArg(v_stx_2889_, v___x_2901_);
v___x_2903_ = lean_unsigned_to_nat(0u);
v___x_2904_ = l_Lean_Syntax_getArg(v___x_2902_, v___x_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_2905_, 0, v___x_2904_);
v___x_2906_ = l_Lean_Elab_Tactic_Conv_convert(v_a_2900_, v___x_2905_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v_fst_2908_; lean_object* v_snd_2909_; lean_object* v___x_2910_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref_known(v___x_2906_, 1);
v_fst_2908_ = lean_ctor_get(v_a_2907_, 0);
lean_inc(v_fst_2908_);
v_snd_2909_ = lean_ctor_get(v_a_2907_, 1);
lean_inc(v_snd_2909_);
lean_dec(v_a_2907_);
v___x_2910_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_fst_2908_, v_snd_2909_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
return v___x_2910_;
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v_a_2911_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2906_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2906_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
v_a_2919_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2899_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2899_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed(lean_object* v_stx_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(v_stx_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v_stx_2927_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq(lean_object* v_stx_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v___f_2948_; lean_object* v___x_2949_; 
v___f_2948_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2948_, 0, v_stx_2938_);
v___x_2949_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2948_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed(lean_object* v_stx_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq(v_stx_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1(){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2976_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2977_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1));
v___x_2978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3));
v___x_2979_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed), 10, 0);
v___x_2980_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2976_, v___x_2977_, v___x_2978_, v___x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___boxed(lean_object* v_a_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3(){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3));
v___x_3010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6));
v___x_3011_ = l_Lean_addBuiltinDeclarationRanges(v___x_3009_, v___x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___boxed(lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen(lean_object* v_stx_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_unsigned_to_nat(1u);
v___x_3025_ = l_Lean_Syntax_getArg(v_stx_3014_, v___x_3024_);
v___x_3026_ = l_Lean_Elab_Tactic_evalTactic(v___x_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___boxed(lean_object* v_stx_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_Elab_Tactic_Conv_evalParen(v_stx_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_stx_3027_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1(){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3052_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0));
v___x_3054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2));
v___x_3055_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalParen___boxed), 10, 0);
v___x_3056_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3052_, v___x_3053_, v___x_3054_, v___x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___boxed(lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3(){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2));
v___x_3086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6));
v___x_3087_ = l_Lean_addBuiltinDeclarationRanges(v___x_3085_, v___x_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___boxed(lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; 
lean_inc(v___y_3094_);
lean_inc_ref(v___y_3093_);
lean_inc(v___y_3092_);
lean_inc_ref(v___y_3091_);
v___x_3100_ = lean_apply_9(v_x_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, lean_box(0));
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed(lean_object* v_x_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(v_x_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(lean_object* v_mvarId_3112_, lean_object* v_x_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v___f_3123_; lean_object* v___x_3124_; 
lean_inc(v___y_3117_);
lean_inc_ref(v___y_3116_);
lean_inc(v___y_3115_);
lean_inc_ref(v___y_3114_);
v___f_3123_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3123_, 0, v_x_3113_);
lean_closure_set(v___f_3123_, 1, v___y_3114_);
lean_closure_set(v___f_3123_, 2, v___y_3115_);
lean_closure_set(v___f_3123_, 3, v___y_3116_);
lean_closure_set(v___f_3123_, 4, v___y_3117_);
v___x_3124_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3112_, v___f_3123_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
if (lean_obj_tag(v___x_3124_) == 0)
{
return v___x_3124_;
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___boxed(lean_object* v_mvarId_3133_, lean_object* v_x_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_mvarId_3133_, v_x_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(lean_object* v_00_u03b1_3145_, lean_object* v_mvarId_3146_, lean_object* v_x_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_mvarId_3146_, v_x_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___boxed(lean_object* v_00_u03b1_3158_, lean_object* v_mvarId_3159_, lean_object* v_x_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(v_00_u03b1_3158_, v_mvarId_3159_, v_x_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(lean_object* v_head_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
lean_inc(v_head_3171_);
v___x_3181_ = l_Lean_MVarId_getType(v_head_3171_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc_n(v_a_3182_, 2);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3183_ = l_Lean_Meta_matchEq_x3f(v_a_3182_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3210_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3210_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3210_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
if (lean_obj_tag(v_a_3184_) == 1)
{
lean_object* v_val_3188_; lean_object* v_snd_3189_; lean_object* v_snd_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v_val_3188_ = lean_ctor_get(v_a_3184_, 0);
lean_inc(v_val_3188_);
lean_dec_ref_known(v_a_3184_, 1);
v_snd_3189_ = lean_ctor_get(v_val_3188_, 1);
lean_inc(v_snd_3189_);
lean_dec(v_val_3188_);
v_snd_3190_ = lean_ctor_get(v_snd_3189_, 1);
lean_inc(v_snd_3190_);
lean_dec(v_snd_3189_);
v___x_3191_ = l_Lean_Expr_getAppFn(v_snd_3190_);
lean_dec(v_snd_3190_);
v___x_3192_ = l_Lean_Expr_isMVar(v___x_3191_);
lean_dec_ref(v___x_3191_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3194_; 
lean_dec(v_a_3182_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v_head_3171_);
v___x_3194_ = v___x_3186_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_head_3171_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
else
{
lean_object* v___x_3196_; 
lean_del_object(v___x_3186_);
v___x_3196_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(v_a_3182_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3198_ = l_Lean_MVarId_replaceTargetDefEq(v_head_3171_, v_a_3197_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3198_;
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec(v_head_3171_);
v_a_3199_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3196_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3196_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
else
{
lean_object* v___x_3208_; 
lean_dec(v_a_3184_);
lean_dec(v_a_3182_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v_head_3171_);
v___x_3208_ = v___x_3186_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_head_3171_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_a_3182_);
lean_dec(v_head_3171_);
v_a_3211_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3183_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3183_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v_head_3171_);
v_a_3219_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3181_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3181_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed(lean_object* v_head_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(v_head_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(lean_object* v_x_3238_, lean_object* v_x_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
if (lean_obj_tag(v_x_3238_) == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = l_List_reverse___redArg(v_x_3239_);
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
return v___x_3250_;
}
else
{
lean_object* v_head_3251_; lean_object* v_tail_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3271_; 
v_head_3251_ = lean_ctor_get(v_x_3238_, 0);
v_tail_3252_ = lean_ctor_get(v_x_3238_, 1);
v_isSharedCheck_3271_ = !lean_is_exclusive(v_x_3238_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3254_ = v_x_3238_;
v_isShared_3255_ = v_isSharedCheck_3271_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_tail_3252_);
lean_inc(v_head_3251_);
lean_dec(v_x_3238_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3271_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___f_3256_; lean_object* v___x_3257_; 
lean_inc(v_head_3251_);
v___f_3256_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3256_, 0, v_head_3251_);
v___x_3257_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_head_3251_, v___f_3256_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___x_3257_, 1);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 1, v_x_3239_);
lean_ctor_set(v___x_3254_, 0, v_a_3258_);
v___x_3260_ = v___x_3254_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3258_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_x_3239_);
v___x_3260_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
v_x_3238_ = v_tail_3252_;
v_x_3239_ = v___x_3260_;
goto _start;
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_del_object(v___x_3254_);
lean_dec(v_tail_3252_);
lean_dec(v_x_3239_);
v_a_3263_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3257_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3257_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___boxed(lean_object* v_x_3272_, lean_object* v_x_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(v_x_3272_, v_x_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3293_, 1);
v___x_3295_ = lean_box(0);
v___x_3296_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(v_a_3294_, v___x_3295_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v___x_3298_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_3297_, v_a_3285_);
return v___x_3298_;
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
v_a_3299_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3296_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3296_);
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
v_a_3307_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3293_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3293_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal___boxed(lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(lean_object* v_stx_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v___x_3335_; lean_object* v_seq_3336_; lean_object* v___x_3337_; 
v___x_3335_ = lean_unsigned_to_nat(2u);
v_seq_3336_ = l_Lean_Syntax_getArg(v_stx_3325_, v___x_3335_);
v___x_3337_ = l_Lean_Elab_Tactic_evalTactic(v_seq_3336_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v___x_3338_; 
lean_dec_ref_known(v___x_3337_, 1);
v___x_3338_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
return v___x_3338_;
}
else
{
return v___x_3337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed(lean_object* v_stx_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(v_stx_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
lean_dec(v_stx_3339_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1(){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3365_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1));
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3));
v___x_3368_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed), 10, 0);
v___x_3369_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3365_, v___x_3366_, v___x_3367_, v___x_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___boxed(lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3(){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3));
v___x_3399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6));
v___x_3400_ = l_Lean_addBuiltinDeclarationRanges(v___x_3398_, v___x_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___boxed(lean_object* v_a_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(lean_object* v_seq_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Elab_Tactic_evalTactic(v_seq_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v___x_3414_; 
lean_dec_ref_known(v___x_3413_, 1);
v___x_3414_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
return v___x_3414_;
}
else
{
return v___x_3413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed(lean_object* v_seq_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(v_seq_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(lean_object* v_a_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v___x_3436_; 
v___x_3436_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3428_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
v___x_3438_ = l_Lean_Expr_mdataExpr_x21(v_a_3426_);
v___x_3439_ = l_Lean_MVarId_replaceTargetDefEq(v_a_3437_, v___x_3438_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___x_3441_ = lean_box(0);
v___x_3442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3442_, 0, v_a_3440_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3442_, v___y_3428_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
return v___x_3443_;
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_a_3444_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3439_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3439_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
v_a_3452_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3436_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3436_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed(lean_object* v_a_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(v_a_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec_ref(v_a_3460_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic(lean_object* v_stx_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v___x_3481_; 
v___x_3481_ = l_Lean_Elab_Tactic_getMainTarget(v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; lean_object* v_seq_3484_; lean_object* v___f_3485_; lean_object* v___x_3486_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3481_, 1);
v___x_3483_ = lean_unsigned_to_nat(2u);
v_seq_3484_ = l_Lean_Syntax_getArg(v_stx_3471_, v___x_3483_);
v___f_3485_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3485_, 0, v_seq_3484_);
v___x_3486_ = l_Lean_isLHSGoal_x3f(v_a_3482_);
if (lean_obj_tag(v___x_3486_) == 1)
{
lean_object* v___f_3487_; lean_object* v___x_3488_; 
lean_dec_ref_known(v___x_3486_, 1);
v___f_3487_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3487_, 0, v_a_3482_);
v___x_3488_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3487_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v___x_3489_; 
lean_dec_ref_known(v___x_3488_, 1);
v___x_3489_ = l_Lean_Elab_Tactic_focus___redArg(v___f_3485_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
return v___x_3489_;
}
else
{
lean_dec_ref(v___f_3485_);
return v___x_3488_;
}
}
else
{
lean_object* v___x_3490_; 
lean_dec(v___x_3486_);
lean_dec(v_a_3482_);
v___x_3490_ = l_Lean_Elab_Tactic_focus___redArg(v___f_3485_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
return v___x_3490_;
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
v_a_3491_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3481_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3481_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(lean_object* v_stx_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic(v_stx_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
lean_dec(v_stx_3499_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1(){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3525_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3526_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1));
v___x_3527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3));
v___x_3528_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed), 10, 0);
v___x_3529_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3525_, v___x_3526_, v___x_3527_, v___x_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___boxed(lean_object* v_a_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3(){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3));
v___x_3559_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6));
v___x_3560_ = l_Lean_addBuiltinDeclarationRanges(v___x_3558_, v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___boxed(lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic(lean_object* v_stx_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = lean_unsigned_to_nat(2u);
v___x_3574_ = l_Lean_Syntax_getArg(v_stx_3563_, v___x_3573_);
v___x_3575_ = l_Lean_Elab_Tactic_evalTactic(v___x_3574_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(lean_object* v_stx_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_Elab_Tactic_Conv_evalConvTactic(v_stx_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_stx_3576_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1(){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3602_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1));
v___x_3604_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3));
v___x_3605_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed), 10, 0);
v___x_3606_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3602_, v___x_3603_, v___x_3604_, v___x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___boxed(lean_object* v_a_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3(){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3));
v___x_3636_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6));
v___x_3637_ = l_Lean_addBuiltinDeclarationRanges(v___x_3635_, v___x_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___boxed(lean_object* v_a_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(lean_object* v_ref_3640_, lean_object* v___x_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_3640_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___f_3653_; lean_object* v___x_3654_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v___f_3653_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3653_, 0, v_a_3652_);
v___x_3654_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___x_3641_, v___f_3653_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
return v___x_3654_;
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec_ref(v___x_3641_);
v_a_3655_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3651_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3651_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed(lean_object* v_ref_3663_, lean_object* v___x_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(v_ref_3663_, v___x_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(lean_object* v_fst_3675_, lean_object* v_snd_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3678_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3688_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v___x_3688_ = l_Lean_MVarId_replaceTargetEq(v_a_3687_, v_fst_3675_, v_snd_3676_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___x_3688_, 1);
v___x_3690_ = lean_box(0);
v___x_3691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3691_, 0, v_a_3689_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
v___x_3692_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3691_, v___y_3678_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
return v___x_3692_;
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
v_a_3693_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3688_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3688_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref(v_snd_3676_);
lean_dec_ref(v_fst_3675_);
v_a_3701_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3686_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3686_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed(lean_object* v_fst_3709_, lean_object* v_snd_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(v_fst_3709_, v_snd_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(lean_object* v_conv_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lean_Elab_Tactic_getMainTarget(v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v_ref_3733_; lean_object* v___x_3734_; lean_object* v___f_3735_; lean_object* v___x_3736_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
v_ref_3733_ = lean_ctor_get(v___y_3728_, 5);
v___x_3734_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_3734_, 0, v_conv_3721_);
lean_inc(v_ref_3733_);
v___f_3735_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3735_, 0, v_ref_3733_);
lean_closure_set(v___f_3735_, 1, v___x_3734_);
v___x_3736_ = l_Lean_Elab_Tactic_Conv_convert(v_a_3732_, v___f_3735_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v_fst_3738_; lean_object* v_snd_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3771_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3736_, 1);
v_fst_3738_ = lean_ctor_get(v_a_3737_, 0);
v_snd_3739_ = lean_ctor_get(v_a_3737_, 1);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_a_3737_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3741_ = v_a_3737_;
v_isShared_3742_ = v_isSharedCheck_3771_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_snd_3739_);
lean_inc(v_fst_3738_);
lean_dec(v_a_3737_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3771_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___f_3743_; lean_object* v___x_3744_; 
v___f_3743_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3743_, 0, v_fst_3738_);
lean_closure_set(v___f_3743_, 1, v_snd_3739_);
v___x_3744_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3743_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3744_) == 0)
{
uint8_t v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3750_; 
lean_dec_ref_known(v___x_3744_, 1);
v___x_3745_ = 0;
v___x_3746_ = l_Lean_SourceInfo_fromRef(v_ref_3733_, v___x_3745_);
v___x_3747_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13));
v___x_3748_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14));
lean_inc(v___x_3746_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set_tag(v___x_3741_, 2);
lean_ctor_set(v___x_3741_, 1, v___x_3748_);
lean_ctor_set(v___x_3741_, 0, v___x_3746_);
v___x_3750_ = v___x_3741_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3751_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4));
v___x_3752_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6));
v___x_3753_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_3754_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16));
v___x_3755_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17));
lean_inc_n(v___x_3746_, 10);
v___x_3756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3746_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19));
v___x_3758_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20));
v___x_3759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3746_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = l_Lean_Syntax_node1(v___x_3746_, v___x_3757_, v___x_3759_);
v___x_3761_ = l_Lean_Syntax_node1(v___x_3746_, v___x_3753_, v___x_3760_);
v___x_3762_ = l_Lean_Syntax_node1(v___x_3746_, v___x_3752_, v___x_3761_);
v___x_3763_ = l_Lean_Syntax_node1(v___x_3746_, v___x_3751_, v___x_3762_);
v___x_3764_ = l_Lean_Syntax_node2(v___x_3746_, v___x_3754_, v___x_3756_, v___x_3763_);
v___x_3765_ = l_Lean_Syntax_node1(v___x_3746_, v___x_3753_, v___x_3764_);
v___x_3766_ = l_Lean_Syntax_node1(v___x_3746_, v___x_3752_, v___x_3765_);
v___x_3767_ = l_Lean_Syntax_node1(v___x_3746_, v___x_3751_, v___x_3766_);
v___x_3768_ = l_Lean_Syntax_node2(v___x_3746_, v___x_3747_, v___x_3750_, v___x_3767_);
v___x_3769_ = l_Lean_Elab_Tactic_evalTactic(v___x_3768_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec_ref(v___y_3728_);
return v___x_3769_;
}
}
else
{
lean_del_object(v___x_3741_);
lean_dec_ref(v___y_3728_);
return v___x_3744_;
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec_ref(v___y_3728_);
v_a_3772_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3736_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3736_);
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
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec_ref(v___y_3728_);
lean_dec(v_conv_3721_);
v_a_3780_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3731_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3731_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed(lean_object* v_conv_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(v_conv_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(lean_object* v_conv_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v___f_3809_; lean_object* v___x_3810_; 
v___f_3809_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3809_, 0, v_conv_3799_);
v___x_3810_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3809_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___boxed(lean_object* v_conv_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(v_conv_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
lean_dec(v_a_3819_);
lean_dec_ref(v_a_3818_);
lean_dec(v_a_3817_);
lean_dec_ref(v_a_3816_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(lean_object* v_snd_3822_, lean_object* v___x_3823_, lean_object* v_fst_3824_, lean_object* v_a_3825_, lean_object* v___x_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_Meta_mkEqMP(v_snd_3822_, v___x_3823_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___x_3832_, 1);
v___x_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3834_, 0, v_fst_3824_);
v___x_3835_ = lean_box(0);
v___x_3836_ = l_Lean_MVarId_replace(v_a_3825_, v___x_3826_, v_a_3833_, v___x_3834_, v___x_3835_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
return v___x_3836_;
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec(v___x_3826_);
lean_dec(v_a_3825_);
lean_dec_ref(v_fst_3824_);
v_a_3837_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3832_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3832_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed(lean_object* v_snd_3845_, lean_object* v___x_3846_, lean_object* v_fst_3847_, lean_object* v_a_3848_, lean_object* v___x_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(v_snd_3845_, v___x_3846_, v_fst_3847_, v_a_3848_, v___x_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(lean_object* v_a_3856_, lean_object* v_snd_3857_, lean_object* v_fst_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3860_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___f_3872_; lean_object* v___x_3873_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc_n(v_a_3869_, 2);
lean_dec_ref_known(v___x_3868_, 1);
v___x_3870_ = l_Lean_LocalDecl_fvarId(v_a_3856_);
lean_inc(v___x_3870_);
v___x_3871_ = l_Lean_mkFVar(v___x_3870_);
v___f_3872_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3872_, 0, v_snd_3857_);
lean_closure_set(v___f_3872_, 1, v___x_3871_);
lean_closure_set(v___f_3872_, 2, v_fst_3858_);
lean_closure_set(v___f_3872_, 3, v_a_3869_);
lean_closure_set(v___f_3872_, 4, v___x_3870_);
v___x_3873_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_a_3869_, v___f_3872_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v_mvarId_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v_mvarId_3875_ = lean_ctor_get(v_a_3874_, 1);
lean_inc(v_mvarId_3875_);
lean_dec(v_a_3874_);
v___x_3876_ = lean_box(0);
v___x_3877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3877_, 0, v_mvarId_3875_);
lean_ctor_set(v___x_3877_, 1, v___x_3876_);
v___x_3878_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3877_, v___y_3860_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3878_;
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
v_a_3879_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3873_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3873_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_fst_3858_);
lean_dec_ref(v_snd_3857_);
v_a_3887_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3868_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3868_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed(lean_object* v_a_3895_, lean_object* v_snd_3896_, lean_object* v_fst_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(v_a_3895_, v_snd_3896_, v_fst_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec_ref(v_a_3895_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(lean_object* v_hUserName_3908_, lean_object* v_conv_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_Lean_Meta_getLocalDeclFromUserName(v_hUserName_3908_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v_ref_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___f_3924_; lean_object* v___x_3925_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v___x_3919_, 1);
v_ref_3921_ = lean_ctor_get(v___y_3916_, 5);
v___x_3922_ = l_Lean_LocalDecl_type(v_a_3920_);
v___x_3923_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_3923_, 0, v_conv_3909_);
lean_inc(v_ref_3921_);
v___f_3924_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3924_, 0, v_ref_3921_);
lean_closure_set(v___f_3924_, 1, v___x_3923_);
v___x_3925_ = l_Lean_Elab_Tactic_Conv_convert(v___x_3922_, v___f_3924_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v_fst_3927_; lean_object* v_snd_3928_; lean_object* v___f_3929_; lean_object* v___x_3930_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref_known(v___x_3925_, 1);
v_fst_3927_ = lean_ctor_get(v_a_3926_, 0);
lean_inc(v_fst_3927_);
v_snd_3928_ = lean_ctor_get(v_a_3926_, 1);
lean_inc(v_snd_3928_);
lean_dec(v_a_3926_);
v___f_3929_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3929_, 0, v_a_3920_);
lean_closure_set(v___f_3929_, 1, v_snd_3928_);
lean_closure_set(v___f_3929_, 2, v_fst_3927_);
v___x_3930_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3929_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
lean_dec_ref(v___y_3916_);
return v___x_3930_;
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec(v_a_3920_);
lean_dec_ref(v___y_3916_);
v_a_3931_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3925_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3925_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_dec_ref(v___y_3916_);
lean_dec(v_conv_3909_);
v_a_3939_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3919_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3919_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed(lean_object* v_hUserName_3947_, lean_object* v_conv_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(v_hUserName_3947_, v_conv_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(lean_object* v_conv_3959_, lean_object* v_hUserName_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v___f_3970_; lean_object* v___x_3971_; 
v___f_3970_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3970_, 0, v_hUserName_3960_);
lean_closure_set(v___f_3970_, 1, v_conv_3959_);
v___x_3971_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3970_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___boxed(lean_object* v_conv_3972_, lean_object* v_hUserName_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(v_conv_3972_, v_hUserName_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
return v_res_3983_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7(void){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Array_mkArray0(lean_box(0));
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv(lean_object* v_stx_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; uint8_t v___x_4055_; 
v___x_4014_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__0));
v___x_4015_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__1));
lean_inc(v_stx_4004_);
v___x_4055_ = l_Lean_Syntax_isOfKind(v_stx_4004_, v___x_4015_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4056_; 
lean_dec(v_stx_4004_);
v___x_4056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4056_;
}
else
{
lean_object* v___x_4057_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v_tk_4091_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___x_4119_; lean_object* v_loc_x3f_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___x_4183_; uint8_t v___x_4184_; 
v___x_4057_ = lean_unsigned_to_nat(0u);
v_tk_4091_ = l_Lean_Syntax_getArg(v_stx_4004_, v___x_4057_);
v___x_4119_ = lean_unsigned_to_nat(1u);
v___x_4183_ = l_Lean_Syntax_getArg(v_stx_4004_, v___x_4119_);
v___x_4184_ = l_Lean_Syntax_isNone(v___x_4183_);
if (v___x_4184_ == 0)
{
lean_object* v___x_4185_; uint8_t v___x_4186_; 
v___x_4185_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4183_);
v___x_4186_ = l_Lean_Syntax_matchesNull(v___x_4183_, v___x_4185_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; 
lean_dec(v___x_4183_);
lean_dec(v_tk_4091_);
lean_dec(v_stx_4004_);
v___x_4187_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4187_;
}
else
{
lean_object* v_loc_x3f_4188_; lean_object* v___x_4189_; 
v_loc_x3f_4188_ = l_Lean_Syntax_getArg(v___x_4183_, v___x_4119_);
lean_dec(v___x_4183_);
v___x_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4189_, 0, v_loc_x3f_4188_);
v_loc_x3f_4121_ = v___x_4189_;
v___y_4122_ = v_a_4005_;
v___y_4123_ = v_a_4006_;
v___y_4124_ = v_a_4007_;
v___y_4125_ = v_a_4008_;
v___y_4126_ = v_a_4009_;
v___y_4127_ = v_a_4010_;
v___y_4128_ = v_a_4011_;
v___y_4129_ = v_a_4012_;
goto v___jp_4120_;
}
}
else
{
lean_object* v___x_4190_; 
lean_dec(v___x_4183_);
v___x_4190_ = lean_box(0);
v_loc_x3f_4121_ = v___x_4190_;
v___y_4122_ = v_a_4005_;
v___y_4123_ = v_a_4006_;
v___y_4124_ = v_a_4007_;
v___y_4125_ = v_a_4008_;
v___y_4126_ = v_a_4009_;
v___y_4127_ = v_a_4010_;
v___y_4128_ = v_a_4011_;
v___y_4129_ = v_a_4012_;
goto v___jp_4120_;
}
v___jp_4058_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
lean_inc_ref_n(v___y_4075_, 2);
v___x_4077_ = l_Array_append___redArg(v___y_4075_, v___y_4076_);
lean_dec_ref(v___y_4076_);
lean_inc_n(v___y_4064_, 2);
lean_inc_n(v___y_4066_, 3);
v___x_4078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4078_, 0, v___y_4066_);
lean_ctor_set(v___x_4078_, 1, v___y_4064_);
lean_ctor_set(v___x_4078_, 2, v___x_4077_);
v___x_4079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4079_, 0, v___y_4066_);
lean_ctor_set(v___x_4079_, 1, v___y_4064_);
lean_ctor_set(v___x_4079_, 2, v___y_4075_);
v___x_4080_ = l_Lean_SourceInfo_fromRef(v___y_4069_, v___x_4055_);
lean_dec(v___y_4069_);
v___x_4081_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__3));
v___x_4082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4080_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1));
v___x_4084_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__4));
v___x_4085_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__5));
v___x_4086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___y_4066_);
lean_ctor_set(v___x_4086_, 1, v___x_4084_);
if (lean_obj_tag(v___y_4065_) == 0)
{
lean_object* v___x_4087_; 
v___x_4087_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___y_4017_ = v___y_4059_;
v___y_4018_ = v___x_4086_;
v___y_4019_ = v___y_4060_;
v___y_4020_ = v___x_4083_;
v___y_4021_ = v___y_4061_;
v___y_4022_ = v___y_4062_;
v___y_4023_ = v___y_4063_;
v___y_4024_ = v___x_4079_;
v___y_4025_ = v___x_4085_;
v___y_4026_ = v___y_4064_;
v___y_4027_ = v___x_4082_;
v___y_4028_ = v___y_4066_;
v___y_4029_ = v___y_4067_;
v___y_4030_ = v___x_4078_;
v___y_4031_ = v___y_4068_;
v___y_4032_ = v___y_4070_;
v___y_4033_ = v___y_4071_;
v___y_4034_ = v___y_4072_;
v___y_4035_ = v___y_4073_;
v___y_4036_ = v___y_4074_;
v___y_4037_ = v___y_4075_;
v___y_4038_ = v___x_4087_;
goto v___jp_4016_;
}
else
{
lean_object* v_val_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_val_4088_ = lean_ctor_get(v___y_4065_, 0);
lean_inc(v_val_4088_);
lean_dec_ref_known(v___y_4065_, 1);
v___x_4089_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___x_4090_ = lean_array_push(v___x_4089_, v_val_4088_);
v___y_4017_ = v___y_4059_;
v___y_4018_ = v___x_4086_;
v___y_4019_ = v___y_4060_;
v___y_4020_ = v___x_4083_;
v___y_4021_ = v___y_4061_;
v___y_4022_ = v___y_4062_;
v___y_4023_ = v___y_4063_;
v___y_4024_ = v___x_4079_;
v___y_4025_ = v___x_4085_;
v___y_4026_ = v___y_4064_;
v___y_4027_ = v___x_4082_;
v___y_4028_ = v___y_4066_;
v___y_4029_ = v___y_4067_;
v___y_4030_ = v___x_4078_;
v___y_4031_ = v___y_4068_;
v___y_4032_ = v___y_4070_;
v___y_4033_ = v___y_4071_;
v___y_4034_ = v___y_4072_;
v___y_4035_ = v___y_4073_;
v___y_4036_ = v___y_4074_;
v___y_4037_ = v___y_4075_;
v___y_4038_ = v___x_4090_;
goto v___jp_4016_;
}
}
v___jp_4092_:
{
lean_object* v_ref_4107_; uint8_t v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v_ref_4107_ = lean_ctor_get(v___y_4105_, 5);
v___x_4108_ = 0;
v___x_4109_ = l_Lean_SourceInfo_fromRef(v_ref_4107_, v___x_4108_);
v___x_4110_ = l_Lean_SourceInfo_fromRef(v_tk_4091_, v___x_4055_);
lean_dec(v_tk_4091_);
v___x_4111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
lean_ctor_set(v___x_4111_, 1, v___x_4014_);
v___x_4112_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_4113_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalConv___closed__7, &l_Lean_Elab_Tactic_Conv_evalConv___closed__7_once, _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7);
if (lean_obj_tag(v___y_4098_) == 1)
{
lean_object* v_val_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v_val_4114_ = lean_ctor_get(v___y_4098_, 0);
lean_inc(v_val_4114_);
lean_dec_ref_known(v___y_4098_, 1);
v___x_4115_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__8));
lean_inc(v___x_4109_);
v___x_4116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4109_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = l_Array_mkArray2___redArg(v___x_4116_, v_val_4114_);
v___y_4059_ = v___y_4093_;
v___y_4060_ = v___x_4111_;
v___y_4061_ = v___y_4094_;
v___y_4062_ = v___y_4095_;
v___y_4063_ = v___y_4096_;
v___y_4064_ = v___x_4112_;
v___y_4065_ = v___y_4106_;
v___y_4066_ = v___x_4109_;
v___y_4067_ = v___y_4097_;
v___y_4068_ = v___y_4099_;
v___y_4069_ = v___y_4100_;
v___y_4070_ = v___y_4101_;
v___y_4071_ = v___y_4102_;
v___y_4072_ = v___y_4103_;
v___y_4073_ = v___y_4104_;
v___y_4074_ = v___y_4105_;
v___y_4075_ = v___x_4113_;
v___y_4076_ = v___x_4117_;
goto v___jp_4058_;
}
else
{
lean_object* v___x_4118_; 
lean_dec(v___y_4098_);
v___x_4118_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___y_4059_ = v___y_4093_;
v___y_4060_ = v___x_4111_;
v___y_4061_ = v___y_4094_;
v___y_4062_ = v___y_4095_;
v___y_4063_ = v___y_4096_;
v___y_4064_ = v___x_4112_;
v___y_4065_ = v___y_4106_;
v___y_4066_ = v___x_4109_;
v___y_4067_ = v___y_4097_;
v___y_4068_ = v___y_4099_;
v___y_4069_ = v___y_4100_;
v___y_4070_ = v___y_4101_;
v___y_4071_ = v___y_4102_;
v___y_4072_ = v___y_4103_;
v___y_4073_ = v___y_4104_;
v___y_4074_ = v___y_4105_;
v___y_4075_ = v___x_4113_;
v___y_4076_ = v___x_4118_;
goto v___jp_4058_;
}
}
v___jp_4120_:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; uint8_t v___x_4133_; 
v___x_4130_ = lean_unsigned_to_nat(2u);
v___x_4131_ = l_Lean_Syntax_getArg(v_stx_4004_, v___x_4130_);
v___x_4132_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_4131_);
v___x_4133_ = l_Lean_Syntax_matchesNull(v___x_4131_, v___x_4132_);
if (v___x_4133_ == 0)
{
uint8_t v___x_4134_; 
v___x_4134_ = l_Lean_Syntax_matchesNull(v___x_4131_, v___x_4057_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; 
lean_dec(v_loc_x3f_4121_);
lean_dec(v_tk_4091_);
lean_dec(v_stx_4004_);
v___x_4135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4135_;
}
else
{
lean_object* v_fileName_4136_; lean_object* v_fileMap_4137_; lean_object* v_options_4138_; lean_object* v_currRecDepth_4139_; lean_object* v_maxRecDepth_4140_; lean_object* v_ref_4141_; lean_object* v_currNamespace_4142_; lean_object* v_openDecls_4143_; lean_object* v_initHeartbeats_4144_; lean_object* v_maxHeartbeats_4145_; lean_object* v_quotContext_4146_; lean_object* v_currMacroScope_4147_; uint8_t v_diag_4148_; lean_object* v_cancelTk_x3f_4149_; uint8_t v_suppressElabErrors_4150_; lean_object* v_inheritedTraceOptions_4151_; lean_object* v_arr_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v_ref_4161_; lean_object* v___x_4162_; 
v_fileName_4136_ = lean_ctor_get(v___y_4128_, 0);
v_fileMap_4137_ = lean_ctor_get(v___y_4128_, 1);
v_options_4138_ = lean_ctor_get(v___y_4128_, 2);
v_currRecDepth_4139_ = lean_ctor_get(v___y_4128_, 3);
v_maxRecDepth_4140_ = lean_ctor_get(v___y_4128_, 4);
v_ref_4141_ = lean_ctor_get(v___y_4128_, 5);
v_currNamespace_4142_ = lean_ctor_get(v___y_4128_, 6);
v_openDecls_4143_ = lean_ctor_get(v___y_4128_, 7);
v_initHeartbeats_4144_ = lean_ctor_get(v___y_4128_, 8);
v_maxHeartbeats_4145_ = lean_ctor_get(v___y_4128_, 9);
v_quotContext_4146_ = lean_ctor_get(v___y_4128_, 10);
v_currMacroScope_4147_ = lean_ctor_get(v___y_4128_, 11);
v_diag_4148_ = lean_ctor_get_uint8(v___y_4128_, sizeof(void*)*14);
v_cancelTk_x3f_4149_ = lean_ctor_get(v___y_4128_, 12);
v_suppressElabErrors_4150_ = lean_ctor_get_uint8(v___y_4128_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4151_ = lean_ctor_get(v___y_4128_, 13);
v_arr_4152_ = l_Lean_Syntax_getArg(v_stx_4004_, v___x_4132_);
v___x_4153_ = lean_unsigned_to_nat(4u);
v___x_4154_ = l_Lean_Syntax_getArg(v_stx_4004_, v___x_4153_);
lean_dec(v_stx_4004_);
v___x_4155_ = lean_mk_empty_array_with_capacity(v___x_4130_);
v___x_4156_ = lean_array_push(v___x_4155_, v_tk_4091_);
v___x_4157_ = lean_array_push(v___x_4156_, v_arr_4152_);
v___x_4158_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_4159_ = lean_box(2);
v___x_4160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
lean_ctor_set(v___x_4160_, 1, v___x_4158_);
lean_ctor_set(v___x_4160_, 2, v___x_4157_);
v_ref_4161_ = l_Lean_replaceRef(v___x_4160_, v_ref_4141_);
lean_dec_ref_known(v___x_4160_, 3);
lean_inc_ref(v_inheritedTraceOptions_4151_);
lean_inc(v_cancelTk_x3f_4149_);
lean_inc(v_currMacroScope_4147_);
lean_inc(v_quotContext_4146_);
lean_inc(v_maxHeartbeats_4145_);
lean_inc(v_initHeartbeats_4144_);
lean_inc(v_openDecls_4143_);
lean_inc(v_currNamespace_4142_);
lean_inc(v_maxRecDepth_4140_);
lean_inc(v_currRecDepth_4139_);
lean_inc_ref(v_options_4138_);
lean_inc_ref(v_fileMap_4137_);
lean_inc_ref(v_fileName_4136_);
v___x_4162_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4162_, 0, v_fileName_4136_);
lean_ctor_set(v___x_4162_, 1, v_fileMap_4137_);
lean_ctor_set(v___x_4162_, 2, v_options_4138_);
lean_ctor_set(v___x_4162_, 3, v_currRecDepth_4139_);
lean_ctor_set(v___x_4162_, 4, v_maxRecDepth_4140_);
lean_ctor_set(v___x_4162_, 5, v_ref_4161_);
lean_ctor_set(v___x_4162_, 6, v_currNamespace_4142_);
lean_ctor_set(v___x_4162_, 7, v_openDecls_4143_);
lean_ctor_set(v___x_4162_, 8, v_initHeartbeats_4144_);
lean_ctor_set(v___x_4162_, 9, v_maxHeartbeats_4145_);
lean_ctor_set(v___x_4162_, 10, v_quotContext_4146_);
lean_ctor_set(v___x_4162_, 11, v_currMacroScope_4147_);
lean_ctor_set(v___x_4162_, 12, v_cancelTk_x3f_4149_);
lean_ctor_set(v___x_4162_, 13, v_inheritedTraceOptions_4151_);
lean_ctor_set_uint8(v___x_4162_, sizeof(void*)*14, v_diag_4148_);
lean_ctor_set_uint8(v___x_4162_, sizeof(void*)*14 + 1, v_suppressElabErrors_4150_);
if (lean_obj_tag(v_loc_x3f_4121_) == 1)
{
lean_object* v_val_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_val_4163_ = lean_ctor_get(v_loc_x3f_4121_, 0);
lean_inc(v_val_4163_);
lean_dec_ref_known(v_loc_x3f_4121_, 1);
v___x_4164_ = l_Lean_TSyntax_getId(v_val_4163_);
lean_dec(v_val_4163_);
v___x_4165_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(v___x_4154_, v___x_4164_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___x_4162_, v___y_4129_);
lean_dec_ref_known(v___x_4162_, 14);
return v___x_4165_;
}
else
{
lean_object* v___x_4166_; 
lean_dec(v_loc_x3f_4121_);
v___x_4166_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(v___x_4154_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___x_4162_, v___y_4129_);
lean_dec_ref_known(v___x_4162_, 14);
return v___x_4166_;
}
}
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v_arr_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4167_ = l_Lean_Syntax_getArg(v___x_4131_, v___x_4119_);
v___x_4168_ = l_Lean_Syntax_getArg(v___x_4131_, v___x_4130_);
lean_dec(v___x_4131_);
v_arr_4169_ = l_Lean_Syntax_getArg(v_stx_4004_, v___x_4132_);
v___x_4170_ = lean_unsigned_to_nat(4u);
v___x_4171_ = l_Lean_Syntax_getArg(v_stx_4004_, v___x_4170_);
lean_dec(v_stx_4004_);
v___x_4172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1));
v___x_4173_ = l_Lean_Syntax_getOptional_x3f(v___x_4167_);
lean_dec(v___x_4167_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v___x_4174_; 
v___x_4174_ = lean_box(0);
v___y_4093_ = v___y_4125_;
v___y_4094_ = v___y_4124_;
v___y_4095_ = v___y_4122_;
v___y_4096_ = v___y_4127_;
v___y_4097_ = v___x_4172_;
v___y_4098_ = v_loc_x3f_4121_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v_arr_4169_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4123_;
v___y_4103_ = v___x_4168_;
v___y_4104_ = v___x_4171_;
v___y_4105_ = v___y_4128_;
v___y_4106_ = v___x_4174_;
goto v___jp_4092_;
}
else
{
lean_object* v_val_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_val_4175_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4173_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_val_4175_);
lean_dec(v___x_4173_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_val_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
v___y_4093_ = v___y_4125_;
v___y_4094_ = v___y_4124_;
v___y_4095_ = v___y_4122_;
v___y_4096_ = v___y_4127_;
v___y_4097_ = v___x_4172_;
v___y_4098_ = v_loc_x3f_4121_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v_arr_4169_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4123_;
v___y_4103_ = v___x_4168_;
v___y_4104_ = v___x_4171_;
v___y_4105_ = v___y_4128_;
v___y_4106_ = v___x_4180_;
goto v___jp_4092_;
}
}
}
}
}
}
v___jp_4016_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_inc_ref(v___y_4037_);
v___x_4039_ = l_Array_append___redArg(v___y_4037_, v___y_4038_);
lean_dec_ref(v___y_4038_);
lean_inc_n(v___y_4026_, 2);
lean_inc_n(v___y_4028_, 9);
v___x_4040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4040_, 0, v___y_4028_);
lean_ctor_set(v___x_4040_, 1, v___y_4026_);
lean_ctor_set(v___x_4040_, 2, v___x_4039_);
lean_inc(v___y_4025_);
v___x_4041_ = l_Lean_Syntax_node3(v___y_4028_, v___y_4025_, v___y_4018_, v___x_4040_, v___y_4034_);
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__2));
v___x_4043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___y_4028_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0));
v___x_4045_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11));
v___x_4046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___y_4028_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
v___x_4047_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21));
v___x_4048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___y_4028_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
v___x_4049_ = l_Lean_Syntax_node3(v___y_4028_, v___x_4044_, v___x_4046_, v___y_4035_, v___x_4048_);
v___x_4050_ = l_Lean_Syntax_node3(v___y_4028_, v___y_4026_, v___x_4041_, v___x_4043_, v___x_4049_);
lean_inc(v___y_4020_);
v___x_4051_ = l_Lean_Syntax_node1(v___y_4028_, v___y_4020_, v___x_4050_);
lean_inc(v___y_4029_);
v___x_4052_ = l_Lean_Syntax_node1(v___y_4028_, v___y_4029_, v___x_4051_);
v___x_4053_ = l_Lean_Syntax_node5(v___y_4028_, v___x_4015_, v___y_4019_, v___y_4030_, v___y_4024_, v___y_4027_, v___x_4052_);
v___x_4054_ = l_Lean_Elab_Tactic_evalTactic(v___x_4053_, v___y_4022_, v___y_4033_, v___y_4021_, v___y_4017_, v___y_4031_, v___y_4023_, v___y_4036_, v___y_4032_);
return v___x_4054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___boxed(lean_object* v_stx_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_Elab_Tactic_Conv_evalConv(v_stx_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1(){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4210_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4211_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__1));
v___x_4212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1));
v___x_4213_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConv___boxed), 10, 0);
v___x_4214_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4210_, v___x_4211_, v___x_4212_, v___x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___boxed(lean_object* v_a_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3(){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4243_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1));
v___x_4244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6));
v___x_4245_ = l_Lean_addBuiltinDeclarationRanges(v___x_4243_, v___x_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___boxed(lean_object* v_a_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst(lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Lean_Elab_Tactic_evalFirst(v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___boxed(lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Elab_Tactic_Conv_evalFirst(v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_);
lean_dec(v_a_4267_);
lean_dec_ref(v_a_4266_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
lean_dec(v_a_4263_);
lean_dec_ref(v_a_4262_);
lean_dec(v_a_4261_);
lean_dec_ref(v_a_4260_);
lean_dec(v_a_4259_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1(){
_start:
{
lean_object* v___f_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___f_4286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0));
v___x_4287_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2));
v___x_4289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4));
v___x_4290_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4287_, v___x_4288_, v___x_4289_, v___f_4286_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___boxed(lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3(){
_start:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4));
v___x_4320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6));
v___x_4321_ = l_Lean_addBuiltinDeclarationRanges(v___x_4319_, v___x_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___boxed(lean_object* v_a_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
return v_res_4323_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BuiltinTactic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BuiltinTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BuiltinTactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BuiltinTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
