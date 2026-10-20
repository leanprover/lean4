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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Array_mkArray0___redArg();
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
v___x_171_ = lean_st_ref_put(v___y_152_, v___x_170_);
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
lean_object* v_head_233_; lean_object* v_tail_234_; lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; 
v_head_233_ = lean_ctor_get(v_as_x27_225_, 0);
v_tail_234_ = lean_ctor_get(v_as_x27_225_, 1);
v___x_235_ = lean_box(0);
v___x_236_ = 1;
v___x_237_ = l_Lean_Meta_saveState___redArg(v___y_228_, v___y_230_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
lean_inc(v_head_233_);
v___x_239_ = l_Lean_MVarId_refl(v_head_233_, v___x_236_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_dec_ref_known(v___x_239_, 1);
lean_dec(v_a_238_);
v_as_x27_225_ = v_tail_234_;
v_b_226_ = v___x_235_;
goto _start;
}
else
{
lean_object* v_a_241_; uint8_t v___x_242_; 
v_a_241_ = lean_ctor_get(v___x_239_, 0);
v___x_242_ = l_Lean_Exception_isInterrupt(v_a_241_);
if (v___x_242_ == 0)
{
uint8_t v___x_243_; 
lean_inc(v_a_241_);
v___x_243_ = l_Lean_Exception_isRuntime(v_a_241_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
lean_dec_ref_known(v___x_239_, 1);
v___x_244_ = l_Lean_Meta_SavedState_restore___redArg(v_a_238_, v___y_228_, v___y_230_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_245_; 
lean_dec_ref_known(v___x_244_, 1);
v___x_245_ = l_Lean_Meta_saveState___redArg(v___y_228_, v___y_230_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
lean_inc(v_head_233_);
v___x_247_ = l_Lean_MVarId_inferInstance(v_head_233_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_dec_ref_known(v___x_247_, 1);
lean_dec(v_a_246_);
v_as_x27_225_ = v_tail_234_;
v_b_226_ = v___x_235_;
goto _start;
}
else
{
lean_object* v_a_249_; uint8_t v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_247_, 0);
v___x_250_ = l_Lean_Exception_isInterrupt(v_a_249_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
lean_inc(v_a_249_);
v___x_251_ = l_Lean_Exception_isRuntime(v_a_249_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref_known(v___x_247_, 1);
v___x_252_ = l_Lean_Meta_SavedState_restore___redArg(v_a_246_, v___y_228_, v___y_230_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_dec_ref_known(v___x_252_, 1);
v_as_x27_225_ = v_tail_234_;
v_b_226_ = v___x_235_;
goto _start;
}
else
{
return v___x_252_;
}
}
else
{
lean_dec(v_a_246_);
return v___x_247_;
}
}
else
{
lean_dec(v_a_246_);
return v___x_247_;
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_a_254_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_245_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_245_);
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
return v___x_244_;
}
}
else
{
lean_dec(v_a_238_);
return v___x_239_;
}
}
else
{
lean_dec(v_a_238_);
return v___x_239_;
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_237_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_237_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg___boxed(lean_object* v_as_x27_270_, lean_object* v_b_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_as_x27_270_, v_b_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v_as_x27_270_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(lean_object* v_msgData_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; lean_object* v_env_285_; uint8_t v___x_286_; lean_object* v_env_287_; lean_object* v___x_288_; lean_object* v_toCold_289_; lean_object* v_mctx_290_; lean_object* v_lctx_291_; lean_object* v_options_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_284_ = lean_st_ref_get(v___y_282_);
v_env_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc_ref(v_env_285_);
lean_dec(v___x_284_);
v___x_286_ = 0;
v_env_287_ = l_Lean_Environment_setRecordingDeps(v_env_285_, v___x_286_);
v___x_288_ = lean_st_ref_get(v___y_280_);
v_toCold_289_ = lean_ctor_get(v___y_281_, 0);
v_mctx_290_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_mctx_290_);
lean_dec(v___x_288_);
v_lctx_291_ = lean_ctor_get(v___y_279_, 2);
v_options_292_ = lean_ctor_get(v_toCold_289_, 2);
lean_inc_ref(v_options_292_);
lean_inc_ref(v_lctx_291_);
v___x_293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_293_, 0, v_env_287_);
lean_ctor_set(v___x_293_, 1, v_mctx_290_);
lean_ctor_set(v___x_293_, 2, v_lctx_291_);
lean_ctor_set(v___x_293_, 3, v_options_292_);
v___x_294_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_msgData_278_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2___boxed(lean_object* v_msgData_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msgData_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_ref_309_; lean_object* v___x_310_; lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
v_ref_309_ = lean_ctor_get(v___y_306_, 2);
v___x_310_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msg_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_319_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_inc(v_ref_309_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v_ref_309_);
lean_ctor_set(v___x_315_, 1, v_a_311_);
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 1);
lean_ctor_set(v___x_313_, 0, v___x_315_);
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg___boxed(lean_object* v_msg_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v_msg_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_convert___closed__1(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_convert___closed__0));
v___x_329_ = l_Lean_stringToMessageData(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert(lean_object* v_lhs_330_, lean_object* v_conv_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_box(0);
v___x_342_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_lhs_330_, v___x_341_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_431_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v_fst_344_ = lean_ctor_get(v_a_343_, 0);
v_snd_345_ = lean_ctor_get(v_a_343_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_343_);
if (v_isSharedCheck_431_ == 0)
{
v___x_347_ = v_a_343_;
v_isShared_348_ = v_isSharedCheck_431_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snd_345_);
lean_inc(v_fst_344_);
lean_dec(v_a_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_431_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_333_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v_a_352_; lean_object* v___y_371_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v___x_395_ = l_Lean_Expr_mvarId_x21(v_snd_345_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_397_, v_a_333_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; 
lean_dec_ref_known(v___x_398_, 1);
lean_inc(v_a_339_);
lean_inc_ref(v_a_338_);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
v___x_399_ = lean_apply_9(v_conv_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, lean_box(0));
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v___x_400_; 
lean_dec_ref_known(v___x_399_, 1);
v___x_400_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_333_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v___x_402_ = lean_box(0);
v___x_403_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_a_401_, v___x_402_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_401_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_404_; 
lean_dec_ref_known(v___x_403_, 1);
v___x_404_ = l_Lean_Elab_Tactic_pruneSolvedGoals(v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; 
lean_dec_ref_known(v___x_404_, 1);
v___x_405_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_333_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; uint8_t v___x_407_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = l_List_isEmpty___redArg(v_a_406_);
lean_dec(v_a_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
v___x_408_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_333_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_a_414_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v___x_410_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_convert___closed__1, &l_Lean_Elab_Tactic_Conv_convert___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_convert___closed__1);
v___x_411_ = l_Lean_Elab_goalsToMessageData(v_a_409_);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v___x_412_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref(v___x_413_);
v_a_352_ = v_a_414_;
goto v___jp_351_;
}
else
{
lean_object* v_a_415_; 
v_a_415_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_408_, 1);
v_a_352_ = v_a_415_;
goto v___jp_351_;
}
}
else
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Elab_Tactic_Conv_convert___lam__0(v___x_402_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
v___y_371_ = v___x_416_;
goto v___jp_370_;
}
}
else
{
lean_object* v_a_417_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
v_a_417_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_405_, 1);
v_a_352_ = v_a_417_;
goto v___jp_351_;
}
}
else
{
lean_object* v_a_418_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
v_a_418_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_404_, 1);
v_a_352_ = v_a_418_;
goto v___jp_351_;
}
}
else
{
lean_object* v_a_419_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
v_a_419_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_403_, 1);
v_a_352_ = v_a_419_;
goto v___jp_351_;
}
}
else
{
lean_object* v_a_420_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
v_a_420_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_400_, 1);
v_a_352_ = v_a_420_;
goto v___jp_351_;
}
}
else
{
lean_object* v_a_421_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
v_a_421_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_399_, 1);
v_a_352_ = v_a_421_;
goto v___jp_351_;
}
}
else
{
lean_object* v_a_422_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
lean_dec_ref(v_conv_331_);
v_a_422_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_398_, 1);
v_a_352_ = v_a_422_;
goto v___jp_351_;
}
v___jp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_350_, v_a_333_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v___x_353_, 0);
lean_dec(v_unused_361_);
v___x_355_ = v___x_353_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_dec(v___x_353_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 1);
lean_ctor_set(v___x_355_, 0, v_a_352_);
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_352_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v_a_352_);
v_a_362_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_353_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_353_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
v___jp_370_:
{
lean_object* v___x_372_; 
lean_dec_ref(v___y_371_);
v___x_372_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_350_, v_a_333_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_386_; 
lean_dec_ref_known(v___x_372_, 1);
v___x_373_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_fst_344_, v_a_337_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref(v___x_373_);
v___x_375_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convert_spec__0___redArg(v_snd_345_, v_a_337_);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_386_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_386_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_386_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_a_376_);
lean_ctor_set(v___x_347_, 0, v_a_374_);
v___x_381_ = v___x_347_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_374_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_a_376_);
v___x_381_ = v_reuseFailAlloc_385_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_383_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_381_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
v_a_387_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_372_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_372_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_del_object(v___x_347_);
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
lean_dec_ref(v_conv_331_);
v_a_423_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_349_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_349_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
lean_dec_ref(v_conv_331_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convert___boxed(lean_object* v_lhs_432_, lean_object* v_conv_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Elab_Tactic_Conv_convert(v_lhs_432_, v_conv_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(lean_object* v_as_444_, lean_object* v_as_x27_445_, lean_object* v_b_446_, lean_object* v_a_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___redArg(v_as_x27_445_, v_b_446_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1___boxed(lean_object* v_as_458_, lean_object* v_as_x27_459_, lean_object* v_b_460_, lean_object* v_a_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Conv_convert_spec__1(v_as_458_, v_as_x27_459_, v_b_460_, v_a_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v_as_x27_459_);
lean_dec(v_as_458_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(lean_object* v_00_u03b1_472_, lean_object* v_msg_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___redArg(v_msg_473_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2___boxed(lean_object* v_00_u03b1_484_, lean_object* v_msg_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2(v_00_u03b1_484_, v_msg_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(lean_object* v_mvarId_496_, lean_object* v_x_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_496_, v_x_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_503_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_503_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg___boxed(lean_object* v_mvarId_520_, lean_object* v_x_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_mvarId_520_, v_x_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(lean_object* v_00_u03b1_528_, lean_object* v_mvarId_529_, lean_object* v_x_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_mvarId_529_, v_x_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___boxed(lean_object* v_00_u03b1_537_, lean_object* v_mvarId_538_, lean_object* v_x_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1(v_00_u03b1_537_, v_mvarId_538_, v_x_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_ref_552_; lean_object* v___x_553_; lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_ref_552_ = lean_ctor_get(v___y_549_, 2);
v___x_553_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_convert_spec__2_spec__2(v_msg_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_562_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
lean_inc(v_ref_552_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v_ref_552_);
lean_ctor_set(v___x_558_, 1, v_a_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 1);
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg___boxed(lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v_msg_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
return v_res_569_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__0));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(lean_object* v_mvarId_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_MVarId_getType(v_mvarId_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = l_Lean_Meta_matchEq_x3f(v_a_580_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_593_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_593_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_593_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_593_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
if (lean_obj_tag(v_a_582_) == 1)
{
lean_object* v_val_586_; lean_object* v_snd_587_; lean_object* v___x_589_; 
v_val_586_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v_a_582_, 1);
v_snd_587_ = lean_ctor_get(v_val_586_, 1);
lean_inc(v_snd_587_);
lean_dec(v_val_586_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v_snd_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_snd_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_del_object(v___x_584_);
lean_dec(v_a_582_);
v___x_591_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___closed__1);
v___x_592_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v___x_591_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
return v___x_592_;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_581_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_581_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_a_602_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_579_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_579_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed(lean_object* v_mvarId_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0(v_mvarId_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore(lean_object* v_mvarId_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___f_623_; lean_object* v___x_624_; 
lean_inc(v_mvarId_617_);
v___f_623_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_getLhsRhsCore___lam__0___boxed), 6, 1);
lean_closure_set(v___f_623_, 0, v_mvarId_617_);
v___x_624_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_mvarId_617_, v___f_623_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore___boxed(lean_object* v_mvarId_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(lean_object* v_00_u03b1_632_, lean_object* v_msg_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___redArg(v_msg_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0___boxed(lean_object* v_00_u03b1_640_, lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__0(v_00_u03b1_640_, v_msg_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_a_655_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
return v___x_656_;
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
v_a_657_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_654_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_654_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg___boxed(lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs(lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_673_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___boxed(lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Elab_Tactic_Conv_getLhsRhs(v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_fst_703_; lean_object* v___x_705_; 
v_fst_703_ = lean_ctor_get(v_a_699_, 0);
lean_inc(v_fst_703_);
lean_dec(v_a_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v_fst_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_fst_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
v_a_708_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_698_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_698_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg___boxed(lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v_a_724_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getLhs___boxed(lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Elab_Tactic_Conv_getLhs(v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg(lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_758_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_snd_754_; lean_object* v___x_756_; 
v_snd_754_ = lean_ctor_get(v_a_750_, 1);
lean_inc(v_snd_754_);
lean_dec(v_a_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v_snd_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_snd_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_749_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_749_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___redArg___boxed(lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs(lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_775_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_getRhs___boxed(lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_Elab_Tactic_Conv_getRhs(v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_ks_798_; lean_object* v_vs_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_823_; 
v_ks_798_ = lean_ctor_get(v_x_794_, 0);
v_vs_799_ = lean_ctor_get(v_x_794_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_823_ == 0)
{
v___x_801_ = v_x_794_;
v_isShared_802_ = v_isSharedCheck_823_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_vs_799_);
lean_inc(v_ks_798_);
lean_dec(v_x_794_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_823_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_array_get_size(v_ks_798_);
v___x_804_ = lean_nat_dec_lt(v_x_795_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v_x_795_);
v___x_805_ = lean_array_push(v_ks_798_, v_x_796_);
v___x_806_ = lean_array_push(v_vs_799_, v_x_797_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_806_);
lean_ctor_set(v___x_801_, 0, v___x_805_);
v___x_808_ = v___x_801_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v_k_x27_810_; uint8_t v___x_811_; 
v_k_x27_810_ = lean_array_fget_borrowed(v_ks_798_, v_x_795_);
v___x_811_ = l_Lean_instBEqMVarId_beq(v_x_796_, v_k_x27_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_813_; 
if (v_isShared_802_ == 0)
{
v___x_813_ = v___x_801_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_ks_798_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_vs_799_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_add(v_x_795_, v___x_814_);
lean_dec(v_x_795_);
v_x_794_ = v___x_813_;
v_x_795_ = v___x_815_;
goto _start;
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_818_ = lean_array_fset(v_ks_798_, v_x_795_, v_x_796_);
v___x_819_ = lean_array_fset(v_vs_799_, v_x_795_, v_x_797_);
lean_dec(v_x_795_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_819_);
lean_ctor_set(v___x_801_, 0, v___x_818_);
v___x_821_ = v___x_801_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_824_, lean_object* v_k_825_, lean_object* v_v_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_824_, v___x_827_, v_k_825_, v_v_826_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(lean_object* v_x_830_, size_t v_x_831_, size_t v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
lean_object* v_es_835_; size_t v___x_836_; size_t v___x_837_; lean_object* v_j_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_es_835_ = lean_ctor_get(v_x_830_, 0);
v___x_836_ = ((size_t)31ULL);
v___x_837_ = lean_usize_land(v_x_831_, v___x_836_);
v_j_838_ = lean_usize_to_nat(v___x_837_);
v___x_839_ = lean_array_get_size(v_es_835_);
v___x_840_ = lean_nat_dec_lt(v_j_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_dec(v_j_838_);
lean_dec(v_x_834_);
lean_dec(v_x_833_);
return v_x_830_;
}
else
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_879_; 
lean_inc_ref(v_es_835_);
v_isSharedCheck_879_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v_x_830_, 0);
lean_dec(v_unused_880_);
v___x_842_ = v_x_830_;
v_isShared_843_ = v_isSharedCheck_879_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_x_830_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_879_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_v_844_; lean_object* v___x_845_; lean_object* v_xs_x27_846_; lean_object* v___y_848_; 
v_v_844_ = lean_array_fget(v_es_835_, v_j_838_);
v___x_845_ = lean_box(0);
v_xs_x27_846_ = lean_array_fset(v_es_835_, v_j_838_, v___x_845_);
switch(lean_obj_tag(v_v_844_))
{
case 0:
{
lean_object* v_key_853_; lean_object* v_val_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_864_; 
v_key_853_ = lean_ctor_get(v_v_844_, 0);
v_val_854_ = lean_ctor_get(v_v_844_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_v_844_);
if (v_isSharedCheck_864_ == 0)
{
v___x_856_ = v_v_844_;
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_val_854_);
lean_inc(v_key_853_);
lean_dec(v_v_844_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
uint8_t v___x_858_; 
v___x_858_ = l_Lean_instBEqMVarId_beq(v_x_833_, v_key_853_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_del_object(v___x_856_);
v___x_859_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_853_, v_val_854_, v_x_833_, v_x_834_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
v___y_848_ = v___x_860_;
goto v___jp_847_;
}
else
{
lean_object* v___x_862_; 
lean_dec(v_val_854_);
lean_dec(v_key_853_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v_x_834_);
lean_ctor_set(v___x_856_, 0, v_x_833_);
v___x_862_ = v___x_856_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_x_833_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_x_834_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
v___y_848_ = v___x_862_;
goto v___jp_847_;
}
}
}
}
case 1:
{
lean_object* v_node_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_877_; 
v_node_865_ = lean_ctor_get(v_v_844_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_v_844_);
if (v_isSharedCheck_877_ == 0)
{
v___x_867_ = v_v_844_;
v_isShared_868_ = v_isSharedCheck_877_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_node_865_);
lean_dec(v_v_844_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_877_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_869_ = ((size_t)5ULL);
v___x_870_ = lean_usize_shift_right(v_x_831_, v___x_869_);
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_add(v_x_832_, v___x_871_);
v___x_873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_node_865_, v___x_870_, v___x_872_, v_x_833_, v_x_834_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_873_);
v___x_875_ = v___x_867_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v___y_848_ = v___x_875_;
goto v___jp_847_;
}
}
}
default: 
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_x_833_);
lean_ctor_set(v___x_878_, 1, v_x_834_);
v___y_848_ = v___x_878_;
goto v___jp_847_;
}
}
v___jp_847_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_array_fset(v_xs_x27_846_, v_j_838_, v___y_848_);
lean_dec(v_j_838_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_849_);
v___x_851_ = v___x_842_;
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
}
}
else
{
lean_object* v_ks_881_; lean_object* v_vs_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_900_; 
v_ks_881_ = lean_ctor_get(v_x_830_, 0);
v_vs_882_ = lean_ctor_get(v_x_830_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_900_ == 0)
{
v___x_884_ = v_x_830_;
v_isShared_885_ = v_isSharedCheck_900_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_vs_882_);
lean_inc(v_ks_881_);
lean_dec(v_x_830_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_900_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_ks_881_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_vs_882_);
v___x_887_ = v_reuseFailAlloc_899_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v_newNode_888_; size_t v___x_889_; uint8_t v___x_890_; 
v_newNode_888_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(v___x_887_, v_x_833_, v_x_834_);
v___x_889_ = ((size_t)7ULL);
v___x_890_ = lean_usize_dec_le(v___x_889_, v_x_832_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_888_);
v___x_892_ = lean_unsigned_to_nat(4u);
v___x_893_ = lean_nat_dec_lt(v___x_891_, v___x_892_);
lean_dec(v___x_891_);
if (v___x_893_ == 0)
{
lean_object* v_ks_894_; lean_object* v_vs_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_ks_894_ = lean_ctor_get(v_newNode_888_, 0);
lean_inc_ref(v_ks_894_);
v_vs_895_ = lean_ctor_get(v_newNode_888_, 1);
lean_inc_ref(v_vs_895_);
lean_dec_ref(v_newNode_888_);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_898_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_x_832_, v_ks_894_, v_vs_895_, v___x_896_, v___x_897_);
lean_dec_ref(v_vs_895_);
lean_dec_ref(v_ks_894_);
return v___x_898_;
}
else
{
return v_newNode_888_;
}
}
else
{
return v_newNode_888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_901_, lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_i_904_, lean_object* v_entries_905_){
_start:
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_array_get_size(v_keys_902_);
v___x_907_ = lean_nat_dec_lt(v_i_904_, v___x_906_);
if (v___x_907_ == 0)
{
lean_dec(v_i_904_);
return v_entries_905_;
}
else
{
lean_object* v_k_908_; lean_object* v_v_909_; uint64_t v___x_910_; size_t v_h_911_; size_t v___x_912_; lean_object* v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v_h_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_k_908_ = lean_array_fget_borrowed(v_keys_902_, v_i_904_);
v_v_909_ = lean_array_fget_borrowed(v_vals_903_, v_i_904_);
v___x_910_ = l_Lean_instHashableMVarId_hash(v_k_908_);
v_h_911_ = lean_uint64_to_usize(v___x_910_);
v___x_912_ = ((size_t)5ULL);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_sub(v_depth_901_, v___x_914_);
v___x_916_ = lean_usize_mul(v___x_912_, v___x_915_);
v_h_917_ = lean_usize_shift_right(v_h_911_, v___x_916_);
v___x_918_ = lean_nat_add(v_i_904_, v___x_913_);
lean_dec(v_i_904_);
lean_inc(v_v_909_);
lean_inc(v_k_908_);
v___x_919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_entries_905_, v_h_917_, v_depth_901_, v_k_908_, v_v_909_);
v_i_904_ = v___x_918_;
v_entries_905_ = v___x_919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_921_, lean_object* v_keys_922_, lean_object* v_vals_923_, lean_object* v_i_924_, lean_object* v_entries_925_){
_start:
{
size_t v_depth_boxed_926_; lean_object* v_res_927_; 
v_depth_boxed_926_ = lean_unbox_usize(v_depth_921_);
lean_dec(v_depth_921_);
v_res_927_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_926_, v_keys_922_, v_vals_923_, v_i_924_, v_entries_925_);
lean_dec_ref(v_vals_923_);
lean_dec_ref(v_keys_922_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
size_t v_x_1701__boxed_933_; size_t v_x_1702__boxed_934_; lean_object* v_res_935_; 
v_x_1701__boxed_933_ = lean_unbox_usize(v_x_929_);
lean_dec(v_x_929_);
v_x_1702__boxed_934_ = lean_unbox_usize(v_x_930_);
lean_dec(v_x_930_);
v_res_935_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_928_, v_x_1701__boxed_933_, v_x_1702__boxed_934_, v_x_931_, v_x_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
uint64_t v___x_939_; size_t v___x_940_; size_t v___x_941_; lean_object* v___x_942_; 
v___x_939_ = l_Lean_instHashableMVarId_hash(v_x_937_);
v___x_940_ = lean_uint64_to_usize(v___x_939_);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_936_, v___x_940_, v___x_941_, v_x_937_, v_x_938_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(lean_object* v_mvarId_943_, lean_object* v_val_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; lean_object* v_mctx_948_; lean_object* v_cache_949_; lean_object* v_zetaDeltaFVarIds_950_; lean_object* v_postponed_951_; lean_object* v_diag_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_982_; 
v___x_947_ = lean_st_ref_take(v___y_945_);
v_mctx_948_ = lean_ctor_get(v___x_947_, 0);
v_cache_949_ = lean_ctor_get(v___x_947_, 1);
v_zetaDeltaFVarIds_950_ = lean_ctor_get(v___x_947_, 2);
v_postponed_951_ = lean_ctor_get(v___x_947_, 3);
v_diag_952_ = lean_ctor_get(v___x_947_, 4);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_982_ == 0)
{
v___x_954_ = v___x_947_;
v_isShared_955_ = v_isSharedCheck_982_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_diag_952_);
lean_inc(v_postponed_951_);
lean_inc(v_zetaDeltaFVarIds_950_);
lean_inc(v_cache_949_);
lean_inc(v_mctx_948_);
lean_dec(v___x_947_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_982_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_depth_956_; lean_object* v_levelAssignDepth_957_; lean_object* v_lmvarCounter_958_; lean_object* v_mvarCounter_959_; lean_object* v_lDecls_960_; lean_object* v_decls_961_; lean_object* v_userNames_962_; lean_object* v_lAssignment_963_; lean_object* v_eAssignment_964_; lean_object* v_dAssignment_965_; lean_object* v_instanceTypedMVars_966_; lean_object* v_synthNormMemo_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_981_; 
v_depth_956_ = lean_ctor_get(v_mctx_948_, 0);
v_levelAssignDepth_957_ = lean_ctor_get(v_mctx_948_, 1);
v_lmvarCounter_958_ = lean_ctor_get(v_mctx_948_, 2);
v_mvarCounter_959_ = lean_ctor_get(v_mctx_948_, 3);
v_lDecls_960_ = lean_ctor_get(v_mctx_948_, 4);
v_decls_961_ = lean_ctor_get(v_mctx_948_, 5);
v_userNames_962_ = lean_ctor_get(v_mctx_948_, 6);
v_lAssignment_963_ = lean_ctor_get(v_mctx_948_, 7);
v_eAssignment_964_ = lean_ctor_get(v_mctx_948_, 8);
v_dAssignment_965_ = lean_ctor_get(v_mctx_948_, 9);
v_instanceTypedMVars_966_ = lean_ctor_get(v_mctx_948_, 10);
v_synthNormMemo_967_ = lean_ctor_get(v_mctx_948_, 11);
v_isSharedCheck_981_ = !lean_is_exclusive(v_mctx_948_);
if (v_isSharedCheck_981_ == 0)
{
v___x_969_ = v_mctx_948_;
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_synthNormMemo_967_);
lean_inc(v_instanceTypedMVars_966_);
lean_inc(v_dAssignment_965_);
lean_inc(v_eAssignment_964_);
lean_inc(v_lAssignment_963_);
lean_inc(v_userNames_962_);
lean_inc(v_decls_961_);
lean_inc(v_lDecls_960_);
lean_inc(v_mvarCounter_959_);
lean_inc(v_lmvarCounter_958_);
lean_inc(v_levelAssignDepth_957_);
lean_inc(v_depth_956_);
lean_dec(v_mctx_948_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_971_ = lean_box(0);
v___x_972_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_eAssignment_964_, v_mvarId_943_, v_val_944_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 8, v___x_972_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_depth_956_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_levelAssignDepth_957_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_lmvarCounter_958_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_mvarCounter_959_);
lean_ctor_set(v_reuseFailAlloc_980_, 4, v_lDecls_960_);
lean_ctor_set(v_reuseFailAlloc_980_, 5, v_decls_961_);
lean_ctor_set(v_reuseFailAlloc_980_, 6, v_userNames_962_);
lean_ctor_set(v_reuseFailAlloc_980_, 7, v_lAssignment_963_);
lean_ctor_set(v_reuseFailAlloc_980_, 8, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_980_, 9, v_dAssignment_965_);
lean_ctor_set(v_reuseFailAlloc_980_, 10, v_instanceTypedMVars_966_);
lean_ctor_set(v_reuseFailAlloc_980_, 11, v_synthNormMemo_967_);
v___x_974_ = v_reuseFailAlloc_980_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_974_);
v___x_976_ = v___x_954_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_cache_949_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_zetaDeltaFVarIds_950_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_postponed_951_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_diag_952_);
v___x_976_ = v_reuseFailAlloc_979_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_st_ref_put(v___y_945_, v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_971_);
return v___x_978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg___boxed(lean_object* v_mvarId_983_, lean_object* v_val_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_mvarId_983_, v_val_984_, v___y_985_);
lean_dec(v___y_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object* v_lhs_x27_988_, lean_object* v_h_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_991_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_991_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = l_Lean_Meta_mkEq(v_lhs_x27_988_, v_a_1002_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
lean_inc(v_a_1000_);
v___x_1005_ = l_Lean_MVarId_getTag(v_a_1000_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = l_Lean_mkLHSGoalRaw(v_a_1004_);
v___x_1008_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1007_, v_a_1006_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_n(v_a_1009_, 2);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = l_Lean_Meta_mkEqTrans(v_h_989_, v_a_1009_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_a_1000_, v_a_1011_, v_a_995_);
lean_dec_ref(v___x_1012_);
v___x_1013_ = l_Lean_Expr_mvarId_x21(v_a_1009_);
lean_dec(v_a_1009_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1015_, v_a_991_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_1016_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v_a_1009_);
lean_dec(v_a_1000_);
v_a_1017_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1010_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1010_);
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
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_a_1000_);
lean_dec_ref(v_h_989_);
v_a_1025_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1008_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1008_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_a_1004_);
lean_dec(v_a_1000_);
lean_dec_ref(v_h_989_);
v_a_1033_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1005_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1005_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_1000_);
lean_dec_ref(v_h_989_);
v_a_1041_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1003_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1003_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_a_1000_);
lean_dec_ref(v_h_989_);
lean_dec_ref(v_lhs_x27_988_);
v_a_1049_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1001_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1001_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_h_989_);
lean_dec_ref(v_lhs_x27_988_);
v_a_1057_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_999_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_999_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_updateLhs___boxed(lean_object* v_lhs_x27_1065_, lean_object* v_h_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_lhs_x27_1065_, v_h_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(lean_object* v_mvarId_1077_, lean_object* v_val_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___redArg(v_mvarId_1077_, v_val_1078_, v___y_1084_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0___boxed(lean_object* v_mvarId_1089_, lean_object* v_val_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0(v_mvarId_1089_, v_val_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0(lean_object* v_00_u03b2_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0___redArg(v_x_1102_, v_x_1103_, v_x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1106_, lean_object* v_x_1107_, size_t v_x_1108_, size_t v_x_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___redArg(v_x_1107_, v_x_1108_, v_x_1109_, v_x_1110_, v_x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
size_t v_x_2085__boxed_1119_; size_t v_x_2086__boxed_1120_; lean_object* v_res_1121_; 
v_x_2085__boxed_1119_ = lean_unbox_usize(v_x_1115_);
lean_dec(v_x_1115_);
v_x_2086__boxed_1120_ = lean_unbox_usize(v_x_1116_);
lean_dec(v_x_1116_);
v_res_1121_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1(v_00_u03b2_1113_, v_x_1114_, v_x_2085__boxed_1119_, v_x_2086__boxed_1120_, v_x_1117_, v_x_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1122_, lean_object* v_n_1123_, lean_object* v_k_1124_, lean_object* v_v_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1123_, v_k_1124_, v_v_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1127_, size_t v_depth_1128_, lean_object* v_keys_1129_, lean_object* v_vals_1130_, lean_object* v_heq_1131_, lean_object* v_i_1132_, lean_object* v_entries_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1128_, v_keys_1129_, v_vals_1130_, v_i_1132_, v_entries_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1135_, lean_object* v_depth_1136_, lean_object* v_keys_1137_, lean_object* v_vals_1138_, lean_object* v_heq_1139_, lean_object* v_i_1140_, lean_object* v_entries_1141_){
_start:
{
size_t v_depth_boxed_1142_; lean_object* v_res_1143_; 
v_depth_boxed_1142_ = lean_unbox_usize(v_depth_1136_);
lean_dec(v_depth_1136_);
v_res_1143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1135_, v_depth_boxed_1142_, v_keys_1137_, v_vals_1138_, v_heq_1139_, v_i_1140_, v_entries_1141_);
lean_dec_ref(v_vals_1138_);
lean_dec_ref(v_keys_1137_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_updateLhs_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1145_, v_x_1146_, v_x_1147_, v_x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(lean_object* v_lhs_x27_1150_, lean_object* v_a_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1153_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = l_Lean_Meta_mkEq(v_lhs_x27_1150_, v_a_1151_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = l_Lean_mkLHSGoalRaw(v_a_1164_);
v___x_1166_ = l_Lean_MVarId_replaceTargetDefEq(v_a_1162_, v___x_1165_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_a_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1169_, v___y_1153_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1170_;
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1166_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1166_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_a_1162_);
v_a_1179_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1163_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1163_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_lhs_x27_1150_);
v_a_1187_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1161_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1161_);
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
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed(lean_object* v_lhs_x27_1195_, lean_object* v_a_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Elab_Tactic_Conv_changeLhs___lam__0(v_lhs_x27_1195_, v_a_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object* v_lhs_x27_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v_a_1209_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_changeLhs___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1219_, 0, v_lhs_x27_1207_);
lean_closure_set(v___f_1219_, 1, v_a_1218_);
v___x_1220_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1219_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
return v___x_1220_;
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_lhs_x27_1207_);
v_a_1221_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1217_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1217_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_changeLhs___boxed(lean_object* v_lhs_x27_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_lhs_x27_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1241_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
v___x_1251_ = lean_whnf(v_a_1250_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1252_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
v_a_1254_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1251_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
v_a_1262_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1249_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1249_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0___boxed(lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___lam__0(v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v___f_1290_; lean_object* v___x_1291_; 
v___f_1290_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___closed__0));
v___x_1291_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1290_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___redArg___boxed(lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf(lean_object* v_x_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Elab_Tactic_Conv_evalWhnf___redArg(v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalWhnf___boxed(lean_object* v_x_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Elab_Tactic_Conv_evalWhnf(v_x_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_x_1313_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1(){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1344_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__5));
v___x_1346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8));
v___x_1347_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalWhnf___boxed), 10, 0);
v___x_1348_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1344_, v___x_1345_, v___x_1346_, v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___boxed(lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1();
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3(){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf__1___closed__8));
v___x_1378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___closed__6));
v___x_1379_ = l_Lean_addBuiltinDeclarationRanges(v___x_1377_, v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3___boxed(lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalWhnf___regBuiltin_Lean_Elab_Tactic_Conv_evalWhnf_declRange__3();
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1383_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = 1;
v___x_1394_ = l_Lean_Meta_reduce(v_a_1392_, v___x_1393_, v___x_1393_, v___x_1393_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1395_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
return v___x_1396_;
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1394_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1394_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1391_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1391_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0___boxed(lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg___lam__0(v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg(lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___f_1433_; lean_object* v___x_1434_; 
v___f_1433_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalReduce___redArg___closed__0));
v___x_1434_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1433_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___redArg___boxed(lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce(lean_object* v_x_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Elab_Tactic_Conv_evalReduce___redArg(v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalReduce___boxed(lean_object* v_x_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Elab_Tactic_Conv_evalReduce(v_x_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_x_1456_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1(){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1482_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__1));
v___x_1484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3));
v___x_1485_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalReduce___boxed), 10, 0);
v___x_1486_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1482_, v___x_1483_, v___x_1484_, v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___boxed(lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1();
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3(){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce__1___closed__3));
v___x_1516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___closed__6));
v___x_1517_ = l_Lean_addBuiltinDeclarationRanges(v___x_1515_, v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3___boxed(lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalReduce___regBuiltin_Lean_Elab_Tactic_Conv_evalReduce_declRange__3();
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1521_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = 1;
v___x_1532_ = l_Lean_Meta_zetaReduce(v_a_1530_, v___x_1531_, v___x_1531_, v___x_1531_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_1533_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v___x_1534_;
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1532_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1532_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1529_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1529_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0___boxed(lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg___lam__0(v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg(lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___f_1571_; lean_object* v___x_1572_; 
v___f_1571_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalZeta___redArg___closed__0));
v___x_1572_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1571_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___redArg___boxed(lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta(lean_object* v_x_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Elab_Tactic_Conv_evalZeta___redArg(v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalZeta___boxed(lean_object* v_x_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Elab_Tactic_Conv_evalZeta(v_x_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_x_1594_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1(){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1620_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__1));
v___x_1622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3));
v___x_1623_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalZeta___boxed), 10, 0);
v___x_1624_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1620_, v___x_1621_, v___x_1622_, v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___boxed(lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1();
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3(){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta__1___closed__3));
v___x_1654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___closed__6));
v___x_1655_ = l_Lean_addBuiltinDeclarationRanges(v___x_1653_, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3___boxed(lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalZeta___regBuiltin_Lean_Elab_Tactic_Conv_evalZeta_declRange__3();
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(lean_object* v_e_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = l_Lean_Expr_hasMVar(v_e_1658_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_e_1658_);
return v___x_1662_;
}
else
{
lean_object* v___x_1663_; lean_object* v_mctx_1664_; lean_object* v___x_1665_; lean_object* v_fst_1666_; lean_object* v_snd_1667_; lean_object* v___x_1668_; lean_object* v_cache_1669_; lean_object* v_zetaDeltaFVarIds_1670_; lean_object* v_postponed_1671_; lean_object* v_diag_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1681_; 
v___x_1663_ = lean_st_ref_get(v___y_1659_);
v_mctx_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_ref(v_mctx_1664_);
lean_dec(v___x_1663_);
v___x_1665_ = l_Lean_instantiateMVarsCore(v_mctx_1664_, v_e_1658_);
v_fst_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_fst_1666_);
v_snd_1667_ = lean_ctor_get(v___x_1665_, 1);
lean_inc(v_snd_1667_);
lean_dec_ref(v___x_1665_);
v___x_1668_ = lean_st_ref_take(v___y_1659_);
v_cache_1669_ = lean_ctor_get(v___x_1668_, 1);
v_zetaDeltaFVarIds_1670_ = lean_ctor_get(v___x_1668_, 2);
v_postponed_1671_ = lean_ctor_get(v___x_1668_, 3);
v_diag_1672_ = lean_ctor_get(v___x_1668_, 4);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; 
v_unused_1682_ = lean_ctor_get(v___x_1668_, 0);
lean_dec(v_unused_1682_);
v___x_1674_ = v___x_1668_;
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_diag_1672_);
lean_inc(v_postponed_1671_);
lean_inc(v_zetaDeltaFVarIds_1670_);
lean_inc(v_cache_1669_);
lean_dec(v___x_1668_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v_snd_1667_);
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_snd_1667_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_cache_1669_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v_zetaDeltaFVarIds_1670_);
lean_ctor_set(v_reuseFailAlloc_1680_, 3, v_postponed_1671_);
lean_ctor_set(v_reuseFailAlloc_1680_, 4, v_diag_1672_);
v___x_1677_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_st_ref_put(v___y_1659_, v___x_1677_);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_fst_1666_);
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg___boxed(lean_object* v_e_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_e_1683_, v___y_1684_);
lean_dec(v___y_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(lean_object* v_e_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_e_1687_, v___y_1689_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___boxed(lean_object* v_e_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0(v_e_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear(lean_object* v_mvarId_1701_, lean_object* v_fvarId_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1708_; 
lean_inc(v_mvarId_1701_);
v___x_1708_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1701_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v_fst_1710_; lean_object* v_snd_1711_; lean_object* v___x_1712_; lean_object* v_a_1713_; uint8_t v___x_1714_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v_fst_1710_ = lean_ctor_get(v_a_1709_, 0);
lean_inc(v_fst_1710_);
v_snd_1711_ = lean_ctor_get(v_a_1709_, 1);
lean_inc(v_snd_1711_);
lean_dec(v_a_1709_);
v___x_1712_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_convClear_spec__0___redArg(v_snd_1711_, v_a_1704_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v___x_1712_);
v___x_1714_ = l_Lean_Expr_isMVar(v_a_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec(v_a_1713_);
lean_dec(v_fst_1710_);
v___x_1715_ = l_Lean_MVarId_clear(v_mvarId_1701_, v_fvarId_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = l_Lean_Expr_mvarId_x21(v_a_1713_);
lean_dec(v_a_1713_);
lean_inc(v___x_1716_);
v___x_1717_ = l_Lean_MVarId_getKind(v___x_1716_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
lean_inc(v_fvarId_1702_);
v___x_1719_ = l_Lean_MVarId_clear(v___x_1716_, v_fvarId_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc_n(v_a_1720_, 2);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = lean_unbox(v_a_1718_);
lean_dec(v_a_1718_);
v___x_1722_ = l_Lean_MVarId_setKind___redArg(v_a_1720_, v___x_1721_, v_a_1704_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec_ref_known(v___x_1722_, 1);
v___x_1723_ = l_Lean_mkMVar(v_a_1720_);
v___x_1724_ = l_Lean_Meta_mkEq(v_fst_1710_, v___x_1723_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = l_Lean_mkLHSGoalRaw(v_a_1725_);
v___x_1727_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1701_, v___x_1726_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = l_Lean_MVarId_clear(v_a_1728_, v_fvarId_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
return v___x_1729_;
}
else
{
lean_dec(v_fvarId_1702_);
return v___x_1727_;
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_fvarId_1702_);
lean_dec(v_mvarId_1701_);
v_a_1730_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1724_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1724_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v_a_1720_);
lean_dec(v_fst_1710_);
lean_dec(v_fvarId_1702_);
lean_dec(v_mvarId_1701_);
v_a_1738_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1722_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1722_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_dec(v_a_1718_);
lean_dec(v_fst_1710_);
lean_dec(v_fvarId_1702_);
lean_dec(v_mvarId_1701_);
return v___x_1719_;
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v___x_1716_);
lean_dec(v_fst_1710_);
lean_dec(v_fvarId_1702_);
lean_dec(v_mvarId_1701_);
v_a_1746_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1717_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1717_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_fvarId_1702_);
lean_dec(v_mvarId_1701_);
v_a_1754_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1708_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1708_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_convClear___boxed(lean_object* v_mvarId_1762_, lean_object* v_fvarId_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_Elab_Tactic_Conv_convClear(v_mvarId_1762_, v_fvarId_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
return v_res_1769_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg(){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___closed__0);
v___x_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg___boxed(lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(lean_object* v_00_u03b1_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___boxed(lean_object* v_00_u03b1_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0(v_00_u03b1_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0(lean_object* v_a_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Meta_sortFVarIds___redArg(v_a_1800_, v___y_1805_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed(lean_object* v_a_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Elab_Tactic_Conv_evalClear___lam__0(v_a_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(lean_object* v_a_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1824_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1834_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v___x_1834_ = l_Lean_Elab_Tactic_Conv_convClear(v_a_1833_, v_a_1822_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_a_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1837_, v___y_1824_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
return v___x_1838_;
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
v_a_1839_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1834_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1834_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_a_1822_);
v_a_1847_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1832_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1832_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed(lean_object* v_a_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0(v_a_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(lean_object* v_as_1866_, size_t v_sz_1867_, size_t v_i_1868_, lean_object* v_b_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
uint8_t v___x_1879_; 
v___x_1879_ = lean_usize_dec_lt(v_i_1868_, v_sz_1867_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_b_1869_);
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; lean_object* v_a_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; 
v___x_1881_ = lean_box(0);
v_a_1882_ = lean_array_uget_borrowed(v_as_1866_, v_i_1868_);
lean_inc(v_a_1882_);
v___f_1883_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1883_, 0, v_a_1882_);
v___x_1884_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1883_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1884_) == 0)
{
size_t v___x_1885_; size_t v___x_1886_; 
lean_dec_ref_known(v___x_1884_, 1);
v___x_1885_ = ((size_t)1ULL);
v___x_1886_ = lean_usize_add(v_i_1868_, v___x_1885_);
v_i_1868_ = v___x_1886_;
v_b_1869_ = v___x_1881_;
goto _start;
}
else
{
return v___x_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1___boxed(lean_object* v_as_1888_, lean_object* v_sz_1889_, lean_object* v_i_1890_, lean_object* v_b_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
size_t v_sz_boxed_1901_; size_t v_i_boxed_1902_; lean_object* v_res_1903_; 
v_sz_boxed_1901_ = lean_unbox_usize(v_sz_1889_);
lean_dec(v_sz_1889_);
v_i_boxed_1902_ = lean_unbox_usize(v_i_1890_);
lean_dec(v_i_1890_);
v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v_as_1888_, v_sz_boxed_1901_, v_i_boxed_1902_, v_b_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec_ref(v_as_1888_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear(lean_object* v_stx_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalClear___closed__1));
lean_inc(v_stx_1911_);
v___x_1922_ = l_Lean_Syntax_isOfKind(v_stx_1911_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; 
lean_dec(v_stx_1911_);
v___x_1923_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_1923_;
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_hs_1926_; lean_object* v___x_1927_; 
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = l_Lean_Syntax_getArg(v_stx_1911_, v___x_1924_);
lean_dec(v_stx_1911_);
v_hs_1926_ = l_Lean_Syntax_getArgs(v___x_1925_);
lean_dec(v___x_1925_);
v___x_1927_ = l_Lean_Elab_Tactic_getFVarIds(v_hs_1926_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___f_1929_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalClear___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1929_, 0, v_a_1928_);
v___x_1930_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1929_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; size_t v_sz_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1932_ = l_Array_reverse___redArg(v_a_1931_);
v___x_1933_ = lean_box(0);
v_sz_1934_ = lean_array_size(v___x_1932_);
v___x_1935_ = ((size_t)0ULL);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalClear_spec__1(v___x_1932_, v_sz_1934_, v___x_1935_, v___x_1933_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
lean_dec_ref(v___x_1932_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v___x_1936_, 0);
lean_dec(v_unused_1944_);
v___x_1938_ = v___x_1936_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_dec(v___x_1936_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1933_);
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1933_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
return v___x_1936_;
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1930_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1930_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
v_a_1953_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1927_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1927_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalClear___boxed(lean_object* v_stx_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Elab_Tactic_Conv_evalClear(v_stx_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1(){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1980_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1981_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalClear___closed__1));
v___x_1982_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___closed__1));
v___x_1983_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalClear___boxed), 10, 0);
v___x_1984_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1980_, v___x_1981_, v___x_1982_, v___x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1___boxed(lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalClear___regBuiltin_Lean_Elab_Tactic_Conv_evalClear__1();
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(lean_object* v_as_1987_, size_t v_sz_1988_, size_t v_i_1989_, lean_object* v_b_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_a_2001_; uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_1989_, v_sz_1988_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_b_1990_);
return v___x_2006_;
}
else
{
lean_object* v_next_2007_; 
v_next_2007_ = lean_ctor_get(v_b_1990_, 0);
lean_inc(v_next_2007_);
if (lean_obj_tag(v_next_2007_) == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_b_1990_);
return v___x_2008_;
}
else
{
lean_object* v_upperBound_2009_; lean_object* v_val_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2053_; 
v_upperBound_2009_ = lean_ctor_get(v_b_1990_, 1);
v_val_2010_ = lean_ctor_get(v_next_2007_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_next_2007_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2012_ = v_next_2007_;
v_isShared_2013_ = v_isSharedCheck_2053_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_val_2010_);
lean_dec(v_next_2007_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2053_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_nat_dec_lt(v_val_2010_, v_upperBound_2009_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_del_object(v___x_2012_);
lean_dec(v_val_2010_);
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_b_1990_);
return v___x_2015_;
}
else
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2050_; 
lean_inc(v_upperBound_2009_);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_b_1990_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2051_ = lean_ctor_get(v_b_1990_, 1);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_b_1990_, 0);
lean_dec(v_unused_2052_);
v___x_2017_ = v_b_1990_;
v_isShared_2018_ = v_isSharedCheck_2050_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v_b_1990_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2050_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
v_a_2019_ = lean_array_uget_borrowed(v_as_1987_, v_i_1989_);
v___x_2020_ = lean_unsigned_to_nat(1u);
v___x_2021_ = lean_nat_add(v_val_2010_, v___x_2020_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2021_);
v___x_2023_ = v___x_2012_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2023_);
v___x_2025_ = v___x_2017_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_upperBound_2009_);
v___x_2025_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2026_ = lean_unsigned_to_nat(2u);
v___x_2027_ = lean_nat_mod(v_val_2010_, v___x_2026_);
lean_dec(v_val_2010_);
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = lean_nat_dec_eq(v___x_2027_, v___x_2028_);
lean_dec(v___x_2027_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_inc(v_a_2019_);
v___x_2030_ = l_Lean_Elab_Tactic_saveTacticInfoForToken(v_a_2019_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_dec_ref_known(v___x_2030_, 1);
v_a_2001_ = v___x_2025_;
goto v___jp_2000_;
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v___x_2025_);
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
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
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v___x_2039_; 
lean_inc(v_a_2019_);
v___x_2039_ = l_Lean_Elab_Tactic_evalTactic(v_a_2019_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_dec_ref_known(v___x_2039_, 1);
v_a_2001_ = v___x_2025_;
goto v___jp_2000_;
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v___x_2025_);
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
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
}
}
}
}
}
}
}
v___jp_2000_:
{
size_t v___x_2002_; size_t v___x_2003_; 
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1989_, v___x_2002_);
v_i_1989_ = v___x_2003_;
v_b_1990_ = v_a_2001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0___boxed(lean_object* v_as_2054_, lean_object* v_sz_2055_, lean_object* v_i_2056_, lean_object* v_b_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
size_t v_sz_boxed_2067_; size_t v_i_boxed_2068_; lean_object* v_res_2069_; 
v_sz_boxed_2067_ = lean_unbox_usize(v_sz_2055_);
lean_dec(v_sz_2055_);
v_i_boxed_2068_ = lean_unbox_usize(v_i_2056_);
lean_dec(v_i_2056_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v_as_2054_, v_sz_boxed_2067_, v_i_boxed_2068_, v_b_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec_ref(v_as_2054_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(lean_object* v_stx_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; size_t v_sz_2086_; size_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2082_ = l_Lean_Syntax_getArgs(v_stx_2072_);
v___x_2083_ = lean_array_get_size(v___x_2082_);
v___x_2084_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___closed__0));
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___x_2083_);
v_sz_2086_ = lean_array_size(v___x_2082_);
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalSepByIndentConv_spec__0(v___x_2082_, v_sz_2086_, v___x_2087_, v___x_2085_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec_ref(v___x_2082_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2096_; 
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v___x_2088_, 0);
lean_dec(v_unused_2097_);
v___x_2090_ = v___x_2088_;
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
else
{
lean_dec(v___x_2088_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2092_ = lean_box(0);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2092_);
v___x_2094_ = v___x_2090_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2088_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2088_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSepByIndentConv___boxed(lean_object* v_stx_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v_stx_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_stx_2106_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(lean_object* v_stx_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = l_Lean_Syntax_getArg(v_stx_2117_, v___x_2127_);
v___x_2129_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v___x_2128_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
lean_dec(v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed(lean_object* v_stx_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented(v_stx_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_stx_2130_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1(){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2156_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1));
v___x_2158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3));
v___x_2159_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq1Indented___boxed), 10, 0);
v___x_2160_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2156_, v___x_2157_, v___x_2158_, v___x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___boxed(lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1();
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3(){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__3));
v___x_2190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___closed__6));
v___x_2191_ = l_Lean_addBuiltinDeclarationRanges(v___x_2189_, v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3___boxed(lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented_declRange__3();
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(lean_object* v_a_2194_, lean_object* v_trees_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
lean_inc(v___y_2203_);
lean_inc_ref(v___y_2202_);
lean_inc(v___y_2201_);
lean_inc_ref(v___y_2200_);
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
v___x_2205_ = lean_apply_9(v_a_2194_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, lean_box(0));
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_a_2206_);
lean_ctor_set(v___x_2210_, 1, v_trees_2195_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v_trees_2195_);
v_a_2215_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2205_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2205_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed(lean_object* v_a_2223_, lean_object* v_trees_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0(v_a_2223_, v_trees_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(lean_object* v___x_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2235_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1___boxed(lean_object* v___x_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__1(v___x_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(lean_object* v___y_2257_, lean_object* v_mkInfoTree_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v_a_2266_, lean_object* v_a_x3f_2267_){
_start:
{
lean_object* v___x_2269_; lean_object* v_infoState_2270_; lean_object* v_trees_2271_; lean_object* v___x_2272_; 
v___x_2269_ = lean_st_ref_get(v___y_2257_);
v_infoState_2270_ = lean_ctor_get(v___x_2269_, 8);
lean_inc_ref(v_infoState_2270_);
lean_dec(v___x_2269_);
v_trees_2271_ = lean_ctor_get(v_infoState_2270_, 2);
lean_inc_ref(v_trees_2271_);
lean_dec_ref(v_infoState_2270_);
lean_inc(v___y_2257_);
lean_inc_ref(v___y_2265_);
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc(v___y_2260_);
lean_inc_ref(v___y_2259_);
v___x_2272_ = lean_apply_10(v_mkInfoTree_2258_, v_trees_2271_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2257_, lean_box(0));
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2312_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2312_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2312_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v_infoState_2278_; lean_object* v_env_2279_; lean_object* v_nextMacroScope_2280_; lean_object* v_ngen_2281_; lean_object* v_auxDeclNGen_2282_; lean_object* v_traceState_2283_; lean_object* v_cache_2284_; lean_object* v_recordedDeps_2285_; lean_object* v_messages_2286_; lean_object* v_snapshotTasks_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2311_; 
v___x_2277_ = lean_st_ref_take(v___y_2257_);
v_infoState_2278_ = lean_ctor_get(v___x_2277_, 8);
v_env_2279_ = lean_ctor_get(v___x_2277_, 0);
v_nextMacroScope_2280_ = lean_ctor_get(v___x_2277_, 1);
v_ngen_2281_ = lean_ctor_get(v___x_2277_, 2);
v_auxDeclNGen_2282_ = lean_ctor_get(v___x_2277_, 3);
v_traceState_2283_ = lean_ctor_get(v___x_2277_, 4);
v_cache_2284_ = lean_ctor_get(v___x_2277_, 5);
v_recordedDeps_2285_ = lean_ctor_get(v___x_2277_, 6);
v_messages_2286_ = lean_ctor_get(v___x_2277_, 7);
v_snapshotTasks_2287_ = lean_ctor_get(v___x_2277_, 9);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2289_ = v___x_2277_;
v_isShared_2290_ = v_isSharedCheck_2311_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_snapshotTasks_2287_);
lean_inc(v_infoState_2278_);
lean_inc(v_messages_2286_);
lean_inc(v_recordedDeps_2285_);
lean_inc(v_cache_2284_);
lean_inc(v_traceState_2283_);
lean_inc(v_auxDeclNGen_2282_);
lean_inc(v_ngen_2281_);
lean_inc(v_nextMacroScope_2280_);
lean_inc(v_env_2279_);
lean_dec(v___x_2277_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2311_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
uint8_t v_enabled_2291_; lean_object* v_assignment_2292_; lean_object* v_lazyAssignment_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2309_; 
v_enabled_2291_ = lean_ctor_get_uint8(v_infoState_2278_, sizeof(void*)*3);
v_assignment_2292_ = lean_ctor_get(v_infoState_2278_, 0);
v_lazyAssignment_2293_ = lean_ctor_get(v_infoState_2278_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_infoState_2278_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v_infoState_2278_, 2);
lean_dec(v_unused_2310_);
v___x_2295_ = v_infoState_2278_;
v_isShared_2296_ = v_isSharedCheck_2309_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_lazyAssignment_2293_);
lean_inc(v_assignment_2292_);
lean_dec(v_infoState_2278_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2309_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2297_ = lean_box(0);
v___x_2298_ = l_Lean_PersistentArray_push___redArg(v_a_2266_, v_a_2273_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 2, v___x_2298_);
v___x_2300_ = v___x_2295_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_assignment_2292_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_lazyAssignment_2293_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v___x_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2308_, sizeof(void*)*3, v_enabled_2291_);
v___x_2300_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 8, v___x_2300_);
v___x_2302_ = v___x_2289_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_env_2279_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_nextMacroScope_2280_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_ngen_2281_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_auxDeclNGen_2282_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_traceState_2283_);
lean_ctor_set(v_reuseFailAlloc_2307_, 5, v_cache_2284_);
lean_ctor_set(v_reuseFailAlloc_2307_, 6, v_recordedDeps_2285_);
lean_ctor_set(v_reuseFailAlloc_2307_, 7, v_messages_2286_);
lean_ctor_set(v_reuseFailAlloc_2307_, 8, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2307_, 9, v_snapshotTasks_2287_);
v___x_2302_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2303_ = lean_st_ref_put(v___y_2257_, v___x_2302_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2297_);
v___x_2305_ = v___x_2275_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2297_);
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
lean_dec_ref(v_a_2266_);
v_a_2313_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2272_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2272_);
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
lean_object* v___x_2345_; lean_object* v_infoState_2346_; lean_object* v_trees_2347_; lean_object* v___x_2348_; lean_object* v_infoState_2349_; lean_object* v_env_2350_; lean_object* v_nextMacroScope_2351_; lean_object* v_ngen_2352_; lean_object* v_auxDeclNGen_2353_; lean_object* v_traceState_2354_; lean_object* v_cache_2355_; lean_object* v_recordedDeps_2356_; lean_object* v_messages_2357_; lean_object* v_snapshotTasks_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2379_; 
v___x_2345_ = lean_st_ref_get(v___y_2343_);
v_infoState_2346_ = lean_ctor_get(v___x_2345_, 8);
lean_inc_ref(v_infoState_2346_);
lean_dec(v___x_2345_);
v_trees_2347_ = lean_ctor_get(v_infoState_2346_, 2);
lean_inc_ref(v_trees_2347_);
lean_dec_ref(v_infoState_2346_);
v___x_2348_ = lean_st_ref_take(v___y_2343_);
v_infoState_2349_ = lean_ctor_get(v___x_2348_, 8);
v_env_2350_ = lean_ctor_get(v___x_2348_, 0);
v_nextMacroScope_2351_ = lean_ctor_get(v___x_2348_, 1);
v_ngen_2352_ = lean_ctor_get(v___x_2348_, 2);
v_auxDeclNGen_2353_ = lean_ctor_get(v___x_2348_, 3);
v_traceState_2354_ = lean_ctor_get(v___x_2348_, 4);
v_cache_2355_ = lean_ctor_get(v___x_2348_, 5);
v_recordedDeps_2356_ = lean_ctor_get(v___x_2348_, 6);
v_messages_2357_ = lean_ctor_get(v___x_2348_, 7);
v_snapshotTasks_2358_ = lean_ctor_get(v___x_2348_, 9);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2360_ = v___x_2348_;
v_isShared_2361_ = v_isSharedCheck_2379_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_snapshotTasks_2358_);
lean_inc(v_infoState_2349_);
lean_inc(v_messages_2357_);
lean_inc(v_recordedDeps_2356_);
lean_inc(v_cache_2355_);
lean_inc(v_traceState_2354_);
lean_inc(v_auxDeclNGen_2353_);
lean_inc(v_ngen_2352_);
lean_inc(v_nextMacroScope_2351_);
lean_inc(v_env_2350_);
lean_dec(v___x_2348_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2379_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
uint8_t v_enabled_2362_; lean_object* v_assignment_2363_; lean_object* v_lazyAssignment_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2377_; 
v_enabled_2362_ = lean_ctor_get_uint8(v_infoState_2349_, sizeof(void*)*3);
v_assignment_2363_ = lean_ctor_get(v_infoState_2349_, 0);
v_lazyAssignment_2364_ = lean_ctor_get(v_infoState_2349_, 1);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_infoState_2349_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; 
v_unused_2378_ = lean_ctor_get(v_infoState_2349_, 2);
lean_dec(v_unused_2378_);
v___x_2366_ = v_infoState_2349_;
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_lazyAssignment_2364_);
lean_inc(v_assignment_2363_);
lean_dec(v_infoState_2349_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2377_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___closed__1);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 2, v___x_2368_);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_assignment_2363_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_lazyAssignment_2364_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v___x_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*3, v_enabled_2362_);
v___x_2370_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 8, v___x_2370_);
v___x_2372_ = v___x_2360_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_env_2350_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_nextMacroScope_2351_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_ngen_2352_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_auxDeclNGen_2353_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v_traceState_2354_);
lean_ctor_set(v_reuseFailAlloc_2375_, 5, v_cache_2355_);
lean_ctor_set(v_reuseFailAlloc_2375_, 6, v_recordedDeps_2356_);
lean_ctor_set(v_reuseFailAlloc_2375_, 7, v_messages_2357_);
lean_ctor_set(v_reuseFailAlloc_2375_, 8, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2375_, 9, v_snapshotTasks_2358_);
v___x_2372_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_st_ref_put(v___y_2343_, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v_trees_2347_);
return v___x_2374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg___boxed(lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2380_);
lean_dec(v___y_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(lean_object* v_x_2383_, lean_object* v_mkInfoTree_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v_infoState_2395_; uint8_t v_enabled_2396_; 
v___x_2394_ = lean_st_ref_get(v___y_2392_);
v_infoState_2395_ = lean_ctor_get(v___x_2394_, 8);
lean_inc_ref(v_infoState_2395_);
lean_dec(v___x_2394_);
v_enabled_2396_ = lean_ctor_get_uint8(v_infoState_2395_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2395_);
if (v_enabled_2396_ == 0)
{
lean_object* v___x_2397_; 
lean_dec_ref(v_mkInfoTree_2384_);
lean_inc(v___y_2392_);
lean_inc_ref(v___y_2391_);
lean_inc(v___y_2390_);
lean_inc_ref(v___y_2389_);
lean_inc(v___y_2388_);
lean_inc_ref(v___y_2387_);
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
v___x_2397_ = lean_apply_9(v_x_2383_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, lean_box(0));
return v___x_2397_;
}
else
{
lean_object* v___x_2398_; lean_object* v_a_2399_; lean_object* v_r_2400_; 
v___x_2398_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2392_);
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref(v___x_2398_);
lean_inc(v___y_2392_);
lean_inc_ref(v___y_2391_);
lean_inc(v___y_2390_);
lean_inc_ref(v___y_2389_);
lean_inc(v___y_2388_);
lean_inc_ref(v___y_2387_);
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
v_r_2400_ = lean_apply_9(v_x_2383_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, lean_box(0));
if (lean_obj_tag(v_r_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2425_; 
v_a_2401_ = lean_ctor_get(v_r_2400_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_r_2400_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2403_ = v_r_2400_;
v_isShared_2404_ = v_isSharedCheck_2425_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v_r_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2425_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
lean_inc(v_a_2401_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set_tag(v___x_2403_, 1);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2392_, v_mkInfoTree_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v_a_2399_, v___x_2406_);
lean_dec_ref(v___x_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v___x_2407_, 0);
lean_dec(v_unused_2415_);
v___x_2409_ = v___x_2407_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_dec(v___x_2407_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v_a_2401_);
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2401_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v_a_2401_);
v_a_2416_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2407_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2407_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_a_2426_ = lean_ctor_get(v_r_2400_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v_r_2400_, 1);
v___x_2427_ = lean_box(0);
v___x_2428_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___lam__0(v___y_2392_, v_mkInfoTree_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v_a_2399_, v___x_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; 
v_unused_2436_ = lean_ctor_get(v___x_2428_, 0);
lean_dec(v_unused_2436_);
v___x_2430_ = v___x_2428_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_dec(v___x_2428_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set_tag(v___x_2430_, 1);
lean_ctor_set(v___x_2430_, 0, v_a_2426_);
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2426_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_a_2426_);
v_a_2437_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2428_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2428_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg___boxed(lean_object* v_x_2445_, lean_object* v_mkInfoTree_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_2445_, v_mkInfoTree_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(lean_object* v___f_2508_, lean_object* v___f_2509_, lean_object* v_stx_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___f_2508_, v___f_2509_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec_ref_known(v___x_2520_, 1);
v___x_2521_ = lean_unsigned_to_nat(1u);
v___x_2522_ = l_Lean_Syntax_getArg(v_stx_2510_, v___x_2521_);
v___x_2523_ = l_Lean_Elab_Tactic_Conv_evalSepByIndentConv(v___x_2522_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___x_2522_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_ref_2524_; uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_dec_ref_known(v___x_2523_, 1);
v_ref_2524_ = lean_ctor_get(v___y_2517_, 2);
v___x_2525_ = 0;
v___x_2526_ = l_Lean_SourceInfo_fromRef(v_ref_2524_, v___x_2525_);
v___x_2527_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__1));
v___x_2528_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__2));
lean_inc_n(v___x_2526_, 22);
v___x_2529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2526_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4));
v___x_2531_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6));
v___x_2532_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_2533_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__10));
v___x_2534_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11));
v___x_2535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2526_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13));
v___x_2537_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14));
v___x_2538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2526_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16));
v___x_2540_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17));
v___x_2541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2526_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19));
v___x_2543_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20));
v___x_2544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2526_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2542_, v___x_2544_);
v___x_2546_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2532_, v___x_2545_);
v___x_2547_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2531_, v___x_2546_);
v___x_2548_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2530_, v___x_2547_);
v___x_2549_ = l_Lean_Syntax_node2(v___x_2526_, v___x_2539_, v___x_2541_, v___x_2548_);
v___x_2550_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2532_, v___x_2549_);
v___x_2551_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2531_, v___x_2550_);
v___x_2552_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2530_, v___x_2551_);
v___x_2553_ = l_Lean_Syntax_node2(v___x_2526_, v___x_2536_, v___x_2538_, v___x_2552_);
v___x_2554_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2532_, v___x_2553_);
v___x_2555_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2531_, v___x_2554_);
v___x_2556_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2530_, v___x_2555_);
v___x_2557_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21));
v___x_2558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2526_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Lean_Syntax_node3(v___x_2526_, v___x_2533_, v___x_2535_, v___x_2556_, v___x_2558_);
v___x_2560_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2532_, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2531_, v___x_2560_);
v___x_2562_ = l_Lean_Syntax_node1(v___x_2526_, v___x_2530_, v___x_2561_);
v___x_2563_ = l_Lean_Syntax_node2(v___x_2526_, v___x_2527_, v___x_2529_, v___x_2562_);
v___x_2564_ = l_Lean_Elab_Tactic_evalTactic(v___x_2563_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
return v___x_2564_;
}
else
{
return v___x_2523_;
}
}
else
{
return v___x_2520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed(lean_object* v___f_2565_, lean_object* v___f_2566_, lean_object* v_stx_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2(v___f_2565_, v___f_2566_, v_stx_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v_stx_2567_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(lean_object* v_stx_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = l_Lean_Syntax_getArg(v_stx_2580_, v___x_2590_);
v___x_2592_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2591_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v_toCold_2594_; lean_object* v_currRecDepth_2595_; lean_object* v_ref_2596_; uint16_t v_optionFlags_2597_; uint8_t v_suppressElabErrors_2598_; uint8_t v_isRecordingDeps_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v_ref_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v_toCold_2594_ = lean_ctor_get(v_a_2587_, 0);
v_currRecDepth_2595_ = lean_ctor_get(v_a_2587_, 1);
v_ref_2596_ = lean_ctor_get(v_a_2587_, 2);
v_optionFlags_2597_ = lean_ctor_get_uint16(v_a_2587_, sizeof(void*)*3);
v_suppressElabErrors_2598_ = lean_ctor_get_uint8(v_a_2587_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2599_ = lean_ctor_get_uint8(v_a_2587_, sizeof(void*)*3 + 3);
v___f_2600_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2600_, 0, v_a_2593_);
v___x_2601_ = lean_unsigned_to_nat(2u);
v___x_2602_ = l_Lean_Syntax_getArg(v_stx_2580_, v___x_2601_);
v___f_2603_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___closed__0));
v___f_2604_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___boxed), 12, 3);
lean_closure_set(v___f_2604_, 0, v___f_2603_);
lean_closure_set(v___f_2604_, 1, v___f_2600_);
lean_closure_set(v___f_2604_, 2, v_stx_2580_);
v_ref_2605_ = l_Lean_replaceRef(v___x_2602_, v_ref_2596_);
lean_dec(v___x_2602_);
lean_inc(v_currRecDepth_2595_);
lean_inc_ref(v_toCold_2594_);
v___x_2606_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2606_, 0, v_toCold_2594_);
lean_ctor_set(v___x_2606_, 1, v_currRecDepth_2595_);
lean_ctor_set(v___x_2606_, 2, v_ref_2605_);
lean_ctor_set_uint16(v___x_2606_, sizeof(void*)*3, v_optionFlags_2597_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3 + 2, v_suppressElabErrors_2598_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3 + 3, v_isRecordingDeps_2599_);
v___x_2607_ = l_Lean_Elab_Tactic_closeUsingOrAdmit(v___f_2604_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v___x_2606_, v_a_2588_);
lean_dec_ref_known(v___x_2606_, 3);
return v___x_2607_;
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_stx_2580_);
v_a_2608_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2592_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2592_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed(lean_object* v_stx_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(v_stx_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___redArg(v___y_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0___boxed(lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0_spec__0(v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(lean_object* v_00_u03b1_2647_, lean_object* v_x_2648_, lean_object* v_mkInfoTree_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v_x_2648_, v_mkInfoTree_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_x_2661_, lean_object* v_mkInfoTree_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0(v_00_u03b1_2660_, v_x_2661_, v_mkInfoTree_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1(){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2688_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__1));
v___x_2690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3));
v___x_2691_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___boxed), 10, 0);
v___x_2692_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2688_, v___x_2689_, v___x_2690_, v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___boxed(lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1();
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3(){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed__1___closed__3));
v___x_2722_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___closed__6));
v___x_2723_ = l_Lean_addBuiltinDeclarationRanges(v___x_2721_, v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3___boxed(lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeqBracketed___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeqBracketed_declRange__3();
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv(lean_object* v_stx_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_unsigned_to_nat(0u);
v___x_2737_ = l_Lean_Syntax_getArg(v_stx_2726_, v___x_2736_);
v___x_2738_ = l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed(v___x_2737_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed(lean_object* v_stx_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Elab_Tactic_Conv_evalNestedConv(v_stx_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_stx_2739_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1(){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2765_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__1));
v___x_2767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3));
v___x_2768_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedConv___boxed), 10, 0);
v___x_2769_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2765_, v___x_2766_, v___x_2767_, v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___boxed(lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1();
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3(){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv__1___closed__3));
v___x_2799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___closed__6));
v___x_2800_ = l_Lean_addBuiltinDeclarationRanges(v___x_2798_, v___x_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3___boxed(lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedConv___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedConv_declRange__3();
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq(lean_object* v_stx_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2813_ = lean_unsigned_to_nat(0u);
v___x_2814_ = l_Lean_Syntax_getArg(v_stx_2803_, v___x_2813_);
v___x_2815_ = l_Lean_Elab_Tactic_evalTactic(v___x_2814_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed(lean_object* v_stx_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Lean_Elab_Tactic_Conv_evalConvSeq(v_stx_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_stx_2816_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1(){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2842_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1));
v___x_2844_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3));
v___x_2845_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeq___boxed), 10, 0);
v___x_2846_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2842_, v___x_2843_, v___x_2844_, v___x_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___boxed(lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1();
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3(){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__3));
v___x_2876_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___closed__6));
v___x_2877_ = l_Lean_addBuiltinDeclarationRanges(v___x_2875_, v___x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3___boxed(lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq_declRange__3();
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(lean_object* v_stx_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_2882_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = lean_unsigned_to_nat(2u);
v___x_2893_ = l_Lean_Syntax_getArg(v_stx_2880_, v___x_2892_);
v___x_2894_ = lean_unsigned_to_nat(0u);
v___x_2895_ = l_Lean_Syntax_getArg(v___x_2893_, v___x_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_2896_, 0, v___x_2895_);
v___x_2897_ = l_Lean_Elab_Tactic_Conv_convert(v_a_2891_, v___x_2896_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v_fst_2899_; lean_object* v_snd_2900_; lean_object* v___x_2901_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
v_fst_2899_ = lean_ctor_get(v_a_2898_, 0);
lean_inc(v_fst_2899_);
v_snd_2900_ = lean_ctor_get(v_a_2898_, 1);
lean_inc(v_snd_2900_);
lean_dec(v_a_2898_);
v___x_2901_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_fst_2899_, v_snd_2900_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
return v___x_2901_;
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
v_a_2902_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2897_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2897_);
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
v_a_2910_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2890_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2890_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed(lean_object* v_stx_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0(v_stx_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v_stx_2918_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq(lean_object* v_stx_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v___f_2939_; lean_object* v___x_2940_; 
v___f_2939_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2939_, 0, v_stx_2929_);
v___x_2940_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2939_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed(lean_object* v_stx_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_Elab_Tactic_Conv_evalConvConvSeq(v_stx_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1(){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2967_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2968_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__1));
v___x_2969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3));
v___x_2970_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvConvSeq___boxed), 10, 0);
v___x_2971_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2967_, v___x_2968_, v___x_2969_, v___x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___boxed(lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1();
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3(){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq__1___closed__3));
v___x_3001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___closed__6));
v___x_3002_ = l_Lean_addBuiltinDeclarationRanges(v___x_3000_, v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3___boxed(lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvConvSeq_declRange__3();
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen(lean_object* v_stx_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_unsigned_to_nat(1u);
v___x_3016_ = l_Lean_Syntax_getArg(v_stx_3005_, v___x_3015_);
v___x_3017_ = l_Lean_Elab_Tactic_evalTactic(v___x_3016_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalParen___boxed(lean_object* v_stx_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Elab_Tactic_Conv_evalParen(v_stx_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_stx_3018_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1(){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3043_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3044_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0));
v___x_3045_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2));
v___x_3046_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalParen___boxed), 10, 0);
v___x_3047_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3043_, v___x_3044_, v___x_3045_, v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___boxed(lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1();
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3(){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__2));
v___x_3077_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___closed__6));
v___x_3078_ = l_Lean_addBuiltinDeclarationRanges(v___x_3076_, v___x_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3___boxed(lean_object* v_a_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen_declRange__3();
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(lean_object* v_x_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v___x_3091_; 
lean_inc(v___y_3085_);
lean_inc_ref(v___y_3084_);
lean_inc(v___y_3083_);
lean_inc_ref(v___y_3082_);
v___x_3091_ = lean_apply_9(v_x_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, lean_box(0));
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed(lean_object* v_x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0(v_x_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(lean_object* v_mvarId_3103_, lean_object* v_x_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___f_3114_; lean_object* v___x_3115_; 
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3114_, 0, v_x_3104_);
lean_closure_set(v___f_3114_, 1, v___y_3105_);
lean_closure_set(v___f_3114_, 2, v___y_3106_);
lean_closure_set(v___f_3114_, 3, v___y_3107_);
lean_closure_set(v___f_3114_, 4, v___y_3108_);
v___x_3115_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3103_, v___f_3114_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3115_) == 0)
{
return v___x_3115_;
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg___boxed(lean_object* v_mvarId_3124_, lean_object* v_x_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_mvarId_3124_, v_x_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(lean_object* v_00_u03b1_3136_, lean_object* v_mvarId_3137_, lean_object* v_x_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_mvarId_3137_, v_x_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___boxed(lean_object* v_00_u03b1_3149_, lean_object* v_mvarId_3150_, lean_object* v_x_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0(v_00_u03b1_3149_, v_mvarId_3150_, v_x_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(lean_object* v_head_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
lean_inc(v_head_3162_);
v___x_3172_ = l_Lean_MVarId_getType(v_head_3162_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3174_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc_n(v_a_3173_, 2);
lean_dec_ref_known(v___x_3172_, 1);
v___x_3174_ = l_Lean_Meta_matchEq_x3f(v_a_3173_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3201_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3201_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3201_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
if (lean_obj_tag(v_a_3175_) == 1)
{
lean_object* v_val_3179_; lean_object* v_snd_3180_; lean_object* v_snd_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v_val_3179_ = lean_ctor_get(v_a_3175_, 0);
lean_inc(v_val_3179_);
lean_dec_ref_known(v_a_3175_, 1);
v_snd_3180_ = lean_ctor_get(v_val_3179_, 1);
lean_inc(v_snd_3180_);
lean_dec(v_val_3179_);
v_snd_3181_ = lean_ctor_get(v_snd_3180_, 1);
lean_inc(v_snd_3181_);
lean_dec(v_snd_3180_);
v___x_3182_ = l_Lean_Expr_getAppFn(v_snd_3181_);
lean_dec(v_snd_3181_);
v___x_3183_ = l_Lean_Expr_isMVar(v___x_3182_);
lean_dec_ref(v___x_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3185_; 
lean_dec(v_a_3173_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v_head_3162_);
v___x_3185_ = v___x_3177_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_head_3162_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
else
{
lean_object* v___x_3187_; 
lean_del_object(v___x_3177_);
v___x_3187_ = l_Lean_Elab_Tactic_Conv_mkLHSGoal(v_a_3173_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3189_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
v___x_3189_ = l_Lean_MVarId_replaceTargetDefEq(v_head_3162_, v_a_3188_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3189_;
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_head_3162_);
v_a_3190_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3187_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3187_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
else
{
lean_object* v___x_3199_; 
lean_dec(v_a_3175_);
lean_dec(v_a_3173_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v_head_3162_);
v___x_3199_ = v___x_3177_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_head_3162_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_a_3173_);
lean_dec(v_head_3162_);
v_a_3202_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3174_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3174_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_head_3162_);
v_a_3210_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3172_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3172_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed(lean_object* v_head_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0(v_head_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(lean_object* v_x_3229_, lean_object* v_x_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
if (lean_obj_tag(v_x_3229_) == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = l_List_reverse___redArg(v_x_3230_);
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
return v___x_3241_;
}
else
{
lean_object* v_head_3242_; lean_object* v_tail_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3262_; 
v_head_3242_ = lean_ctor_get(v_x_3229_, 0);
v_tail_3243_ = lean_ctor_get(v_x_3229_, 1);
v_isSharedCheck_3262_ = !lean_is_exclusive(v_x_3229_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3245_ = v_x_3229_;
v_isShared_3246_ = v_isSharedCheck_3262_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_tail_3243_);
lean_inc(v_head_3242_);
lean_dec(v_x_3229_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3262_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___f_3247_; lean_object* v___x_3248_; 
lean_inc(v_head_3242_);
v___f_3247_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3247_, 0, v_head_3242_);
v___x_3248_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__0___redArg(v_head_3242_, v___f_3247_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3251_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 1, v_x_3230_);
lean_ctor_set(v___x_3245_, 0, v_a_3249_);
v___x_3251_ = v___x_3245_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3249_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_x_3230_);
v___x_3251_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
v_x_3229_ = v_tail_3243_;
v_x_3230_ = v___x_3251_;
goto _start;
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_del_object(v___x_3245_);
lean_dec(v_tail_3243_);
lean_dec(v_x_3230_);
v_a_3254_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3248_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3248_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1___boxed(lean_object* v_x_3263_, lean_object* v_x_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(v_x_3263_, v_x_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_Elab_Tactic_getUnsolvedGoals(v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = lean_box(0);
v___x_3287_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Conv_remarkAsConvGoal_spec__1(v_a_3285_, v___x_3286_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3289_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___x_3287_, 1);
v___x_3289_ = l_Lean_Elab_Tactic_setGoals___redArg(v_a_3288_, v_a_3276_);
return v___x_3289_;
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_a_3290_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3287_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3287_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
v_a_3298_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3284_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3284_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_remarkAsConvGoal___boxed(lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(lean_object* v_stx_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v_seq_3327_; lean_object* v___x_3328_; 
v___x_3326_ = lean_unsigned_to_nat(2u);
v_seq_3327_ = l_Lean_Syntax_getArg(v_stx_3316_, v___x_3326_);
v___x_3328_ = l_Lean_Elab_Tactic_evalTactic(v_seq_3327_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v___x_3329_; 
lean_dec_ref_known(v___x_3328_, 1);
v___x_3329_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
return v___x_3329_;
}
else
{
return v___x_3328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed(lean_object* v_stx_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Elab_Tactic_Conv_evalNestedTacticCore(v_stx_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec(v_a_3332_);
lean_dec_ref(v_a_3331_);
lean_dec(v_stx_3330_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1(){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3356_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__1));
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3));
v___x_3359_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTacticCore___boxed), 10, 0);
v___x_3360_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3356_, v___x_3357_, v___x_3358_, v___x_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___boxed(lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1();
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3(){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore__1___closed__3));
v___x_3390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___closed__6));
v___x_3391_ = l_Lean_addBuiltinDeclarationRanges(v___x_3389_, v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3___boxed(lean_object* v_a_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTacticCore___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTacticCore_declRange__3();
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(lean_object* v_seq_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_Elab_Tactic_evalTactic(v_seq_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v___x_3405_; 
lean_dec_ref_known(v___x_3404_, 1);
v___x_3405_ = l_Lean_Elab_Tactic_Conv_remarkAsConvGoal(v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v___x_3405_;
}
else
{
return v___x_3404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed(lean_object* v_seq_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0(v_seq_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(lean_object* v_a_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3419_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3429_ = l_Lean_Expr_mdataExpr_x21(v_a_3417_);
v___x_3430_ = l_Lean_MVarId_replaceTargetDefEq(v_a_3428_, v___x_3429_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = lean_box(0);
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_a_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3433_, v___y_3419_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
return v___x_3434_;
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
v_a_3435_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3430_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3430_);
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
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
v_a_3443_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3427_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3427_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed(lean_object* v_a_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1(v_a_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec_ref(v_a_3451_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic(lean_object* v_stx_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v___x_3472_; lean_object* v_seq_3473_; lean_object* v___f_3474_; lean_object* v___x_3475_; 
v___x_3472_ = lean_unsigned_to_nat(2u);
v_seq_3473_ = l_Lean_Syntax_getArg(v_stx_3462_, v___x_3472_);
v___f_3474_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3474_, 0, v_seq_3473_);
v___x_3475_ = l_Lean_Elab_Tactic_getMainTarget(v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3477_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v___x_3477_ = l_Lean_isLHSGoal_x3f(v_a_3476_);
if (lean_obj_tag(v___x_3477_) == 1)
{
lean_object* v___f_3478_; lean_object* v___x_3479_; 
lean_dec_ref_known(v___x_3477_, 1);
v___f_3478_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___lam__1___boxed), 10, 1);
lean_closure_set(v___f_3478_, 0, v_a_3476_);
v___x_3479_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3478_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v___x_3480_; 
lean_dec_ref_known(v___x_3479_, 1);
v___x_3480_ = l_Lean_Elab_Tactic_focus___redArg(v___f_3474_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
return v___x_3480_;
}
else
{
lean_dec_ref(v___f_3474_);
return v___x_3479_;
}
}
else
{
lean_object* v___x_3481_; 
lean_dec(v___x_3477_);
lean_dec(v_a_3476_);
v___x_3481_ = l_Lean_Elab_Tactic_focus___redArg(v___f_3474_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
return v___x_3481_;
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v___f_3474_);
v_a_3482_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3475_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3475_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed(lean_object* v_stx_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Elab_Tactic_Conv_evalNestedTactic(v_stx_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
lean_dec(v_a_3498_);
lean_dec_ref(v_a_3497_);
lean_dec(v_a_3496_);
lean_dec_ref(v_a_3495_);
lean_dec(v_a_3494_);
lean_dec_ref(v_a_3493_);
lean_dec(v_a_3492_);
lean_dec_ref(v_a_3491_);
lean_dec(v_stx_3490_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1(){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3516_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__1));
v___x_3518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3));
v___x_3519_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalNestedTactic___boxed), 10, 0);
v___x_3520_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3516_, v___x_3517_, v___x_3518_, v___x_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___boxed(lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1();
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3(){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic__1___closed__3));
v___x_3550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___closed__6));
v___x_3551_ = l_Lean_addBuiltinDeclarationRanges(v___x_3549_, v___x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3___boxed(lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalNestedTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalNestedTactic_declRange__3();
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic(lean_object* v_stx_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_unsigned_to_nat(2u);
v___x_3565_ = l_Lean_Syntax_getArg(v_stx_3554_, v___x_3564_);
v___x_3566_ = l_Lean_Elab_Tactic_evalTactic(v___x_3565_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed(lean_object* v_stx_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_Elab_Tactic_Conv_evalConvTactic(v_stx_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_stx_3567_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1(){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3593_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__1));
v___x_3595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3));
v___x_3596_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvTactic___boxed), 10, 0);
v___x_3597_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3593_, v___x_3594_, v___x_3595_, v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___boxed(lean_object* v_a_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1();
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3(){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic__1___closed__3));
v___x_3627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___closed__6));
v___x_3628_ = l_Lean_addBuiltinDeclarationRanges(v___x_3626_, v___x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3___boxed(lean_object* v_a_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvTactic___regBuiltin_Lean_Elab_Tactic_Conv_evalConvTactic_declRange__3();
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(lean_object* v_ref_3631_, lean_object* v___x_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_3631_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___f_3644_; lean_object* v___x_3645_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___x_3642_, 1);
v___f_3644_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3644_, 0, v_a_3643_);
v___x_3645_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalConvSeqBracketed_spec__0___redArg(v___x_3632_, v___f_3644_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
return v___x_3645_;
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec_ref(v___x_3632_);
v_a_3646_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3642_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3642_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed(lean_object* v_ref_3654_, lean_object* v___x_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1(v_ref_3654_, v___x_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(lean_object* v_fst_3666_, lean_object* v_snd_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3669_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3679_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3677_, 1);
v___x_3679_ = l_Lean_MVarId_replaceTargetEq(v_a_3678_, v_fst_3666_, v_snd_3667_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3679_, 1);
v___x_3681_ = lean_box(0);
v___x_3682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3682_, 0, v_a_3680_);
lean_ctor_set(v___x_3682_, 1, v___x_3681_);
v___x_3683_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3682_, v___y_3669_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
return v___x_3683_;
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
v_a_3684_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3679_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3679_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec_ref(v_snd_3667_);
lean_dec_ref(v_fst_3666_);
v_a_3692_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3677_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3677_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed(lean_object* v_fst_3700_, lean_object* v_snd_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0(v_fst_3700_, v_snd_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(lean_object* v_conv_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Elab_Tactic_getMainTarget(v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v_ref_3724_; lean_object* v___x_3725_; lean_object* v___f_3726_; lean_object* v___x_3727_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
v_ref_3724_ = lean_ctor_get(v___y_3719_, 2);
v___x_3725_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_3725_, 0, v_conv_3712_);
lean_inc(v_ref_3724_);
v___f_3726_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3726_, 0, v_ref_3724_);
lean_closure_set(v___f_3726_, 1, v___x_3725_);
v___x_3727_ = l_Lean_Elab_Tactic_Conv_convert(v_a_3723_, v___f_3726_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v_fst_3729_; lean_object* v_snd_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3762_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v_fst_3729_ = lean_ctor_get(v_a_3728_, 0);
v_snd_3730_ = lean_ctor_get(v_a_3728_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_a_3728_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3732_ = v_a_3728_;
v_isShared_3733_ = v_isSharedCheck_3762_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_snd_3730_);
lean_inc(v_fst_3729_);
lean_dec(v_a_3728_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3762_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___f_3734_; lean_object* v___x_3735_; 
v___f_3734_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__0___boxed), 11, 2);
lean_closure_set(v___f_3734_, 0, v_fst_3729_);
lean_closure_set(v___f_3734_, 1, v_snd_3730_);
v___x_3735_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3734_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3735_) == 0)
{
uint8_t v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3741_; 
lean_dec_ref_known(v___x_3735_, 1);
v___x_3736_ = 0;
v___x_3737_ = l_Lean_SourceInfo_fromRef(v_ref_3724_, v___x_3736_);
v___x_3738_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__13));
v___x_3739_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__14));
lean_inc(v___x_3737_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set_tag(v___x_3732_, 2);
lean_ctor_set(v___x_3732_, 1, v___x_3739_);
lean_ctor_set(v___x_3732_, 0, v___x_3737_);
v___x_3741_ = v___x_3732_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3742_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__4));
v___x_3743_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__6));
v___x_3744_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_3745_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__16));
v___x_3746_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__17));
lean_inc_n(v___x_3737_, 10);
v___x_3747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3737_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__19));
v___x_3749_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__20));
v___x_3750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3737_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = l_Lean_Syntax_node1(v___x_3737_, v___x_3748_, v___x_3750_);
v___x_3752_ = l_Lean_Syntax_node1(v___x_3737_, v___x_3744_, v___x_3751_);
v___x_3753_ = l_Lean_Syntax_node1(v___x_3737_, v___x_3743_, v___x_3752_);
v___x_3754_ = l_Lean_Syntax_node1(v___x_3737_, v___x_3742_, v___x_3753_);
v___x_3755_ = l_Lean_Syntax_node2(v___x_3737_, v___x_3745_, v___x_3747_, v___x_3754_);
v___x_3756_ = l_Lean_Syntax_node1(v___x_3737_, v___x_3744_, v___x_3755_);
v___x_3757_ = l_Lean_Syntax_node1(v___x_3737_, v___x_3743_, v___x_3756_);
v___x_3758_ = l_Lean_Syntax_node1(v___x_3737_, v___x_3742_, v___x_3757_);
v___x_3759_ = l_Lean_Syntax_node2(v___x_3737_, v___x_3738_, v___x_3741_, v___x_3758_);
v___x_3760_ = l_Lean_Elab_Tactic_evalTactic(v___x_3759_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec_ref(v___y_3719_);
return v___x_3760_;
}
}
else
{
lean_del_object(v___x_3732_);
lean_dec_ref(v___y_3719_);
return v___x_3735_;
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec_ref(v___y_3719_);
v_a_3763_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3727_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3727_);
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
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec_ref(v___y_3719_);
lean_dec(v_conv_3712_);
v_a_3771_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3722_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3722_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed(lean_object* v_conv_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2(v_conv_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
lean_dec(v___y_3787_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(lean_object* v_conv_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_){
_start:
{
lean_object* v___f_3800_; lean_object* v___x_3801_; 
v___f_3800_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3800_, 0, v_conv_3790_);
v___x_3801_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3800_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___boxed(lean_object* v_conv_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(v_conv_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec(v_a_3808_);
lean_dec_ref(v_a_3807_);
lean_dec(v_a_3806_);
lean_dec_ref(v_a_3805_);
lean_dec(v_a_3804_);
lean_dec_ref(v_a_3803_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(lean_object* v_snd_3813_, lean_object* v___x_3814_, lean_object* v_fst_3815_, lean_object* v_a_3816_, lean_object* v___x_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Meta_mkEqMP(v_snd_3813_, v___x_3814_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3823_, 1);
v___x_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3825_, 0, v_fst_3815_);
v___x_3826_ = lean_box(0);
v___x_3827_ = l_Lean_MVarId_replace(v_a_3816_, v___x_3817_, v_a_3824_, v___x_3825_, v___x_3826_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
return v___x_3827_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v___x_3817_);
lean_dec(v_a_3816_);
lean_dec_ref(v_fst_3815_);
v_a_3828_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3823_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3823_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed(lean_object* v_snd_3836_, lean_object* v___x_3837_, lean_object* v_fst_3838_, lean_object* v_a_3839_, lean_object* v___x_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2(v_snd_3836_, v___x_3837_, v_fst_3838_, v_a_3839_, v___x_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(lean_object* v_a_3847_, lean_object* v_snd_3848_, lean_object* v_fst_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3851_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___f_3863_; lean_object* v___x_3864_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc_n(v_a_3860_, 2);
lean_dec_ref_known(v___x_3859_, 1);
v___x_3861_ = l_Lean_LocalDecl_fvarId(v_a_3847_);
lean_inc(v___x_3861_);
v___x_3862_ = l_Lean_mkFVar(v___x_3861_);
v___f_3863_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3863_, 0, v_snd_3848_);
lean_closure_set(v___f_3863_, 1, v___x_3862_);
lean_closure_set(v___f_3863_, 2, v_fst_3849_);
lean_closure_set(v___f_3863_, 3, v_a_3860_);
lean_closure_set(v___f_3863_, 4, v___x_3861_);
v___x_3864_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_getLhsRhsCore_spec__1___redArg(v_a_3860_, v___f_3863_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v_mvarId_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v_mvarId_3866_ = lean_ctor_get(v_a_3865_, 1);
lean_inc(v_mvarId_3866_);
lean_dec(v_a_3865_);
v___x_3867_ = lean_box(0);
v___x_3868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3868_, 0, v_mvarId_3866_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3868_, v___y_3851_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v___x_3869_;
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
v_a_3870_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3864_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3864_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v_fst_3849_);
lean_dec_ref(v_snd_3848_);
v_a_3878_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3859_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3859_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed(lean_object* v_a_3886_, lean_object* v_snd_3887_, lean_object* v_fst_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0(v_a_3886_, v_snd_3887_, v_fst_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec_ref(v_a_3886_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(lean_object* v_hUserName_3899_, lean_object* v_conv_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_Meta_getLocalDeclFromUserName(v_hUserName_3899_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v_ref_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___f_3915_; lean_object* v___x_3916_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v_ref_3912_ = lean_ctor_get(v___y_3907_, 2);
v___x_3913_ = l_Lean_LocalDecl_type(v_a_3911_);
v___x_3914_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_3914_, 0, v_conv_3900_);
lean_inc(v_ref_3912_);
v___f_3915_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3915_, 0, v_ref_3912_);
lean_closure_set(v___f_3915_, 1, v___x_3914_);
v___x_3916_ = l_Lean_Elab_Tactic_Conv_convert(v___x_3913_, v___f_3915_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v_fst_3918_; lean_object* v_snd_3919_; lean_object* v___f_3920_; lean_object* v___x_3921_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v_fst_3918_ = lean_ctor_get(v_a_3917_, 0);
lean_inc(v_fst_3918_);
v_snd_3919_ = lean_ctor_get(v_a_3917_, 1);
lean_inc(v_snd_3919_);
lean_dec(v_a_3917_);
v___f_3920_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__0___boxed), 12, 3);
lean_closure_set(v___f_3920_, 0, v_a_3911_);
lean_closure_set(v___f_3920_, 1, v_snd_3919_);
lean_closure_set(v___f_3920_, 2, v_fst_3918_);
v___x_3921_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3920_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
lean_dec_ref(v___y_3907_);
return v___x_3921_;
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec(v_a_3911_);
lean_dec_ref(v___y_3907_);
v_a_3922_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3916_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3916_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec_ref(v___y_3907_);
lean_dec(v_conv_3900_);
v_a_3930_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3910_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3910_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed(lean_object* v_hUserName_3938_, lean_object* v_conv_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1(v_hUserName_3938_, v_conv_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(lean_object* v_conv_3950_, lean_object* v_hUserName_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v___f_3961_; lean_object* v___x_3962_; 
v___f_3961_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___lam__1___boxed), 11, 2);
lean_closure_set(v___f_3961_, 0, v_hUserName_3951_);
lean_closure_set(v___f_3961_, 1, v_conv_3950_);
v___x_3962_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_3961_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl___boxed(lean_object* v_conv_3963_, lean_object* v_hUserName_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(v_conv_3963_, v_hUserName_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_);
lean_dec(v_a_3972_);
lean_dec_ref(v_a_3971_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
return v_res_3974_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7(void){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Array_mkArray0___redArg();
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv(lean_object* v_stx_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; uint8_t v___x_4046_; 
v___x_4005_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__0));
v___x_4006_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__1));
lean_inc(v_stx_3995_);
v___x_4046_ = l_Lean_Syntax_isOfKind(v_stx_3995_, v___x_4006_);
if (v___x_4046_ == 0)
{
lean_object* v___x_4047_; 
lean_dec(v_stx_3995_);
v___x_4047_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4047_;
}
else
{
lean_object* v___x_4048_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v_tk_4082_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___x_4110_; lean_object* v_loc_x3f_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v___x_4048_ = lean_unsigned_to_nat(0u);
v_tk_4082_ = l_Lean_Syntax_getArg(v_stx_3995_, v___x_4048_);
v___x_4110_ = lean_unsigned_to_nat(1u);
v___x_4164_ = l_Lean_Syntax_getArg(v_stx_3995_, v___x_4110_);
v___x_4165_ = l_Lean_Syntax_isNone(v___x_4164_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; uint8_t v___x_4167_; 
v___x_4166_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4164_);
v___x_4167_ = l_Lean_Syntax_matchesNull(v___x_4164_, v___x_4166_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; 
lean_dec(v___x_4164_);
lean_dec(v_tk_4082_);
lean_dec(v_stx_3995_);
v___x_4168_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4168_;
}
else
{
lean_object* v_loc_x3f_4169_; lean_object* v___x_4170_; 
v_loc_x3f_4169_ = l_Lean_Syntax_getArg(v___x_4164_, v___x_4110_);
lean_dec(v___x_4164_);
v___x_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4170_, 0, v_loc_x3f_4169_);
v_loc_x3f_4112_ = v___x_4170_;
v___y_4113_ = v_a_3996_;
v___y_4114_ = v_a_3997_;
v___y_4115_ = v_a_3998_;
v___y_4116_ = v_a_3999_;
v___y_4117_ = v_a_4000_;
v___y_4118_ = v_a_4001_;
v___y_4119_ = v_a_4002_;
v___y_4120_ = v_a_4003_;
goto v___jp_4111_;
}
}
else
{
lean_object* v___x_4171_; 
lean_dec(v___x_4164_);
v___x_4171_ = lean_box(0);
v_loc_x3f_4112_ = v___x_4171_;
v___y_4113_ = v_a_3996_;
v___y_4114_ = v_a_3997_;
v___y_4115_ = v_a_3998_;
v___y_4116_ = v_a_3999_;
v___y_4117_ = v_a_4000_;
v___y_4118_ = v_a_4001_;
v___y_4119_ = v_a_4002_;
v___y_4120_ = v_a_4003_;
goto v___jp_4111_;
}
v___jp_4049_:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_inc_ref_n(v___y_4052_, 2);
v___x_4068_ = l_Array_append___redArg(v___y_4052_, v___y_4067_);
lean_dec_ref(v___y_4067_);
lean_inc_n(v___y_4053_, 2);
lean_inc_n(v___y_4062_, 3);
v___x_4069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4069_, 0, v___y_4062_);
lean_ctor_set(v___x_4069_, 1, v___y_4053_);
lean_ctor_set(v___x_4069_, 2, v___x_4068_);
v___x_4070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4070_, 0, v___y_4062_);
lean_ctor_set(v___x_4070_, 1, v___y_4053_);
lean_ctor_set(v___x_4070_, 2, v___y_4052_);
v___x_4071_ = l_Lean_SourceInfo_fromRef(v___y_4054_, v___x_4046_);
lean_dec(v___y_4054_);
v___x_4072_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__3));
v___x_4073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4071_);
lean_ctor_set(v___x_4073_, 1, v___x_4072_);
v___x_4074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq1Indented___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq1Indented__1___closed__1));
v___x_4075_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__4));
v___x_4076_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__5));
v___x_4077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___y_4062_);
lean_ctor_set(v___x_4077_, 1, v___x_4075_);
if (lean_obj_tag(v___y_4060_) == 0)
{
lean_object* v___x_4078_; 
v___x_4078_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___y_4008_ = v___y_4050_;
v___y_4009_ = v___y_4051_;
v___y_4010_ = v___x_4074_;
v___y_4011_ = v___x_4076_;
v___y_4012_ = v___y_4052_;
v___y_4013_ = v___y_4053_;
v___y_4014_ = v___x_4069_;
v___y_4015_ = v___y_4055_;
v___y_4016_ = v___y_4056_;
v___y_4017_ = v___x_4070_;
v___y_4018_ = v___y_4057_;
v___y_4019_ = v___y_4058_;
v___y_4020_ = v___x_4073_;
v___y_4021_ = v___y_4059_;
v___y_4022_ = v___x_4077_;
v___y_4023_ = v___y_4061_;
v___y_4024_ = v___y_4062_;
v___y_4025_ = v___y_4063_;
v___y_4026_ = v___y_4065_;
v___y_4027_ = v___y_4064_;
v___y_4028_ = v___y_4066_;
v___y_4029_ = v___x_4078_;
goto v___jp_4007_;
}
else
{
lean_object* v_val_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v_val_4079_ = lean_ctor_get(v___y_4060_, 0);
lean_inc(v_val_4079_);
lean_dec_ref_known(v___y_4060_, 1);
v___x_4080_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___x_4081_ = lean_array_push(v___x_4080_, v_val_4079_);
v___y_4008_ = v___y_4050_;
v___y_4009_ = v___y_4051_;
v___y_4010_ = v___x_4074_;
v___y_4011_ = v___x_4076_;
v___y_4012_ = v___y_4052_;
v___y_4013_ = v___y_4053_;
v___y_4014_ = v___x_4069_;
v___y_4015_ = v___y_4055_;
v___y_4016_ = v___y_4056_;
v___y_4017_ = v___x_4070_;
v___y_4018_ = v___y_4057_;
v___y_4019_ = v___y_4058_;
v___y_4020_ = v___x_4073_;
v___y_4021_ = v___y_4059_;
v___y_4022_ = v___x_4077_;
v___y_4023_ = v___y_4061_;
v___y_4024_ = v___y_4062_;
v___y_4025_ = v___y_4063_;
v___y_4026_ = v___y_4065_;
v___y_4027_ = v___y_4064_;
v___y_4028_ = v___y_4066_;
v___y_4029_ = v___x_4081_;
goto v___jp_4007_;
}
}
v___jp_4083_:
{
lean_object* v_ref_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v_ref_4098_ = lean_ctor_get(v___y_4089_, 2);
v___x_4099_ = 0;
v___x_4100_ = l_Lean_SourceInfo_fromRef(v_ref_4098_, v___x_4099_);
v___x_4101_ = l_Lean_SourceInfo_fromRef(v_tk_4082_, v___x_4046_);
lean_dec(v_tk_4082_);
v___x_4102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
lean_ctor_set(v___x_4102_, 1, v___x_4005_);
v___x_4103_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_4104_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalConv___closed__7, &l_Lean_Elab_Tactic_Conv_evalConv___closed__7_once, _init_l_Lean_Elab_Tactic_Conv_evalConv___closed__7);
if (lean_obj_tag(v___y_4092_) == 1)
{
lean_object* v_val_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_val_4105_ = lean_ctor_get(v___y_4092_, 0);
lean_inc(v_val_4105_);
lean_dec_ref_known(v___y_4092_, 1);
v___x_4106_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__8));
lean_inc(v___x_4100_);
v___x_4107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4100_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = l_Array_mkArray2___redArg(v___x_4107_, v_val_4105_);
v___y_4050_ = v___y_4084_;
v___y_4051_ = v___y_4085_;
v___y_4052_ = v___x_4104_;
v___y_4053_ = v___x_4103_;
v___y_4054_ = v___y_4086_;
v___y_4055_ = v___y_4087_;
v___y_4056_ = v___y_4088_;
v___y_4057_ = v___y_4089_;
v___y_4058_ = v___x_4102_;
v___y_4059_ = v___y_4090_;
v___y_4060_ = v___y_4097_;
v___y_4061_ = v___y_4091_;
v___y_4062_ = v___x_4100_;
v___y_4063_ = v___y_4093_;
v___y_4064_ = v___y_4094_;
v___y_4065_ = v___y_4095_;
v___y_4066_ = v___y_4096_;
v___y_4067_ = v___x_4108_;
goto v___jp_4049_;
}
else
{
lean_object* v___x_4109_; 
lean_dec(v___y_4092_);
v___x_4109_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__6));
v___y_4050_ = v___y_4084_;
v___y_4051_ = v___y_4085_;
v___y_4052_ = v___x_4104_;
v___y_4053_ = v___x_4103_;
v___y_4054_ = v___y_4086_;
v___y_4055_ = v___y_4087_;
v___y_4056_ = v___y_4088_;
v___y_4057_ = v___y_4089_;
v___y_4058_ = v___x_4102_;
v___y_4059_ = v___y_4090_;
v___y_4060_ = v___y_4097_;
v___y_4061_ = v___y_4091_;
v___y_4062_ = v___x_4100_;
v___y_4063_ = v___y_4093_;
v___y_4064_ = v___y_4094_;
v___y_4065_ = v___y_4095_;
v___y_4066_ = v___y_4096_;
v___y_4067_ = v___x_4109_;
goto v___jp_4049_;
}
}
v___jp_4111_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; uint8_t v___x_4124_; 
v___x_4121_ = lean_unsigned_to_nat(2u);
v___x_4122_ = l_Lean_Syntax_getArg(v_stx_3995_, v___x_4121_);
v___x_4123_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_4122_);
v___x_4124_ = l_Lean_Syntax_matchesNull(v___x_4122_, v___x_4123_);
if (v___x_4124_ == 0)
{
uint8_t v___x_4125_; 
v___x_4125_ = l_Lean_Syntax_matchesNull(v___x_4122_, v___x_4048_);
if (v___x_4125_ == 0)
{
lean_object* v___x_4126_; 
lean_dec(v_loc_x3f_4112_);
lean_dec(v_tk_4082_);
lean_dec(v_stx_3995_);
v___x_4126_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalClear_spec__0___redArg();
return v___x_4126_;
}
else
{
lean_object* v_toCold_4127_; lean_object* v_currRecDepth_4128_; lean_object* v_ref_4129_; uint16_t v_optionFlags_4130_; uint8_t v_suppressElabErrors_4131_; uint8_t v_isRecordingDeps_4132_; lean_object* v_arr_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v_ref_4142_; lean_object* v___x_4143_; 
v_toCold_4127_ = lean_ctor_get(v___y_4119_, 0);
v_currRecDepth_4128_ = lean_ctor_get(v___y_4119_, 1);
v_ref_4129_ = lean_ctor_get(v___y_4119_, 2);
v_optionFlags_4130_ = lean_ctor_get_uint16(v___y_4119_, sizeof(void*)*3);
v_suppressElabErrors_4131_ = lean_ctor_get_uint8(v___y_4119_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4132_ = lean_ctor_get_uint8(v___y_4119_, sizeof(void*)*3 + 3);
v_arr_4133_ = l_Lean_Syntax_getArg(v_stx_3995_, v___x_4123_);
v___x_4134_ = lean_unsigned_to_nat(4u);
v___x_4135_ = l_Lean_Syntax_getArg(v_stx_3995_, v___x_4134_);
lean_dec(v_stx_3995_);
v___x_4136_ = lean_mk_empty_array_with_capacity(v___x_4121_);
v___x_4137_ = lean_array_push(v___x_4136_, v_tk_4082_);
v___x_4138_ = lean_array_push(v___x_4137_, v_arr_4133_);
v___x_4139_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__8));
v___x_4140_ = lean_box(2);
v___x_4141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4140_);
lean_ctor_set(v___x_4141_, 1, v___x_4139_);
lean_ctor_set(v___x_4141_, 2, v___x_4138_);
v_ref_4142_ = l_Lean_replaceRef(v___x_4141_, v_ref_4129_);
lean_dec_ref_known(v___x_4141_, 3);
lean_inc(v_currRecDepth_4128_);
lean_inc_ref(v_toCold_4127_);
v___x_4143_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4143_, 0, v_toCold_4127_);
lean_ctor_set(v___x_4143_, 1, v_currRecDepth_4128_);
lean_ctor_set(v___x_4143_, 2, v_ref_4142_);
lean_ctor_set_uint16(v___x_4143_, sizeof(void*)*3, v_optionFlags_4130_);
lean_ctor_set_uint8(v___x_4143_, sizeof(void*)*3 + 2, v_suppressElabErrors_4131_);
lean_ctor_set_uint8(v___x_4143_, sizeof(void*)*3 + 3, v_isRecordingDeps_4132_);
if (lean_obj_tag(v_loc_x3f_4112_) == 1)
{
lean_object* v_val_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v_val_4144_ = lean_ctor_get(v_loc_x3f_4112_, 0);
lean_inc(v_val_4144_);
lean_dec_ref_known(v_loc_x3f_4112_, 1);
v___x_4145_ = l_Lean_TSyntax_getId(v_val_4144_);
lean_dec(v_val_4144_);
v___x_4146_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convLocalDecl(v___x_4135_, v___x_4145_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___x_4143_, v___y_4120_);
lean_dec_ref_known(v___x_4143_, 3);
return v___x_4146_;
}
else
{
lean_object* v___x_4147_; 
lean_dec(v_loc_x3f_4112_);
v___x_4147_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_convTarget(v___x_4135_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___x_4143_, v___y_4120_);
lean_dec_ref_known(v___x_4143_, 3);
return v___x_4147_;
}
}
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v_arr_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4148_ = l_Lean_Syntax_getArg(v___x_4122_, v___x_4110_);
v___x_4149_ = l_Lean_Syntax_getArg(v___x_4122_, v___x_4121_);
lean_dec(v___x_4122_);
v_arr_4150_ = l_Lean_Syntax_getArg(v_stx_3995_, v___x_4123_);
v___x_4151_ = lean_unsigned_to_nat(4u);
v___x_4152_ = l_Lean_Syntax_getArg(v_stx_3995_, v___x_4151_);
lean_dec(v_stx_3995_);
v___x_4153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConvSeq___regBuiltin_Lean_Elab_Tactic_Conv_evalConvSeq__1___closed__1));
v___x_4154_ = l_Lean_Syntax_getOptional_x3f(v___x_4148_);
lean_dec(v___x_4148_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v___x_4155_; 
v___x_4155_ = lean_box(0);
v___y_4084_ = v___y_4117_;
v___y_4085_ = v___y_4113_;
v___y_4086_ = v_arr_4150_;
v___y_4087_ = v___y_4120_;
v___y_4088_ = v___y_4114_;
v___y_4089_ = v___y_4119_;
v___y_4090_ = v___x_4149_;
v___y_4091_ = v___x_4153_;
v___y_4092_ = v_loc_x3f_4112_;
v___y_4093_ = v___x_4152_;
v___y_4094_ = v___y_4116_;
v___y_4095_ = v___y_4118_;
v___y_4096_ = v___y_4115_;
v___y_4097_ = v___x_4155_;
goto v___jp_4083_;
}
else
{
lean_object* v_val_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
v_val_4156_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4154_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_val_4156_);
lean_dec(v___x_4154_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_val_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
v___y_4084_ = v___y_4117_;
v___y_4085_ = v___y_4113_;
v___y_4086_ = v_arr_4150_;
v___y_4087_ = v___y_4120_;
v___y_4088_ = v___y_4114_;
v___y_4089_ = v___y_4119_;
v___y_4090_ = v___x_4149_;
v___y_4091_ = v___x_4153_;
v___y_4092_ = v_loc_x3f_4112_;
v___y_4093_ = v___x_4152_;
v___y_4094_ = v___y_4116_;
v___y_4095_ = v___y_4118_;
v___y_4096_ = v___y_4115_;
v___y_4097_ = v___x_4161_;
goto v___jp_4083_;
}
}
}
}
}
}
v___jp_4007_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
lean_inc_ref(v___y_4012_);
v___x_4030_ = l_Array_append___redArg(v___y_4012_, v___y_4029_);
lean_dec_ref(v___y_4029_);
lean_inc_n(v___y_4013_, 2);
lean_inc_n(v___y_4024_, 9);
v___x_4031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4031_, 0, v___y_4024_);
lean_ctor_set(v___x_4031_, 1, v___y_4013_);
lean_ctor_set(v___x_4031_, 2, v___x_4030_);
lean_inc(v___y_4011_);
v___x_4032_ = l_Lean_Syntax_node3(v___y_4024_, v___y_4011_, v___y_4022_, v___x_4031_, v___y_4021_);
v___x_4033_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__2));
v___x_4034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___y_4024_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalParen___regBuiltin_Lean_Elab_Tactic_Conv_evalParen__1___closed__0));
v___x_4036_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__11));
v___x_4037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___y_4024_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConvSeqBracketed___lam__2___closed__21));
v___x_4039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___y_4024_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = l_Lean_Syntax_node3(v___y_4024_, v___x_4035_, v___x_4037_, v___y_4025_, v___x_4039_);
v___x_4041_ = l_Lean_Syntax_node3(v___y_4024_, v___y_4013_, v___x_4032_, v___x_4034_, v___x_4040_);
lean_inc(v___y_4010_);
v___x_4042_ = l_Lean_Syntax_node1(v___y_4024_, v___y_4010_, v___x_4041_);
lean_inc(v___y_4023_);
v___x_4043_ = l_Lean_Syntax_node1(v___y_4024_, v___y_4023_, v___x_4042_);
v___x_4044_ = l_Lean_Syntax_node5(v___y_4024_, v___x_4006_, v___y_4019_, v___y_4014_, v___y_4017_, v___y_4020_, v___x_4043_);
v___x_4045_ = l_Lean_Elab_Tactic_evalTactic(v___x_4044_, v___y_4009_, v___y_4016_, v___y_4028_, v___y_4027_, v___y_4008_, v___y_4026_, v___y_4018_, v___y_4015_);
return v___x_4045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalConv___boxed(lean_object* v_stx_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Lean_Elab_Tactic_Conv_evalConv(v_stx_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1(){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4191_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4192_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalConv___closed__1));
v___x_4193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1));
v___x_4194_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalConv___boxed), 10, 0);
v___x_4195_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4191_, v___x_4192_, v___x_4193_, v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___boxed(lean_object* v_a_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1();
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3(){
_start:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv__1___closed__1));
v___x_4225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___closed__6));
v___x_4226_ = l_Lean_addBuiltinDeclarationRanges(v___x_4224_, v___x_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3___boxed(lean_object* v_a_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalConv___regBuiltin_Lean_Elab_Tactic_Conv_evalConv_declRange__3();
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst(lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_Elab_Tactic_evalFirst(v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFirst___boxed(lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_Lean_Elab_Tactic_Conv_evalFirst(v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
lean_dec(v_a_4248_);
lean_dec_ref(v_a_4247_);
lean_dec(v_a_4246_);
lean_dec_ref(v_a_4245_);
lean_dec(v_a_4244_);
lean_dec_ref(v_a_4243_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
lean_dec(v_a_4240_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1(){
_start:
{
lean_object* v___f_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___f_4267_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__0));
v___x_4268_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__2));
v___x_4270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4));
v___x_4271_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4268_, v___x_4269_, v___x_4270_, v___f_4267_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___boxed(lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1();
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3(){
_start:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst__1___closed__4));
v___x_4301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___closed__6));
v___x_4302_ = l_Lean_addBuiltinDeclarationRanges(v___x_4300_, v___x_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3___boxed(lean_object* v_a_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l___private_Lean_Elab_Tactic_Conv_Basic_0__Lean_Elab_Tactic_Conv_evalFirst___regBuiltin_Lean_Elab_Tactic_Conv_evalFirst_declRange__3();
return v_res_4304_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BuiltinTactic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
