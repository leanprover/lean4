// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Split
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.CasesMatch Lean.Meta.Tactic.Grind.SearchM
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__1;
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7;
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprSplitStatus;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8;
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_beqSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_54____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Meta_Grind_isIte(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_reprSplitStatus___closed__2____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
lean_object* l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_beqSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_54_(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_updateSplitArgPosMap_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedSplitStatus;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__0;
lean_object* l_Lean_Meta_Grind_casesMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Meta_Grind_splitNext___lam__9___closed__1;
uint8_t l_Lean_Meta_Grind_Goal_isCongruent(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_reprSplitStatus___closed__4____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
static lean_object* l_Lean_Meta_Grind_reprSplitStatus___closed__1____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reprSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_168____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
lean_object* l_Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateEtaStruct_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13;
static lean_object* l_Lean_Meta_Grind_reprSplitStatus___closed__7____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object*);
static lean_object* l_Lean_Meta_Grind_splitNext___lam__9___closed__0;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_reprSplitStatus___closed__8____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14;
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0;
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqSplitStatus;
lean_object* l_Lean_Meta_Grind_mkChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_reprSplitStatus___closed__6____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3;
static lean_object* l_Lean_Meta_Grind_instBEqSplitStatus___closed__0;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object**);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17;
lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_reprSplitStatus___closed__5____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
static lean_object* l_Lean_Meta_Grind_instReprSplitStatus___closed__0;
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGoal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15;
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_reprSplitStatus___closed__3____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reprSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6;
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___Lean_Meta_Grind_splitNext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMorallyIff(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1;
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3;
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isDIte(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_reprSplitStatus___closed__0____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSplitStatus() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_beqSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_54_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_19; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_19 = lean_nat_dec_eq(x_11, x_14);
if (x_19 == 0)
{
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
if (x_12 == 0)
{
if (x_15 == 0)
{
x_17 = x_19;
goto block_18;
}
else
{
uint8_t x_21; 
x_21 = lean_unbox(x_20);
return x_21;
}
}
else
{
if (x_15 == 0)
{
uint8_t x_22; 
x_22 = lean_unbox(x_20);
return x_22;
}
else
{
x_17 = x_19;
goto block_18;
}
}
}
block_18:
{
if (x_17 == 0)
{
return x_17;
}
else
{
if (x_13 == 0)
{
if (x_16 == 0)
{
return x_17;
}
else
{
return x_13;
}
}
else
{
return x_16;
}
}
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_beqSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_54____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_beqSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_54_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instBEqSplitStatus___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_beqSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_54____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instBEqSplitStatus() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instBEqSplitStatus___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reprSplitStatus___closed__0____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.SplitStatus.notReady", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reprSplitStatus___closed__1____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_reprSplitStatus___closed__0____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reprSplitStatus___closed__2____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.SplitStatus.resolved", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reprSplitStatus___closed__3____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_reprSplitStatus___closed__2____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reprSplitStatus___closed__4____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reprSplitStatus___closed__5____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reprSplitStatus___closed__6____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.SplitStatus.ready", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reprSplitStatus___closed__7____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_reprSplitStatus___closed__6____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_reprSplitStatus___closed__8____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Grind_reprSplitStatus___closed__7____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reprSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(1024u);
x_20 = lean_nat_dec_le(x_19, x_2);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Meta_Grind_reprSplitStatus___closed__4____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_11 = x_21;
goto block_18;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_reprSplitStatus___closed__5____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_11 = x_22;
goto block_18;
}
}
case 1:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_unsigned_to_nat(1024u);
x_24 = lean_nat_dec_le(x_23, x_2);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Grind_reprSplitStatus___closed__4____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_3 = x_25;
goto block_10;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Grind_reprSplitStatus___closed__5____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_3 = x_26;
goto block_10;
}
}
default: 
{
lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_48; uint8_t x_49; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
x_48 = lean_unsigned_to_nat(1024u);
x_49 = lean_nat_dec_le(x_48, x_2);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Lean_Meta_Grind_reprSplitStatus___closed__4____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_30 = x_50;
goto block_47;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_Meta_Grind_reprSplitStatus___closed__5____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_30 = x_51;
goto block_47;
}
block_47:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_31 = lean_box(1);
x_32 = l_Lean_Meta_Grind_reprSplitStatus___closed__8____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_33 = l_Nat_reprFast(x_27);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
x_37 = l_Bool_repr___redArg(x_28);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
x_40 = l_Bool_repr___redArg(x_29);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = l_Repr_addAppParen(x_44, x_2);
return x_46;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_Lean_Meta_Grind_reprSplitStatus___closed__1____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = l_Repr_addAppParen(x_7, x_2);
return x_9;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_Lean_Meta_Grind_reprSplitStatus___closed__3____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reprSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_168____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_reprSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reprSplitStatus____x40_Lean_Meta_Tactic_Grind_Split___hyg_168____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprSplitStatus() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instReprSplitStatus___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_33; 
lean_inc(x_1);
x_33 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_3, x_4, x_5, x_36);
x_7 = x_37;
goto block_32;
}
else
{
lean_dec(x_1);
x_7 = x_33;
goto block_32;
}
}
else
{
lean_dec(x_1);
x_7 = x_33;
goto block_32;
}
block_32:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unbox(x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 1, x_15);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_unbox(x_8);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
x_20 = lean_unbox(x_8);
lean_dec(x_8);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_7, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
return x_7;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_7, 0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_7);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(x_1, x_2, x_4, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_35; 
lean_inc(x_1);
x_35 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_box(1);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_39, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_39, 0, x_50);
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_dec(x_39);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_39);
if (x_54 == 0)
{
return x_39;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_39);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_dec(x_35);
x_59 = l_Lean_Meta_Grind_isEqTrue___redArg(x_2, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_5, x_6, x_7, x_62);
x_9 = x_63;
goto block_34;
}
else
{
lean_dec(x_3);
x_9 = x_59;
goto block_34;
}
}
else
{
lean_dec(x_3);
x_9 = x_59;
goto block_34;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_35);
if (x_64 == 0)
{
return x_35;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_35, 0);
x_66 = lean_ctor_get(x_35, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_35);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
block_34:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_unbox(x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 1, x_17);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_unbox(x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_22 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 1, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_9, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(x_1, x_2, x_3, x_4, x_6, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_35; 
lean_inc(x_1);
x_35 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_box(1);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_5, x_6, x_7, x_52);
x_9 = x_53;
goto block_34;
}
else
{
lean_dec(x_3);
x_9 = x_49;
goto block_34;
}
}
else
{
lean_dec(x_3);
x_9 = x_49;
goto block_34;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_39);
if (x_54 == 0)
{
return x_39;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_39);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_35);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_35, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_35, 0, x_60);
return x_35;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 1);
lean_inc(x_61);
lean_dec(x_35);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_35);
if (x_64 == 0)
{
return x_35;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_35, 0);
x_66 = lean_ctor_get(x_35, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_35);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
block_34:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_unbox(x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 1, x_17);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_unbox(x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_22 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 1, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_9, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(x_1, x_2, x_3, x_4, x_6, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_34; lean_object* x_49; lean_object* x_53; lean_object* x_74; lean_object* x_89; 
lean_inc(x_1);
x_89 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_4, x_5, x_6, x_7, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
uint8_t x_96; 
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_93, 0);
lean_dec(x_97);
x_98 = lean_box(1);
lean_ctor_set(x_93, 0, x_98);
return x_93;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_dec(x_93);
x_100 = lean_box(1);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_93, 1);
lean_inc(x_102);
lean_dec(x_93);
lean_inc(x_2);
x_103 = l_Lean_Meta_Grind_isEqTrue___redArg(x_2, x_4, x_5, x_6, x_7, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
x_34 = x_103;
goto block_48;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
lean_inc(x_3);
x_107 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_5, x_6, x_7, x_106);
x_34 = x_107;
goto block_48;
}
}
else
{
x_34 = x_103;
goto block_48;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_93);
if (x_108 == 0)
{
return x_93;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_93, 0);
x_110 = lean_ctor_get(x_93, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_93);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_1);
x_112 = lean_ctor_get(x_89, 1);
lean_inc(x_112);
lean_dec(x_89);
lean_inc(x_2);
x_113 = l_Lean_Meta_Grind_isEqTrue___redArg(x_2, x_4, x_5, x_6, x_7, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
x_74 = x_113;
goto block_88;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
lean_inc(x_3);
x_117 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_5, x_6, x_7, x_116);
x_74 = x_117;
goto block_88;
}
}
else
{
x_74 = x_113;
goto block_88;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_89);
if (x_118 == 0)
{
return x_89;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_89, 0);
x_120 = lean_ctor_get(x_89, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_89);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_33:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unbox(x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
x_21 = lean_unbox(x_14);
lean_dec(x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_21);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_unbox(x_14);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
x_26 = lean_unbox(x_14);
lean_dec(x_14);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 1, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_14);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_9 = x_28;
goto block_12;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
block_48:
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_dec(x_3);
x_13 = x_38;
goto block_33;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_5, x_6, x_7, x_41);
x_13 = x_42;
goto block_33;
}
}
else
{
lean_dec(x_3);
x_13 = x_38;
goto block_33;
}
}
else
{
lean_object* x_43; 
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_9 = x_43;
goto block_12;
}
}
else
{
uint8_t x_44; 
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
block_73:
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_53, 0);
lean_dec(x_57);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_unbox(x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_60);
x_61 = lean_unbox(x_54);
lean_dec(x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*1 + 1, x_61);
lean_ctor_set(x_53, 0, x_59);
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_unbox(x_54);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_65);
x_66 = lean_unbox(x_54);
lean_dec(x_54);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 1, x_66);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
else
{
lean_object* x_68; 
lean_dec(x_54);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_dec(x_53);
x_49 = x_68;
goto block_52;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_53);
if (x_69 == 0)
{
return x_53;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_53, 0);
x_71 = lean_ctor_get(x_53, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_53);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_88:
{
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_5, x_6, x_7, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_dec(x_3);
x_53 = x_78;
goto block_73;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_5, x_6, x_7, x_81);
x_53 = x_82;
goto block_73;
}
}
else
{
lean_dec(x_3);
x_53 = x_78;
goto block_73;
}
}
else
{
lean_object* x_83; 
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_dec(x_74);
x_49 = x_83;
goto block_52;
}
}
else
{
uint8_t x_84; 
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_74);
if (x_84 == 0)
{
return x_74;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_74, 0);
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_74);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(x_1, x_2, x_3, x_4, x_6, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; uint8_t x_25; 
x_25 = lean_usize_dec_eq(x_3, x_4);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = lean_apply_12(x_1, x_5, x_27, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_21 = x_29;
goto block_24;
}
case 1:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_31 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(x_1, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_30);
x_21 = x_31;
goto block_24;
}
default: 
{
x_15 = x_5;
x_16 = x_14;
goto block_20;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_14);
return x_32;
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_14 = x_16;
goto _start;
}
block_24:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_15 = x_22;
x_16 = x_23;
goto block_20;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_4, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_fget(x_2, x_4);
x_19 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = lean_apply_12(x_1, x_5, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_4 = x_24;
x_5 = x_21;
x_14 = x_22;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_13);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_15, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(x_1, x_13, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(x_1, x_23, x_24, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (x_3 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_get(x_6, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Expr_isApp(x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_box(x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
uint8_t x_20; lean_object* x_21; 
x_20 = l_Lean_Meta_Grind_Goal_isCongruent(x_17, x_1, x_4);
x_21 = lean_box(x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = l_Lean_Expr_isApp(x_4);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_1);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lean_Meta_Grind_Goal_isCongruent(x_22, x_1, x_4);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_1);
x_30 = lean_box(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_14);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isApp(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_st_ref_get(x_2, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 13);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_16, 4);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(x_11);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed), 14, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(x_20, x_18, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
lean_dec(x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentHashMap_foldlM___at_____private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit___lam__0(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot perform case-split on ", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", unexpected type", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split resolved: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Or", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_19; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_308; uint8_t x_309; 
lean_inc(x_1);
x_308 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_323; uint8_t x_324; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = lean_ctor_get(x_308, 1);
x_323 = l_Lean_Expr_cleanupAnnotations(x_310);
x_324 = l_Lean_Expr_isApp(x_323);
if (x_324 == 0)
{
lean_dec(x_323);
lean_free_object(x_308);
x_312 = x_2;
x_313 = x_3;
x_314 = x_4;
x_315 = x_5;
x_316 = x_6;
x_317 = x_7;
x_318 = x_8;
x_319 = x_9;
goto block_322;
}
else
{
lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
x_326 = l_Lean_Expr_appFnCleanup___redArg(x_323);
x_327 = l_Lean_Expr_isApp(x_326);
if (x_327 == 0)
{
lean_dec(x_326);
lean_dec(x_325);
lean_free_object(x_308);
x_312 = x_2;
x_313 = x_3;
x_314 = x_4;
x_315 = x_5;
x_316 = x_6;
x_317 = x_7;
x_318 = x_8;
x_319 = x_9;
goto block_322;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
x_329 = l_Lean_Expr_appFnCleanup___redArg(x_326);
x_330 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13;
x_331 = l_Lean_Expr_isConstOf(x_329, x_330);
if (x_331 == 0)
{
lean_object* x_332; uint8_t x_333; 
x_332 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15;
x_333 = l_Lean_Expr_isConstOf(x_329, x_332);
if (x_333 == 0)
{
uint8_t x_334; 
x_334 = l_Lean_Expr_isApp(x_329);
if (x_334 == 0)
{
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_325);
lean_free_object(x_308);
x_312 = x_2;
x_313 = x_3;
x_314 = x_4;
x_315 = x_5;
x_316 = x_6;
x_317 = x_7;
x_318 = x_8;
x_319 = x_9;
goto block_322;
}
else
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_335 = l_Lean_Expr_appFnCleanup___redArg(x_329);
x_336 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17;
x_337 = l_Lean_Expr_isConstOf(x_335, x_336);
lean_dec(x_335);
if (x_337 == 0)
{
lean_dec(x_328);
lean_dec(x_325);
lean_free_object(x_308);
x_312 = x_2;
x_313 = x_3;
x_314 = x_4;
x_315 = x_5;
x_316 = x_6;
x_317 = x_7;
x_318 = x_8;
x_319 = x_9;
goto block_322;
}
else
{
uint8_t x_338; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_338 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_328);
lean_dec(x_325);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_339 = lean_unsigned_to_nat(2u);
x_340 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set_uint8(x_340, sizeof(void*)*1, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*1 + 1, x_338);
lean_ctor_set(x_308, 0, x_340);
return x_308;
}
else
{
lean_object* x_341; 
lean_free_object(x_308);
x_341 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(x_1, x_328, x_325, x_2, x_4, x_8, x_9, x_311);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_341;
}
}
}
}
else
{
lean_object* x_342; 
lean_dec(x_329);
lean_free_object(x_308);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_342 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(x_1, x_328, x_325, x_2, x_4, x_8, x_9, x_311);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_342;
}
}
else
{
lean_object* x_343; 
lean_dec(x_329);
lean_free_object(x_308);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_343 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(x_1, x_328, x_325, x_2, x_4, x_8, x_9, x_311);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_343;
}
}
}
block_322:
{
uint8_t x_320; 
x_320 = l_Lean_Meta_Grind_isIte(x_1);
if (x_320 == 0)
{
uint8_t x_321; 
x_321 = l_Lean_Meta_Grind_isDIte(x_1);
x_130 = x_313;
x_131 = x_316;
x_132 = x_319;
x_133 = x_314;
x_134 = x_318;
x_135 = x_315;
x_136 = x_311;
x_137 = x_312;
x_138 = x_317;
x_139 = x_321;
goto block_307;
}
else
{
x_130 = x_313;
x_131 = x_316;
x_132 = x_319;
x_133 = x_314;
x_134 = x_318;
x_135 = x_315;
x_136 = x_311;
x_137 = x_312;
x_138 = x_317;
x_139 = x_320;
goto block_307;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_357; uint8_t x_358; 
x_344 = lean_ctor_get(x_308, 0);
x_345 = lean_ctor_get(x_308, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_308);
x_357 = l_Lean_Expr_cleanupAnnotations(x_344);
x_358 = l_Lean_Expr_isApp(x_357);
if (x_358 == 0)
{
lean_dec(x_357);
x_346 = x_2;
x_347 = x_3;
x_348 = x_4;
x_349 = x_5;
x_350 = x_6;
x_351 = x_7;
x_352 = x_8;
x_353 = x_9;
goto block_356;
}
else
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; 
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
x_360 = l_Lean_Expr_appFnCleanup___redArg(x_357);
x_361 = l_Lean_Expr_isApp(x_360);
if (x_361 == 0)
{
lean_dec(x_360);
lean_dec(x_359);
x_346 = x_2;
x_347 = x_3;
x_348 = x_4;
x_349 = x_5;
x_350 = x_6;
x_351 = x_7;
x_352 = x_8;
x_353 = x_9;
goto block_356;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
x_363 = l_Lean_Expr_appFnCleanup___redArg(x_360);
x_364 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13;
x_365 = l_Lean_Expr_isConstOf(x_363, x_364);
if (x_365 == 0)
{
lean_object* x_366; uint8_t x_367; 
x_366 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15;
x_367 = l_Lean_Expr_isConstOf(x_363, x_366);
if (x_367 == 0)
{
uint8_t x_368; 
x_368 = l_Lean_Expr_isApp(x_363);
if (x_368 == 0)
{
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_359);
x_346 = x_2;
x_347 = x_3;
x_348 = x_4;
x_349 = x_5;
x_350 = x_6;
x_351 = x_7;
x_352 = x_8;
x_353 = x_9;
goto block_356;
}
else
{
lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_369 = l_Lean_Expr_appFnCleanup___redArg(x_363);
x_370 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17;
x_371 = l_Lean_Expr_isConstOf(x_369, x_370);
lean_dec(x_369);
if (x_371 == 0)
{
lean_dec(x_362);
lean_dec(x_359);
x_346 = x_2;
x_347 = x_3;
x_348 = x_4;
x_349 = x_5;
x_350 = x_6;
x_351 = x_7;
x_352 = x_8;
x_353 = x_9;
goto block_356;
}
else
{
uint8_t x_372; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_372 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_362);
lean_dec(x_359);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_373 = lean_unsigned_to_nat(2u);
x_374 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*1, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*1 + 1, x_372);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_345);
return x_375;
}
else
{
lean_object* x_376; 
x_376 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIffStatus___redArg(x_1, x_362, x_359, x_2, x_4, x_8, x_9, x_345);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_376;
}
}
}
}
else
{
lean_object* x_377; 
lean_dec(x_363);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_377 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDisjunctStatus___redArg(x_1, x_362, x_359, x_2, x_4, x_8, x_9, x_345);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_377;
}
}
else
{
lean_object* x_378; 
lean_dec(x_363);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_378 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkConjunctStatus___redArg(x_1, x_362, x_359, x_2, x_4, x_8, x_9, x_345);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_378;
}
}
}
block_356:
{
uint8_t x_354; 
x_354 = l_Lean_Meta_Grind_isIte(x_1);
if (x_354 == 0)
{
uint8_t x_355; 
x_355 = l_Lean_Meta_Grind_isDIte(x_1);
x_130 = x_347;
x_131 = x_350;
x_132 = x_353;
x_133 = x_348;
x_134 = x_352;
x_135 = x_349;
x_136 = x_345;
x_137 = x_346;
x_138 = x_351;
x_139 = x_355;
goto block_307;
}
else
{
x_130 = x_347;
x_131 = x_350;
x_132 = x_353;
x_133 = x_348;
x_134 = x_352;
x_135 = x_349;
x_136 = x_345;
x_137 = x_346;
x_138 = x_351;
x_139 = x_354;
goto block_307;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
block_129:
{
uint8_t x_32; 
x_32 = l_Lean_Expr_isFVar(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; 
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_1);
x_35 = lean_infer_type(x_1, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_38 = l_Lean_Meta_whnfD(x_36, x_27, x_28, x_29, x_30, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_getAppFn(x_39);
if (lean_obj_tag(x_41) == 4)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_getConstInfo___at_____private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateEtaStruct_spec__0___redArg(x_42, x_27, x_28, x_29, x_30, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 5)
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_45, 4);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_45, sizeof(void*)*6);
lean_dec(x_45);
x_50 = l_List_lengthTR___redArg(x_48);
lean_dec(x_48);
x_51 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1 + 1, x_23);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_ctor_get(x_45, 4);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_45, sizeof(void*)*6);
lean_dec(x_45);
x_55 = l_List_lengthTR___redArg(x_53);
lean_dec(x_53);
x_56 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1 + 1, x_23);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_44);
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_dec(x_43);
x_59 = l_Lean_Meta_Grind_getConfig___redArg(x_25, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_60, sizeof(void*)*6 + 11);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_15 = x_62;
goto block_18;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_59, 1);
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
x_66 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1;
x_67 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_67);
lean_ctor_set(x_59, 0, x_66);
x_68 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_indentExpr(x_39);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Meta_Grind_reportIssue(x_73, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_64);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_15 = x_75;
goto block_18;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_59, 1);
lean_inc(x_76);
lean_dec(x_59);
x_77 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1;
x_78 = l_Lean_MessageData_ofExpr(x_1);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_indentExpr(x_39);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_Meta_Grind_reportIssue(x_85, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_76);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_15 = x_87;
goto block_18;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_43);
if (x_88 == 0)
{
return x_43;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_43, 0);
x_90 = lean_ctor_get(x_43, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_43);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_41);
x_92 = l_Lean_Meta_Grind_getConfig___redArg(x_25, x_40);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_93, sizeof(void*)*6 + 11);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_19 = x_95;
goto block_22;
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_97 = lean_ctor_get(x_92, 1);
x_98 = lean_ctor_get(x_92, 0);
lean_dec(x_98);
x_99 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1;
x_100 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_92, 7);
lean_ctor_set(x_92, 1, x_100);
lean_ctor_set(x_92, 0, x_99);
x_101 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_92);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_indentExpr(x_39);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Meta_Grind_reportIssue(x_106, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_97);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_19 = x_108;
goto block_22;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
lean_dec(x_92);
x_110 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1;
x_111 = l_Lean_MessageData_ofExpr(x_1);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_indentExpr(x_39);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Meta_Grind_reportIssue(x_118, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_109);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_19 = x_120;
goto block_22;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_38);
if (x_121 == 0)
{
return x_38;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_38, 0);
x_123 = lean_ctor_get(x_38, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_38);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_35);
if (x_125 == 0)
{
return x_35;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_35, 0);
x_127 = lean_ctor_get(x_35, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_35);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
block_307:
{
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = l_Lean_Meta_Grind_isResolvedCaseSplit___redArg(x_1, x_137, x_136);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
lean_inc(x_132);
lean_inc(x_134);
lean_inc(x_138);
lean_inc(x_131);
lean_inc(x_135);
lean_inc(x_133);
lean_inc(x_130);
lean_inc(x_137);
lean_inc(x_1);
x_144 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_isCongrToPrevSplit(x_1, x_137, x_130, x_133, x_135, x_131, x_138, x_134, x_132, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_st_ref_get(x_132, x_147);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_ctor_get(x_148, 1);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_Meta_isMatcherAppCore_x3f(x_152, x_1);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
lean_free_object(x_148);
x_154 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_154) == 4)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec(x_154);
lean_inc(x_132);
lean_inc(x_134);
lean_inc(x_138);
lean_inc(x_131);
x_156 = l_Lean_Meta_isInductivePredicate_x3f(x_155, x_131, x_138, x_134, x_132, x_151);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; uint8_t x_159; 
lean_dec(x_137);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_unbox(x_145);
lean_dec(x_145);
x_23 = x_159;
x_24 = x_130;
x_25 = x_133;
x_26 = x_135;
x_27 = x_131;
x_28 = x_138;
x_29 = x_134;
x_30 = x_132;
x_31 = x_158;
goto block_129;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_156, 1);
lean_inc(x_160);
lean_dec(x_156);
x_161 = lean_ctor_get(x_157, 0);
lean_inc(x_161);
lean_dec(x_157);
lean_inc(x_1);
x_162 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_137, x_133, x_134, x_132, x_160);
lean_dec(x_137);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
lean_dec(x_161);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_unbox(x_145);
lean_dec(x_145);
x_23 = x_166;
x_24 = x_130;
x_25 = x_133;
x_26 = x_135;
x_27 = x_131;
x_28 = x_138;
x_29 = x_134;
x_30 = x_132;
x_31 = x_165;
goto block_129;
}
else
{
uint8_t x_167; 
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_162);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_162, 0);
lean_dec(x_168);
x_169 = lean_ctor_get(x_161, 4);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_161, sizeof(void*)*6);
lean_dec(x_161);
x_171 = l_List_lengthTR___redArg(x_169);
lean_dec(x_169);
x_172 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_170);
x_173 = lean_unbox(x_145);
lean_dec(x_145);
lean_ctor_set_uint8(x_172, sizeof(void*)*1 + 1, x_173);
lean_ctor_set(x_162, 0, x_172);
return x_162;
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_162, 1);
lean_inc(x_174);
lean_dec(x_162);
x_175 = lean_ctor_get(x_161, 4);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_161, sizeof(void*)*6);
lean_dec(x_161);
x_177 = l_List_lengthTR___redArg(x_175);
lean_dec(x_175);
x_178 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_176);
x_179 = lean_unbox(x_145);
lean_dec(x_145);
lean_ctor_set_uint8(x_178, sizeof(void*)*1 + 1, x_179);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_174);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_161);
lean_dec(x_145);
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_162);
if (x_181 == 0)
{
return x_162;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_162, 0);
x_183 = lean_ctor_get(x_162, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_162);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_145);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_156);
if (x_185 == 0)
{
return x_156;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_156, 0);
x_187 = lean_ctor_get(x_156, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_156);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_154);
lean_dec(x_137);
x_189 = lean_unbox(x_145);
lean_dec(x_145);
x_23 = x_189;
x_24 = x_130;
x_25 = x_133;
x_26 = x_135;
x_27 = x_131;
x_28 = x_138;
x_29 = x_134;
x_30 = x_132;
x_31 = x_151;
goto block_129;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_190 = lean_ctor_get(x_153, 0);
lean_inc(x_190);
lean_dec(x_153);
x_191 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_190);
lean_dec(x_190);
x_192 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_unbox(x_145);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_193);
x_194 = lean_unbox(x_145);
lean_dec(x_145);
lean_ctor_set_uint8(x_192, sizeof(void*)*1 + 1, x_194);
lean_ctor_set(x_148, 0, x_192);
return x_148;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_148, 0);
x_196 = lean_ctor_get(x_148, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_148);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
lean_dec(x_195);
x_198 = l_Lean_Meta_isMatcherAppCore_x3f(x_197, x_1);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
x_199 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_199) == 4)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_dec(x_199);
lean_inc(x_132);
lean_inc(x_134);
lean_inc(x_138);
lean_inc(x_131);
x_201 = l_Lean_Meta_isInductivePredicate_x3f(x_200, x_131, x_138, x_134, x_132, x_196);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; uint8_t x_204; 
lean_dec(x_137);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_unbox(x_145);
lean_dec(x_145);
x_23 = x_204;
x_24 = x_130;
x_25 = x_133;
x_26 = x_135;
x_27 = x_131;
x_28 = x_138;
x_29 = x_134;
x_30 = x_132;
x_31 = x_203;
goto block_129;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
lean_dec(x_201);
x_206 = lean_ctor_get(x_202, 0);
lean_inc(x_206);
lean_dec(x_202);
lean_inc(x_1);
x_207 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_137, x_133, x_134, x_132, x_205);
lean_dec(x_137);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
lean_dec(x_206);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_dec(x_207);
x_211 = lean_unbox(x_145);
lean_dec(x_145);
x_23 = x_211;
x_24 = x_130;
x_25 = x_133;
x_26 = x_135;
x_27 = x_131;
x_28 = x_138;
x_29 = x_134;
x_30 = x_132;
x_31 = x_210;
goto block_129;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; 
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_213 = x_207;
} else {
 lean_dec_ref(x_207);
 x_213 = lean_box(0);
}
x_214 = lean_ctor_get(x_206, 4);
lean_inc(x_214);
x_215 = lean_ctor_get_uint8(x_206, sizeof(void*)*6);
lean_dec(x_206);
x_216 = l_List_lengthTR___redArg(x_214);
lean_dec(x_214);
x_217 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set_uint8(x_217, sizeof(void*)*1, x_215);
x_218 = lean_unbox(x_145);
lean_dec(x_145);
lean_ctor_set_uint8(x_217, sizeof(void*)*1 + 1, x_218);
if (lean_is_scalar(x_213)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_213;
}
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_212);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_206);
lean_dec(x_145);
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_220 = lean_ctor_get(x_207, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_207, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_222 = x_207;
} else {
 lean_dec_ref(x_207);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_145);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_224 = lean_ctor_get(x_201, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_201, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_226 = x_201;
} else {
 lean_dec_ref(x_201);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
uint8_t x_228; 
lean_dec(x_199);
lean_dec(x_137);
x_228 = lean_unbox(x_145);
lean_dec(x_145);
x_23 = x_228;
x_24 = x_130;
x_25 = x_133;
x_26 = x_135;
x_27 = x_131;
x_28 = x_138;
x_29 = x_134;
x_30 = x_132;
x_31 = x_196;
goto block_129;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_233; lean_object* x_234; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_229 = lean_ctor_get(x_198, 0);
lean_inc(x_229);
lean_dec(x_198);
x_230 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_229);
lean_dec(x_229);
x_231 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_231, 0, x_230);
x_232 = lean_unbox(x_145);
lean_ctor_set_uint8(x_231, sizeof(void*)*1, x_232);
x_233 = lean_unbox(x_145);
lean_dec(x_145);
lean_ctor_set_uint8(x_231, sizeof(void*)*1 + 1, x_233);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_196);
return x_234;
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_145);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_144);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_144, 0);
lean_dec(x_236);
x_237 = lean_box(0);
lean_ctor_set(x_144, 0, x_237);
return x_144;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_144, 1);
lean_inc(x_238);
lean_dec(x_144);
x_239 = lean_box(0);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_241 = !lean_is_exclusive(x_144);
if (x_241 == 0)
{
return x_144;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_144, 0);
x_243 = lean_ctor_get(x_144, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_144);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
else
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_140);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_140, 1);
x_247 = lean_ctor_get(x_140, 0);
lean_dec(x_247);
x_248 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9;
x_249 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_248, x_134, x_246);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_unbox(x_250);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; 
lean_free_object(x_140);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_dec(x_249);
x_11 = x_252;
goto block_14;
}
else
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_249);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_249, 1);
x_255 = lean_ctor_get(x_249, 0);
lean_dec(x_255);
x_256 = l_Lean_Meta_Grind_updateLastTag(x_137, x_130, x_133, x_135, x_131, x_138, x_134, x_132, x_254);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_137);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_258 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11;
x_259 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_249, 7);
lean_ctor_set(x_249, 1, x_259);
lean_ctor_set(x_249, 0, x_258);
x_260 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_ctor_set_tag(x_140, 7);
lean_ctor_set(x_140, 1, x_260);
lean_ctor_set(x_140, 0, x_249);
x_261 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_248, x_140, x_131, x_138, x_134, x_132, x_257);
lean_dec(x_132);
lean_dec(x_134);
lean_dec(x_138);
lean_dec(x_131);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec(x_261);
x_11 = x_262;
goto block_14;
}
else
{
uint8_t x_263; 
lean_free_object(x_249);
lean_free_object(x_140);
lean_dec(x_138);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_1);
x_263 = !lean_is_exclusive(x_256);
if (x_263 == 0)
{
return x_256;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_256, 0);
x_265 = lean_ctor_get(x_256, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_256);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_249, 1);
lean_inc(x_267);
lean_dec(x_249);
x_268 = l_Lean_Meta_Grind_updateLastTag(x_137, x_130, x_133, x_135, x_131, x_138, x_134, x_132, x_267);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_137);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_270 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11;
x_271 = l_Lean_MessageData_ofExpr(x_1);
x_272 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_ctor_set_tag(x_140, 7);
lean_ctor_set(x_140, 1, x_273);
lean_ctor_set(x_140, 0, x_272);
x_274 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_248, x_140, x_131, x_138, x_134, x_132, x_269);
lean_dec(x_132);
lean_dec(x_134);
lean_dec(x_138);
lean_dec(x_131);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
x_11 = x_275;
goto block_14;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_free_object(x_140);
lean_dec(x_138);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_1);
x_276 = lean_ctor_get(x_268, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_268, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_278 = x_268;
} else {
 lean_dec_ref(x_268);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_280 = lean_ctor_get(x_140, 1);
lean_inc(x_280);
lean_dec(x_140);
x_281 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9;
x_282 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_281, x_134, x_280);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_unbox(x_283);
lean_dec(x_283);
if (x_284 == 0)
{
lean_object* x_285; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_1);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
x_11 = x_285;
goto block_14;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_282, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_287 = x_282;
} else {
 lean_dec_ref(x_282);
 x_287 = lean_box(0);
}
x_288 = l_Lean_Meta_Grind_updateLastTag(x_137, x_130, x_133, x_135, x_131, x_138, x_134, x_132, x_286);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_137);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
lean_dec(x_288);
x_290 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11;
x_291 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_287)) {
 x_292 = lean_alloc_ctor(7, 2, 0);
} else {
 x_292 = x_287;
 lean_ctor_set_tag(x_292, 7);
}
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_281, x_294, x_131, x_138, x_134, x_132, x_289);
lean_dec(x_132);
lean_dec(x_134);
lean_dec(x_138);
lean_dec(x_131);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
x_11 = x_296;
goto block_14;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_287);
lean_dec(x_138);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_1);
x_297 = lean_ctor_get(x_288, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_288, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_299 = x_288;
} else {
 lean_dec_ref(x_288);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_131);
lean_dec(x_130);
x_301 = lean_unsigned_to_nat(1u);
x_302 = l_Lean_Expr_getAppNumArgs(x_1);
x_303 = lean_nat_sub(x_302, x_301);
lean_dec(x_302);
x_304 = lean_nat_sub(x_303, x_301);
lean_dec(x_303);
x_305 = l_Lean_Expr_getRevArg_x21(x_1, x_304);
lean_dec(x_1);
x_306 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkIteCondStatus___redArg(x_305, x_137, x_133, x_134, x_132, x_136);
lean_dec(x_132);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_137);
return x_306;
}
}
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("may be irrelevant\na: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nb: ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\neq: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\narg_a: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\narg_b: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", gen: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_46; uint8_t x_234; 
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_17 = x_6;
} else {
 lean_dec_ref(x_6);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_234 = l_Lean_Expr_isApp(x_19);
if (x_234 == 0)
{
x_46 = x_234;
goto block_233;
}
else
{
uint8_t x_235; 
x_235 = l_Lean_Expr_isApp(x_21);
x_46 = x_235;
goto block_233;
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*1 + 1, x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_26);
if (lean_is_scalar(x_20)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_20;
}
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
if (lean_is_scalar(x_17)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_17;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
block_45:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = l_Lean_Expr_appFn_x21(x_37);
lean_dec(x_37);
x_40 = l_Lean_Expr_appFn_x21(x_21);
lean_dec(x_21);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
x_6 = x_43;
x_15 = x_38;
goto _start;
}
block_233:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 1, x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_21);
lean_ctor_set(x_50, 1, x_22);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_15);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_22, x_54);
lean_dec(x_22);
x_56 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0;
lean_inc(x_2);
lean_inc(x_55);
x_57 = l_List_elem___redArg(x_56, x_55, x_2);
x_58 = l_instDecidableNot___redArg(x_57);
if (x_58 == 0)
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
x_36 = x_55;
x_37 = x_19;
x_38 = x_15;
goto block_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = l_Lean_Expr_appArg_x21(x_19);
x_60 = l_Lean_Expr_appArg_x21(x_21);
lean_inc(x_60);
lean_inc(x_59);
x_61 = l_Lean_Meta_Grind_isEqv___redArg(x_59, x_60, x_7, x_15);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_61, 1);
x_66 = lean_ctor_get(x_61, 0);
lean_dec(x_66);
x_67 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
x_68 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_67, x_13, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
lean_free_object(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_46;
x_25 = x_72;
x_26 = x_55;
x_27 = x_71;
goto block_35;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 1);
x_75 = lean_ctor_get(x_68, 0);
lean_dec(x_75);
x_76 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_3);
x_78 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_77);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
x_82 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_83 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_78, 7);
lean_ctor_set(x_78, 1, x_83);
lean_ctor_set(x_78, 0, x_82);
x_84 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_84);
lean_ctor_set(x_68, 0, x_78);
x_85 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_85);
lean_ctor_set(x_61, 0, x_68);
x_86 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_61);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_MessageData_ofExpr(x_3);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_MessageData_ofExpr(x_59);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_MessageData_ofExpr(x_60);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Nat_reprFast(x_80);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_MessageData_ofFormat(x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
x_104 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_67, x_105, x_11, x_12, x_13, x_14, x_81);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_46;
x_25 = x_108;
x_26 = x_55;
x_27 = x_107;
goto block_35;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_109 = lean_ctor_get(x_78, 0);
x_110 = lean_ctor_get(x_78, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_78);
x_111 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_112 = l_Lean_MessageData_ofExpr(x_4);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_114);
lean_ctor_set(x_68, 0, x_113);
x_115 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_115);
lean_ctor_set(x_61, 0, x_68);
x_116 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_61);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_MessageData_ofExpr(x_3);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_MessageData_ofExpr(x_59);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_MessageData_ofExpr(x_60);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Nat_reprFast(x_109);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = l_Lean_MessageData_ofFormat(x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_132);
x_134 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_67, x_135, x_11, x_12, x_13, x_14, x_110);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_46;
x_25 = x_138;
x_26 = x_55;
x_27 = x_137;
goto block_35;
}
}
else
{
uint8_t x_139; 
lean_free_object(x_68);
lean_free_object(x_61);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_76);
if (x_139 == 0)
{
return x_76;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_76, 0);
x_141 = lean_ctor_get(x_76, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_76);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_68, 1);
lean_inc(x_143);
lean_dec(x_68);
x_144 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
lean_inc(x_3);
x_146 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_151 = l_Lean_MessageData_ofExpr(x_4);
if (lean_is_scalar(x_149)) {
 x_152 = lean_alloc_ctor(7, 2, 0);
} else {
 x_152 = x_149;
 lean_ctor_set_tag(x_152, 7);
}
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_155);
lean_ctor_set(x_61, 0, x_154);
x_156 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_61);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_MessageData_ofExpr(x_3);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_MessageData_ofExpr(x_59);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_MessageData_ofExpr(x_60);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Nat_reprFast(x_147);
x_171 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = l_Lean_MessageData_ofFormat(x_171);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_169);
lean_ctor_set(x_173, 1, x_172);
x_174 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_67, x_175, x_11, x_12, x_13, x_14, x_148);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_46;
x_25 = x_178;
x_26 = x_55;
x_27 = x_177;
goto block_35;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_free_object(x_61);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = lean_ctor_get(x_144, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_144, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_181 = x_144;
} else {
 lean_dec_ref(x_144);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_61, 1);
lean_inc(x_183);
lean_dec(x_61);
x_184 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
x_185 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_184, x_13, x_183);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_46;
x_25 = x_189;
x_26 = x_55;
x_27 = x_188;
goto block_35;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_191 = x_185;
} else {
 lean_dec_ref(x_185);
 x_191 = lean_box(0);
}
x_192 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
lean_inc(x_3);
x_194 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_199 = l_Lean_MessageData_ofExpr(x_4);
if (lean_is_scalar(x_197)) {
 x_200 = lean_alloc_ctor(7, 2, 0);
} else {
 x_200 = x_197;
 lean_ctor_set_tag(x_200, 7);
}
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
if (lean_is_scalar(x_191)) {
 x_202 = lean_alloc_ctor(7, 2, 0);
} else {
 x_202 = x_191;
 lean_ctor_set_tag(x_202, 7);
}
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_MessageData_ofExpr(x_5);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_MessageData_ofExpr(x_3);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_MessageData_ofExpr(x_59);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_214 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_MessageData_ofExpr(x_60);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Nat_reprFast(x_195);
x_220 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_221 = l_Lean_MessageData_ofFormat(x_220);
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_221);
x_223 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_184, x_224, x_11, x_12, x_13, x_14, x_196);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_46;
x_25 = x_227;
x_26 = x_55;
x_27 = x_226;
goto block_35;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_191);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_228 = lean_ctor_get(x_192, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_192, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_230 = x_192;
} else {
 lean_dec_ref(x_192);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
}
else
{
lean_object* x_232; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
x_232 = lean_ctor_get(x_61, 1);
lean_inc(x_232);
lean_dec(x_61);
x_36 = x_55;
x_37 = x_19;
x_38 = x_232;
goto block_45;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_46; uint8_t x_234; 
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_17 = x_6;
} else {
 lean_dec_ref(x_6);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_234 = l_Lean_Expr_isApp(x_19);
if (x_234 == 0)
{
x_46 = x_234;
goto block_233;
}
else
{
uint8_t x_235; 
x_235 = l_Lean_Expr_isApp(x_21);
x_46 = x_235;
goto block_233;
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*1 + 1, x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_26);
if (lean_is_scalar(x_20)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_20;
}
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
if (lean_is_scalar(x_17)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_17;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
block_45:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = l_Lean_Expr_appFn_x21(x_37);
lean_dec(x_37);
x_40 = l_Lean_Expr_appFn_x21(x_21);
lean_dec(x_21);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_38);
return x_44;
}
block_233:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 1, x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_21);
lean_ctor_set(x_50, 1, x_22);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_15);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_22, x_54);
lean_dec(x_22);
x_56 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0;
lean_inc(x_2);
lean_inc(x_55);
x_57 = l_List_elem___redArg(x_56, x_55, x_2);
x_58 = l_instDecidableNot___redArg(x_57);
if (x_58 == 0)
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
x_36 = x_55;
x_37 = x_19;
x_38 = x_15;
goto block_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = l_Lean_Expr_appArg_x21(x_19);
x_60 = l_Lean_Expr_appArg_x21(x_21);
lean_inc(x_60);
lean_inc(x_59);
x_61 = l_Lean_Meta_Grind_isEqv___redArg(x_59, x_60, x_7, x_15);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_61, 1);
x_66 = lean_ctor_get(x_61, 0);
lean_dec(x_66);
x_67 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
x_68 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_67, x_13, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
lean_free_object(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_72;
x_25 = x_46;
x_26 = x_55;
x_27 = x_71;
goto block_35;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 1);
x_75 = lean_ctor_get(x_68, 0);
lean_dec(x_75);
x_76 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_3);
x_78 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_77);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
x_82 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_83 = l_Lean_MessageData_ofExpr(x_4);
lean_ctor_set_tag(x_78, 7);
lean_ctor_set(x_78, 1, x_83);
lean_ctor_set(x_78, 0, x_82);
x_84 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_84);
lean_ctor_set(x_68, 0, x_78);
x_85 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_85);
lean_ctor_set(x_61, 0, x_68);
x_86 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_61);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_MessageData_ofExpr(x_3);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_MessageData_ofExpr(x_59);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_MessageData_ofExpr(x_60);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Nat_reprFast(x_80);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_MessageData_ofFormat(x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
x_104 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_67, x_105, x_11, x_12, x_13, x_14, x_81);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_108;
x_25 = x_46;
x_26 = x_55;
x_27 = x_107;
goto block_35;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_109 = lean_ctor_get(x_78, 0);
x_110 = lean_ctor_get(x_78, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_78);
x_111 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_112 = l_Lean_MessageData_ofExpr(x_4);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_114);
lean_ctor_set(x_68, 0, x_113);
x_115 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_115);
lean_ctor_set(x_61, 0, x_68);
x_116 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_61);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_MessageData_ofExpr(x_3);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_MessageData_ofExpr(x_59);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_MessageData_ofExpr(x_60);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Nat_reprFast(x_109);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = l_Lean_MessageData_ofFormat(x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_132);
x_134 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_67, x_135, x_11, x_12, x_13, x_14, x_110);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_138;
x_25 = x_46;
x_26 = x_55;
x_27 = x_137;
goto block_35;
}
}
else
{
uint8_t x_139; 
lean_free_object(x_68);
lean_free_object(x_61);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_76);
if (x_139 == 0)
{
return x_76;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_76, 0);
x_141 = lean_ctor_get(x_76, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_76);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_68, 1);
lean_inc(x_143);
lean_dec(x_68);
x_144 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
lean_inc(x_3);
x_146 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_151 = l_Lean_MessageData_ofExpr(x_4);
if (lean_is_scalar(x_149)) {
 x_152 = lean_alloc_ctor(7, 2, 0);
} else {
 x_152 = x_149;
 lean_ctor_set_tag(x_152, 7);
}
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_155);
lean_ctor_set(x_61, 0, x_154);
x_156 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_61);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_MessageData_ofExpr(x_3);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_MessageData_ofExpr(x_59);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_MessageData_ofExpr(x_60);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Nat_reprFast(x_147);
x_171 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = l_Lean_MessageData_ofFormat(x_171);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_169);
lean_ctor_set(x_173, 1, x_172);
x_174 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_67, x_175, x_11, x_12, x_13, x_14, x_148);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_178;
x_25 = x_46;
x_26 = x_55;
x_27 = x_177;
goto block_35;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_free_object(x_61);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = lean_ctor_get(x_144, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_144, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_181 = x_144;
} else {
 lean_dec_ref(x_144);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_61, 1);
lean_inc(x_183);
lean_dec(x_61);
x_184 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
x_185 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_184, x_13, x_183);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_189;
x_25 = x_46;
x_26 = x_55;
x_27 = x_188;
goto block_35;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_191 = x_185;
} else {
 lean_dec_ref(x_185);
 x_191 = lean_box(0);
}
x_192 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
lean_inc(x_3);
x_194 = l_Lean_Meta_Grind_getGeneration___redArg(x_3, x_7, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3;
x_199 = l_Lean_MessageData_ofExpr(x_4);
if (lean_is_scalar(x_197)) {
 x_200 = lean_alloc_ctor(7, 2, 0);
} else {
 x_200 = x_197;
 lean_ctor_set_tag(x_200, 7);
}
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5;
if (lean_is_scalar(x_191)) {
 x_202 = lean_alloc_ctor(7, 2, 0);
} else {
 x_202 = x_191;
 lean_ctor_set_tag(x_202, 7);
}
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_MessageData_ofExpr(x_5);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7;
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_MessageData_ofExpr(x_3);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9;
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_MessageData_ofExpr(x_59);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11;
x_214 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_MessageData_ofExpr(x_60);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13;
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Nat_reprFast(x_195);
x_220 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_221 = l_Lean_MessageData_ofFormat(x_220);
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_221);
x_223 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_184, x_224, x_11, x_12, x_13, x_14, x_196);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_unbox(x_62);
lean_dec(x_62);
x_24 = x_227;
x_25 = x_46;
x_26 = x_55;
x_27 = x_226;
goto block_35;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_191);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_228 = lean_ctor_get(x_192, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_192, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_230 = x_192;
} else {
 lean_dec_ref(x_192);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
}
else
{
lean_object* x_232; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
x_232 = lean_ctor_get(x_61, 1);
lean_inc(x_232);
lean_dec(x_61);
x_36 = x_55;
x_37 = x_19;
x_38 = x_232;
goto block_45;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_43; lean_object* x_110; 
lean_inc(x_3);
x_110 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_6, x_10, x_11, x_12);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
lean_inc(x_3);
x_114 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_6, x_10, x_11, x_113);
x_43 = x_114;
goto block_109;
}
else
{
x_43 = x_110;
goto block_109;
}
}
else
{
x_43 = x_110;
goto block_109;
}
block_42:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = l_Lean_Expr_getAppNumArgs(x_1);
x_17 = lean_box(0);
lean_inc(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_16);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(x_17, x_15, x_3, x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_13);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 1, x_13);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_21, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_34);
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
block_109:
{
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_st_ref_get(x_4, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 13);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 7);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; size_t x_65; size_t x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; 
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_ctor_get(x_50, 0);
lean_dec(x_54);
lean_inc(x_2);
lean_inc(x_1);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_50, 0, x_1);
x_55 = lean_array_get_size(x_53);
x_56 = l_Lean_Expr_hash(x_1);
x_57 = l_Lean_Expr_hash(x_2);
x_58 = lean_uint64_mix_hash(x_56, x_57);
x_59 = 32;
x_60 = lean_uint64_shift_right(x_58, x_59);
x_61 = lean_uint64_xor(x_58, x_60);
x_62 = 16;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = lean_uint64_to_usize(x_64);
x_66 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_67 = 1;
x_68 = lean_usize_sub(x_66, x_67);
x_69 = lean_usize_land(x_65, x_68);
x_70 = lean_array_uget(x_53, x_69);
lean_dec(x_53);
x_71 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_updateSplitArgPosMap_spec__5___redArg(x_50, x_70);
lean_dec(x_70);
lean_dec(x_50);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_box(0);
x_73 = lean_unbox(x_44);
lean_dec(x_44);
x_13 = x_73;
x_14 = x_51;
x_15 = x_72;
goto block_42;
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_unbox(x_44);
lean_dec(x_44);
x_13 = x_75;
x_14 = x_51;
x_15 = x_74;
goto block_42;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; size_t x_88; size_t x_89; size_t x_90; size_t x_91; size_t x_92; lean_object* x_93; lean_object* x_94; 
x_76 = lean_ctor_get(x_50, 1);
lean_inc(x_76);
lean_dec(x_50);
lean_inc(x_2);
lean_inc(x_1);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_2);
x_78 = lean_array_get_size(x_76);
x_79 = l_Lean_Expr_hash(x_1);
x_80 = l_Lean_Expr_hash(x_2);
x_81 = lean_uint64_mix_hash(x_79, x_80);
x_82 = 32;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = 16;
x_86 = lean_uint64_shift_right(x_84, x_85);
x_87 = lean_uint64_xor(x_84, x_86);
x_88 = lean_uint64_to_usize(x_87);
x_89 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_90 = 1;
x_91 = lean_usize_sub(x_89, x_90);
x_92 = lean_usize_land(x_88, x_91);
x_93 = lean_array_uget(x_76, x_92);
lean_dec(x_76);
x_94 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_updateSplitArgPosMap_spec__5___redArg(x_77, x_93);
lean_dec(x_93);
lean_dec(x_77);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_box(0);
x_96 = lean_unbox(x_44);
lean_dec(x_44);
x_13 = x_96;
x_14 = x_51;
x_15 = x_95;
goto block_42;
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_unbox(x_44);
lean_dec(x_44);
x_13 = x_98;
x_14 = x_51;
x_15 = x_97;
goto block_42;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_44);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_43);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_43, 0);
lean_dec(x_100);
x_101 = lean_box(0);
lean_ctor_set(x_43, 0, x_101);
return x_43;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_43, 1);
lean_inc(x_102);
lean_dec(x_43);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_43);
if (x_105 == 0)
{
return x_43;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_43, 0);
x_107 = lean_ctor_get(x_43, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_43);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
lean_object* x_21; 
x_21 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitInfoArgStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_checkSplitInfoArgStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; uint8_t x_13; lean_object* x_14; lean_object* x_29; 
lean_inc(x_1);
x_29 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_3, x_4, x_5, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_box(1);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_box(1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_33, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_33, 0, x_44);
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_33);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_80; 
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_dec(x_29);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
lean_dec(x_1);
lean_inc(x_53);
x_80 = l_Lean_Meta_Grind_isEqTrue___redArg(x_53, x_2, x_3, x_4, x_5, x_52);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = l_Lean_Meta_Grind_isEqFalse___redArg(x_53, x_2, x_3, x_4, x_5, x_83);
x_55 = x_84;
goto block_79;
}
else
{
lean_dec(x_53);
x_55 = x_80;
goto block_79;
}
}
else
{
lean_dec(x_53);
x_55 = x_80;
goto block_79;
}
block_79:
{
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l_Lean_Expr_hasLooseBVars(x_54);
if (x_59 == 0)
{
lean_object* x_60; 
lean_inc(x_54);
x_60 = l_Lean_Meta_Grind_isEqTrue___redArg(x_54, x_2, x_3, x_4, x_5, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_Lean_Meta_Grind_isEqFalse___redArg(x_54, x_2, x_3, x_4, x_5, x_63);
x_65 = lean_unbox(x_56);
lean_dec(x_56);
x_13 = x_65;
x_14 = x_64;
goto block_28;
}
else
{
uint8_t x_66; 
lean_dec(x_54);
x_66 = lean_unbox(x_56);
lean_dec(x_56);
x_13 = x_66;
x_14 = x_60;
goto block_28;
}
}
else
{
uint8_t x_67; 
lean_dec(x_54);
x_67 = lean_unbox(x_56);
lean_dec(x_56);
x_13 = x_67;
x_14 = x_60;
goto block_28;
}
}
else
{
uint8_t x_68; 
lean_dec(x_54);
x_68 = lean_unbox(x_56);
lean_dec(x_56);
x_7 = x_68;
x_8 = x_58;
goto block_12;
}
}
else
{
uint8_t x_69; 
lean_dec(x_56);
lean_dec(x_54);
x_69 = !lean_is_exclusive(x_55);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_55, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_ctor_set(x_55, 0, x_71);
return x_55;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_55, 1);
lean_inc(x_72);
lean_dec(x_55);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_54);
x_75 = !lean_is_exclusive(x_55);
if (x_75 == 0)
{
return x_55;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_55, 0);
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_55);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_29);
if (x_85 == 0)
{
return x_29;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_29, 0);
x_87 = lean_ctor_get(x_29, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_29);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_alloc_ctor(2, 1, 2);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 1, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
block_28:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_7 = x_13;
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(x_1, x_3, x_5, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSplitStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkForallStatus___redArg(x_13, x_2, x_4, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Meta_Grind_checkSplitInfoArgStatus(x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checking: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 13);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 13);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 2);
lean_dec(x_20);
x_21 = l_List_reverse___redArg(x_3);
lean_ctor_set(x_15, 2, x_21);
x_22 = lean_st_ref_set(x_4, x_14, x_16);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_23; 
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_138; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_30 = lean_st_ref_get(x_4, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_132 = lean_ctor_get(x_31, 13);
lean_inc(x_132);
lean_dec(x_31);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_dec_lt(x_134, x_28);
lean_dec(x_28);
if (x_138 == 0)
{
x_135 = x_29;
goto block_137;
}
else
{
x_135 = x_138;
goto block_137;
}
block_131:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_st_ref_take(x_4, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 12);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 13);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_35, 13);
lean_dec(x_40);
x_41 = lean_ctor_get(x_35, 12);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_36, 5);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_36, 5, x_46);
lean_ctor_set(x_37, 0, x_33);
x_47 = lean_st_ref_set(x_4, x_35, x_38);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_2);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_ctor_get(x_37, 1);
x_53 = lean_ctor_get(x_37, 2);
x_54 = lean_ctor_get(x_37, 3);
x_55 = lean_ctor_get(x_37, 4);
x_56 = lean_ctor_get(x_37, 5);
x_57 = lean_ctor_get(x_37, 6);
x_58 = lean_ctor_get(x_37, 7);
x_59 = lean_ctor_get(x_37, 8);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
x_60 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_36, 5, x_60);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_33);
lean_ctor_set(x_61, 1, x_52);
lean_ctor_set(x_61, 2, x_53);
lean_ctor_set(x_61, 3, x_54);
lean_ctor_set(x_61, 4, x_55);
lean_ctor_set(x_61, 5, x_56);
lean_ctor_set(x_61, 6, x_57);
lean_ctor_set(x_61, 7, x_58);
lean_ctor_set(x_61, 8, x_59);
lean_ctor_set(x_35, 13, x_61);
x_62 = lean_st_ref_set(x_4, x_35, x_38);
lean_dec(x_4);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_66 = lean_ctor_get(x_36, 0);
x_67 = lean_ctor_get(x_36, 1);
x_68 = lean_ctor_get(x_36, 2);
x_69 = lean_ctor_get(x_36, 3);
x_70 = lean_ctor_get(x_36, 4);
x_71 = lean_ctor_get(x_36, 6);
x_72 = lean_ctor_get(x_36, 7);
x_73 = lean_ctor_get(x_36, 8);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_36);
x_74 = lean_ctor_get(x_37, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_37, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_37, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_37, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_37, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_37, 6);
lean_inc(x_79);
x_80 = lean_ctor_get(x_37, 7);
lean_inc(x_80);
x_81 = lean_ctor_get(x_37, 8);
lean_inc(x_81);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 lean_ctor_release(x_37, 6);
 lean_ctor_release(x_37, 7);
 lean_ctor_release(x_37, 8);
 x_82 = x_37;
} else {
 lean_dec_ref(x_37);
 x_82 = lean_box(0);
}
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_84, 0, x_66);
lean_ctor_set(x_84, 1, x_67);
lean_ctor_set(x_84, 2, x_68);
lean_ctor_set(x_84, 3, x_69);
lean_ctor_set(x_84, 4, x_70);
lean_ctor_set(x_84, 5, x_83);
lean_ctor_set(x_84, 6, x_71);
lean_ctor_set(x_84, 7, x_72);
lean_ctor_set(x_84, 8, x_73);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 9, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_33);
lean_ctor_set(x_85, 1, x_74);
lean_ctor_set(x_85, 2, x_75);
lean_ctor_set(x_85, 3, x_76);
lean_ctor_set(x_85, 4, x_77);
lean_ctor_set(x_85, 5, x_78);
lean_ctor_set(x_85, 6, x_79);
lean_ctor_set(x_85, 7, x_80);
lean_ctor_set(x_85, 8, x_81);
lean_ctor_set(x_35, 13, x_85);
lean_ctor_set(x_35, 12, x_84);
x_86 = lean_st_ref_set(x_4, x_35, x_38);
lean_dec(x_4);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_2);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_90 = lean_ctor_get(x_35, 0);
x_91 = lean_ctor_get(x_35, 1);
x_92 = lean_ctor_get(x_35, 2);
x_93 = lean_ctor_get(x_35, 3);
x_94 = lean_ctor_get(x_35, 4);
x_95 = lean_ctor_get(x_35, 5);
x_96 = lean_ctor_get(x_35, 6);
x_97 = lean_ctor_get(x_35, 7);
x_98 = lean_ctor_get_uint8(x_35, sizeof(void*)*16);
x_99 = lean_ctor_get(x_35, 8);
x_100 = lean_ctor_get(x_35, 9);
x_101 = lean_ctor_get(x_35, 10);
x_102 = lean_ctor_get(x_35, 11);
x_103 = lean_ctor_get(x_35, 14);
x_104 = lean_ctor_get(x_35, 15);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_35);
x_105 = lean_ctor_get(x_36, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_36, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_36, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_36, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_36, 4);
lean_inc(x_109);
x_110 = lean_ctor_get(x_36, 6);
lean_inc(x_110);
x_111 = lean_ctor_get(x_36, 7);
lean_inc(x_111);
x_112 = lean_ctor_get(x_36, 8);
lean_inc(x_112);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 lean_ctor_release(x_36, 6);
 lean_ctor_release(x_36, 7);
 lean_ctor_release(x_36, 8);
 x_113 = x_36;
} else {
 lean_dec_ref(x_36);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_37, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_37, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_37, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_37, 4);
lean_inc(x_117);
x_118 = lean_ctor_get(x_37, 5);
lean_inc(x_118);
x_119 = lean_ctor_get(x_37, 6);
lean_inc(x_119);
x_120 = lean_ctor_get(x_37, 7);
lean_inc(x_120);
x_121 = lean_ctor_get(x_37, 8);
lean_inc(x_121);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 lean_ctor_release(x_37, 6);
 lean_ctor_release(x_37, 7);
 lean_ctor_release(x_37, 8);
 x_122 = x_37;
} else {
 lean_dec_ref(x_37);
 x_122 = lean_box(0);
}
x_123 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_113)) {
 x_124 = lean_alloc_ctor(0, 9, 0);
} else {
 x_124 = x_113;
}
lean_ctor_set(x_124, 0, x_105);
lean_ctor_set(x_124, 1, x_106);
lean_ctor_set(x_124, 2, x_107);
lean_ctor_set(x_124, 3, x_108);
lean_ctor_set(x_124, 4, x_109);
lean_ctor_set(x_124, 5, x_123);
lean_ctor_set(x_124, 6, x_110);
lean_ctor_set(x_124, 7, x_111);
lean_ctor_set(x_124, 8, x_112);
if (lean_is_scalar(x_122)) {
 x_125 = lean_alloc_ctor(0, 9, 0);
} else {
 x_125 = x_122;
}
lean_ctor_set(x_125, 0, x_33);
lean_ctor_set(x_125, 1, x_114);
lean_ctor_set(x_125, 2, x_115);
lean_ctor_set(x_125, 3, x_116);
lean_ctor_set(x_125, 4, x_117);
lean_ctor_set(x_125, 5, x_118);
lean_ctor_set(x_125, 6, x_119);
lean_ctor_set(x_125, 7, x_120);
lean_ctor_set(x_125, 8, x_121);
x_126 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_126, 0, x_90);
lean_ctor_set(x_126, 1, x_91);
lean_ctor_set(x_126, 2, x_92);
lean_ctor_set(x_126, 3, x_93);
lean_ctor_set(x_126, 4, x_94);
lean_ctor_set(x_126, 5, x_95);
lean_ctor_set(x_126, 6, x_96);
lean_ctor_set(x_126, 7, x_97);
lean_ctor_set(x_126, 8, x_99);
lean_ctor_set(x_126, 9, x_100);
lean_ctor_set(x_126, 10, x_101);
lean_ctor_set(x_126, 11, x_102);
lean_ctor_set(x_126, 12, x_124);
lean_ctor_set(x_126, 13, x_125);
lean_ctor_set(x_126, 14, x_103);
lean_ctor_set(x_126, 15, x_104);
lean_ctor_set_uint8(x_126, sizeof(void*)*16, x_98);
x_127 = lean_st_ref_set(x_4, x_126, x_38);
lean_dec(x_4);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_2);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
block_137:
{
if (x_135 == 0)
{
x_33 = x_133;
goto block_131;
}
else
{
lean_object* x_136; 
x_136 = lean_nat_add(x_133, x_134);
lean_dec(x_133);
x_33 = x_136;
goto block_131;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_139 = lean_ctor_get(x_15, 0);
x_140 = lean_ctor_get(x_15, 1);
x_141 = lean_ctor_get(x_15, 3);
x_142 = lean_ctor_get(x_15, 4);
x_143 = lean_ctor_get(x_15, 5);
x_144 = lean_ctor_get(x_15, 6);
x_145 = lean_ctor_get(x_15, 7);
x_146 = lean_ctor_get(x_15, 8);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_15);
x_147 = l_List_reverse___redArg(x_3);
x_148 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_148, 0, x_139);
lean_ctor_set(x_148, 1, x_140);
lean_ctor_set(x_148, 2, x_147);
lean_ctor_set(x_148, 3, x_141);
lean_ctor_set(x_148, 4, x_142);
lean_ctor_set(x_148, 5, x_143);
lean_ctor_set(x_148, 6, x_144);
lean_ctor_set(x_148, 7, x_145);
lean_ctor_set(x_148, 8, x_146);
lean_ctor_set(x_14, 13, x_148);
x_149 = lean_st_ref_set(x_4, x_14, x_16);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_4);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_2);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_214; 
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
lean_dec(x_149);
x_154 = lean_ctor_get(x_2, 1);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_156 = lean_st_ref_get(x_4, x_153);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_208 = lean_ctor_get(x_157, 13);
lean_inc(x_208);
lean_dec(x_157);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_dec_lt(x_210, x_154);
lean_dec(x_154);
if (x_214 == 0)
{
x_211 = x_155;
goto block_213;
}
else
{
x_211 = x_214;
goto block_213;
}
block_207:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_160 = lean_st_ref_take(x_4, x_158);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_161, 12);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 13);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_ctor_get(x_161, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_161, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_161, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_161, 4);
lean_inc(x_169);
x_170 = lean_ctor_get(x_161, 5);
lean_inc(x_170);
x_171 = lean_ctor_get(x_161, 6);
lean_inc(x_171);
x_172 = lean_ctor_get(x_161, 7);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_161, sizeof(void*)*16);
x_174 = lean_ctor_get(x_161, 8);
lean_inc(x_174);
x_175 = lean_ctor_get(x_161, 9);
lean_inc(x_175);
x_176 = lean_ctor_get(x_161, 10);
lean_inc(x_176);
x_177 = lean_ctor_get(x_161, 11);
lean_inc(x_177);
x_178 = lean_ctor_get(x_161, 14);
lean_inc(x_178);
x_179 = lean_ctor_get(x_161, 15);
lean_inc(x_179);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 lean_ctor_release(x_161, 6);
 lean_ctor_release(x_161, 7);
 lean_ctor_release(x_161, 8);
 lean_ctor_release(x_161, 9);
 lean_ctor_release(x_161, 10);
 lean_ctor_release(x_161, 11);
 lean_ctor_release(x_161, 12);
 lean_ctor_release(x_161, 13);
 lean_ctor_release(x_161, 14);
 lean_ctor_release(x_161, 15);
 x_180 = x_161;
} else {
 lean_dec_ref(x_161);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_162, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_162, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_162, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_162, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_162, 4);
lean_inc(x_185);
x_186 = lean_ctor_get(x_162, 6);
lean_inc(x_186);
x_187 = lean_ctor_get(x_162, 7);
lean_inc(x_187);
x_188 = lean_ctor_get(x_162, 8);
lean_inc(x_188);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 lean_ctor_release(x_162, 3);
 lean_ctor_release(x_162, 4);
 lean_ctor_release(x_162, 5);
 lean_ctor_release(x_162, 6);
 lean_ctor_release(x_162, 7);
 lean_ctor_release(x_162, 8);
 x_189 = x_162;
} else {
 lean_dec_ref(x_162);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_163, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_163, 2);
lean_inc(x_191);
x_192 = lean_ctor_get(x_163, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_163, 4);
lean_inc(x_193);
x_194 = lean_ctor_get(x_163, 5);
lean_inc(x_194);
x_195 = lean_ctor_get(x_163, 6);
lean_inc(x_195);
x_196 = lean_ctor_get(x_163, 7);
lean_inc(x_196);
x_197 = lean_ctor_get(x_163, 8);
lean_inc(x_197);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 lean_ctor_release(x_163, 5);
 lean_ctor_release(x_163, 6);
 lean_ctor_release(x_163, 7);
 lean_ctor_release(x_163, 8);
 x_198 = x_163;
} else {
 lean_dec_ref(x_163);
 x_198 = lean_box(0);
}
x_199 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_189)) {
 x_200 = lean_alloc_ctor(0, 9, 0);
} else {
 x_200 = x_189;
}
lean_ctor_set(x_200, 0, x_181);
lean_ctor_set(x_200, 1, x_182);
lean_ctor_set(x_200, 2, x_183);
lean_ctor_set(x_200, 3, x_184);
lean_ctor_set(x_200, 4, x_185);
lean_ctor_set(x_200, 5, x_199);
lean_ctor_set(x_200, 6, x_186);
lean_ctor_set(x_200, 7, x_187);
lean_ctor_set(x_200, 8, x_188);
if (lean_is_scalar(x_198)) {
 x_201 = lean_alloc_ctor(0, 9, 0);
} else {
 x_201 = x_198;
}
lean_ctor_set(x_201, 0, x_159);
lean_ctor_set(x_201, 1, x_190);
lean_ctor_set(x_201, 2, x_191);
lean_ctor_set(x_201, 3, x_192);
lean_ctor_set(x_201, 4, x_193);
lean_ctor_set(x_201, 5, x_194);
lean_ctor_set(x_201, 6, x_195);
lean_ctor_set(x_201, 7, x_196);
lean_ctor_set(x_201, 8, x_197);
if (lean_is_scalar(x_180)) {
 x_202 = lean_alloc_ctor(0, 16, 1);
} else {
 x_202 = x_180;
}
lean_ctor_set(x_202, 0, x_165);
lean_ctor_set(x_202, 1, x_166);
lean_ctor_set(x_202, 2, x_167);
lean_ctor_set(x_202, 3, x_168);
lean_ctor_set(x_202, 4, x_169);
lean_ctor_set(x_202, 5, x_170);
lean_ctor_set(x_202, 6, x_171);
lean_ctor_set(x_202, 7, x_172);
lean_ctor_set(x_202, 8, x_174);
lean_ctor_set(x_202, 9, x_175);
lean_ctor_set(x_202, 10, x_176);
lean_ctor_set(x_202, 11, x_177);
lean_ctor_set(x_202, 12, x_200);
lean_ctor_set(x_202, 13, x_201);
lean_ctor_set(x_202, 14, x_178);
lean_ctor_set(x_202, 15, x_179);
lean_ctor_set_uint8(x_202, sizeof(void*)*16, x_173);
x_203 = lean_st_ref_set(x_4, x_202, x_164);
lean_dec(x_4);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_205 = x_203;
} else {
 lean_dec_ref(x_203);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_2);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
block_213:
{
if (x_211 == 0)
{
x_159 = x_209;
goto block_207;
}
else
{
lean_object* x_212; 
x_212 = lean_nat_add(x_209, x_210);
lean_dec(x_209);
x_159 = x_212;
goto block_207;
}
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_215 = lean_ctor_get(x_14, 0);
x_216 = lean_ctor_get(x_14, 1);
x_217 = lean_ctor_get(x_14, 2);
x_218 = lean_ctor_get(x_14, 3);
x_219 = lean_ctor_get(x_14, 4);
x_220 = lean_ctor_get(x_14, 5);
x_221 = lean_ctor_get(x_14, 6);
x_222 = lean_ctor_get(x_14, 7);
x_223 = lean_ctor_get_uint8(x_14, sizeof(void*)*16);
x_224 = lean_ctor_get(x_14, 8);
x_225 = lean_ctor_get(x_14, 9);
x_226 = lean_ctor_get(x_14, 10);
x_227 = lean_ctor_get(x_14, 11);
x_228 = lean_ctor_get(x_14, 12);
x_229 = lean_ctor_get(x_14, 14);
x_230 = lean_ctor_get(x_14, 15);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_14);
x_231 = lean_ctor_get(x_15, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_15, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_15, 3);
lean_inc(x_233);
x_234 = lean_ctor_get(x_15, 4);
lean_inc(x_234);
x_235 = lean_ctor_get(x_15, 5);
lean_inc(x_235);
x_236 = lean_ctor_get(x_15, 6);
lean_inc(x_236);
x_237 = lean_ctor_get(x_15, 7);
lean_inc(x_237);
x_238 = lean_ctor_get(x_15, 8);
lean_inc(x_238);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 lean_ctor_release(x_15, 6);
 lean_ctor_release(x_15, 7);
 lean_ctor_release(x_15, 8);
 x_239 = x_15;
} else {
 lean_dec_ref(x_15);
 x_239 = lean_box(0);
}
x_240 = l_List_reverse___redArg(x_3);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(0, 9, 0);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_231);
lean_ctor_set(x_241, 1, x_232);
lean_ctor_set(x_241, 2, x_240);
lean_ctor_set(x_241, 3, x_233);
lean_ctor_set(x_241, 4, x_234);
lean_ctor_set(x_241, 5, x_235);
lean_ctor_set(x_241, 6, x_236);
lean_ctor_set(x_241, 7, x_237);
lean_ctor_set(x_241, 8, x_238);
x_242 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_242, 0, x_215);
lean_ctor_set(x_242, 1, x_216);
lean_ctor_set(x_242, 2, x_217);
lean_ctor_set(x_242, 3, x_218);
lean_ctor_set(x_242, 4, x_219);
lean_ctor_set(x_242, 5, x_220);
lean_ctor_set(x_242, 6, x_221);
lean_ctor_set(x_242, 7, x_222);
lean_ctor_set(x_242, 8, x_224);
lean_ctor_set(x_242, 9, x_225);
lean_ctor_set(x_242, 10, x_226);
lean_ctor_set(x_242, 11, x_227);
lean_ctor_set(x_242, 12, x_228);
lean_ctor_set(x_242, 13, x_241);
lean_ctor_set(x_242, 14, x_229);
lean_ctor_set(x_242, 15, x_230);
lean_ctor_set_uint8(x_242, sizeof(void*)*16, x_223);
x_243 = lean_st_ref_set(x_4, x_242, x_16);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_4);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_2);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_308; 
x_247 = lean_ctor_get(x_243, 1);
lean_inc(x_247);
lean_dec(x_243);
x_248 = lean_ctor_get(x_2, 1);
lean_inc(x_248);
x_249 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_250 = lean_st_ref_get(x_4, x_247);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_302 = lean_ctor_get(x_251, 13);
lean_inc(x_302);
lean_dec(x_251);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
lean_dec(x_302);
x_304 = lean_unsigned_to_nat(1u);
x_308 = lean_nat_dec_lt(x_304, x_248);
lean_dec(x_248);
if (x_308 == 0)
{
x_305 = x_249;
goto block_307;
}
else
{
x_305 = x_308;
goto block_307;
}
block_301:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_254 = lean_st_ref_take(x_4, x_252);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_255, 12);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 13);
lean_inc(x_257);
x_258 = lean_ctor_get(x_254, 1);
lean_inc(x_258);
lean_dec(x_254);
x_259 = lean_ctor_get(x_255, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_255, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_255, 2);
lean_inc(x_261);
x_262 = lean_ctor_get(x_255, 3);
lean_inc(x_262);
x_263 = lean_ctor_get(x_255, 4);
lean_inc(x_263);
x_264 = lean_ctor_get(x_255, 5);
lean_inc(x_264);
x_265 = lean_ctor_get(x_255, 6);
lean_inc(x_265);
x_266 = lean_ctor_get(x_255, 7);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_255, sizeof(void*)*16);
x_268 = lean_ctor_get(x_255, 8);
lean_inc(x_268);
x_269 = lean_ctor_get(x_255, 9);
lean_inc(x_269);
x_270 = lean_ctor_get(x_255, 10);
lean_inc(x_270);
x_271 = lean_ctor_get(x_255, 11);
lean_inc(x_271);
x_272 = lean_ctor_get(x_255, 14);
lean_inc(x_272);
x_273 = lean_ctor_get(x_255, 15);
lean_inc(x_273);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 lean_ctor_release(x_255, 3);
 lean_ctor_release(x_255, 4);
 lean_ctor_release(x_255, 5);
 lean_ctor_release(x_255, 6);
 lean_ctor_release(x_255, 7);
 lean_ctor_release(x_255, 8);
 lean_ctor_release(x_255, 9);
 lean_ctor_release(x_255, 10);
 lean_ctor_release(x_255, 11);
 lean_ctor_release(x_255, 12);
 lean_ctor_release(x_255, 13);
 lean_ctor_release(x_255, 14);
 lean_ctor_release(x_255, 15);
 x_274 = x_255;
} else {
 lean_dec_ref(x_255);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_256, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_256, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_256, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_256, 3);
lean_inc(x_278);
x_279 = lean_ctor_get(x_256, 4);
lean_inc(x_279);
x_280 = lean_ctor_get(x_256, 6);
lean_inc(x_280);
x_281 = lean_ctor_get(x_256, 7);
lean_inc(x_281);
x_282 = lean_ctor_get(x_256, 8);
lean_inc(x_282);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 lean_ctor_release(x_256, 3);
 lean_ctor_release(x_256, 4);
 lean_ctor_release(x_256, 5);
 lean_ctor_release(x_256, 6);
 lean_ctor_release(x_256, 7);
 lean_ctor_release(x_256, 8);
 x_283 = x_256;
} else {
 lean_dec_ref(x_256);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_257, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_257, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_257, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_257, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_257, 5);
lean_inc(x_288);
x_289 = lean_ctor_get(x_257, 6);
lean_inc(x_289);
x_290 = lean_ctor_get(x_257, 7);
lean_inc(x_290);
x_291 = lean_ctor_get(x_257, 8);
lean_inc(x_291);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 lean_ctor_release(x_257, 4);
 lean_ctor_release(x_257, 5);
 lean_ctor_release(x_257, 6);
 lean_ctor_release(x_257, 7);
 lean_ctor_release(x_257, 8);
 x_292 = x_257;
} else {
 lean_dec_ref(x_257);
 x_292 = lean_box(0);
}
x_293 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_283)) {
 x_294 = lean_alloc_ctor(0, 9, 0);
} else {
 x_294 = x_283;
}
lean_ctor_set(x_294, 0, x_275);
lean_ctor_set(x_294, 1, x_276);
lean_ctor_set(x_294, 2, x_277);
lean_ctor_set(x_294, 3, x_278);
lean_ctor_set(x_294, 4, x_279);
lean_ctor_set(x_294, 5, x_293);
lean_ctor_set(x_294, 6, x_280);
lean_ctor_set(x_294, 7, x_281);
lean_ctor_set(x_294, 8, x_282);
if (lean_is_scalar(x_292)) {
 x_295 = lean_alloc_ctor(0, 9, 0);
} else {
 x_295 = x_292;
}
lean_ctor_set(x_295, 0, x_253);
lean_ctor_set(x_295, 1, x_284);
lean_ctor_set(x_295, 2, x_285);
lean_ctor_set(x_295, 3, x_286);
lean_ctor_set(x_295, 4, x_287);
lean_ctor_set(x_295, 5, x_288);
lean_ctor_set(x_295, 6, x_289);
lean_ctor_set(x_295, 7, x_290);
lean_ctor_set(x_295, 8, x_291);
if (lean_is_scalar(x_274)) {
 x_296 = lean_alloc_ctor(0, 16, 1);
} else {
 x_296 = x_274;
}
lean_ctor_set(x_296, 0, x_259);
lean_ctor_set(x_296, 1, x_260);
lean_ctor_set(x_296, 2, x_261);
lean_ctor_set(x_296, 3, x_262);
lean_ctor_set(x_296, 4, x_263);
lean_ctor_set(x_296, 5, x_264);
lean_ctor_set(x_296, 6, x_265);
lean_ctor_set(x_296, 7, x_266);
lean_ctor_set(x_296, 8, x_268);
lean_ctor_set(x_296, 9, x_269);
lean_ctor_set(x_296, 10, x_270);
lean_ctor_set(x_296, 11, x_271);
lean_ctor_set(x_296, 12, x_294);
lean_ctor_set(x_296, 13, x_295);
lean_ctor_set(x_296, 14, x_272);
lean_ctor_set(x_296, 15, x_273);
lean_ctor_set_uint8(x_296, sizeof(void*)*16, x_267);
x_297 = lean_st_ref_set(x_4, x_296, x_258);
lean_dec(x_4);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_299 = x_297;
} else {
 lean_dec_ref(x_297);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_2);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
block_307:
{
if (x_305 == 0)
{
x_253 = x_303;
goto block_301;
}
else
{
lean_object* x_306; 
x_306 = lean_nat_add(x_303, x_304);
lean_dec(x_303);
x_253 = x_306;
goto block_301;
}
}
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_309 = lean_ctor_get(x_1, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_1, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_311 = x_1;
} else {
 lean_dec_ref(x_1);
 x_311 = lean_box(0);
}
x_466 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9;
x_467 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_466, x_10, x_12);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_unbox(x_468);
lean_dec(x_468);
if (x_469 == 0)
{
lean_object* x_470; 
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
lean_dec(x_467);
x_425 = x_4;
x_426 = x_5;
x_427 = x_6;
x_428 = x_7;
x_429 = x_8;
x_430 = x_9;
x_431 = x_10;
x_432 = x_11;
x_433 = x_470;
goto block_465;
}
else
{
uint8_t x_471; 
x_471 = !lean_is_exclusive(x_467);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_467, 1);
x_473 = lean_ctor_get(x_467, 0);
lean_dec(x_473);
x_474 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_472);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
lean_dec(x_474);
x_476 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1;
x_477 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_309);
x_478 = l_Lean_MessageData_ofExpr(x_477);
lean_ctor_set_tag(x_467, 7);
lean_ctor_set(x_467, 1, x_478);
lean_ctor_set(x_467, 0, x_476);
x_479 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_480 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_480, 0, x_467);
lean_ctor_set(x_480, 1, x_479);
x_481 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_466, x_480, x_8, x_9, x_10, x_11, x_475);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
lean_dec(x_481);
x_425 = x_4;
x_426 = x_5;
x_427 = x_6;
x_428 = x_7;
x_429 = x_8;
x_430 = x_9;
x_431 = x_10;
x_432 = x_11;
x_433 = x_482;
goto block_465;
}
else
{
uint8_t x_483; 
lean_free_object(x_467);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_483 = !lean_is_exclusive(x_474);
if (x_483 == 0)
{
return x_474;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_474, 0);
x_485 = lean_ctor_get(x_474, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_474);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
else
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_467, 1);
lean_inc(x_487);
lean_dec(x_467);
x_488 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_487);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
lean_dec(x_488);
x_490 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1;
x_491 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_309);
x_492 = l_Lean_MessageData_ofExpr(x_491);
x_493 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_493, 0, x_490);
lean_ctor_set(x_493, 1, x_492);
x_494 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
x_495 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
x_496 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_466, x_495, x_8, x_9, x_10, x_11, x_489);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec(x_496);
x_425 = x_4;
x_426 = x_5;
x_427 = x_6;
x_428 = x_7;
x_429 = x_8;
x_430 = x_9;
x_431 = x_10;
x_432 = x_11;
x_433 = x_497;
goto block_465;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_498 = lean_ctor_get(x_488, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_488, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_500 = x_488;
} else {
 lean_dec_ref(x_488);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_498);
lean_ctor_set(x_501, 1, x_499);
return x_501;
}
}
}
block_323:
{
lean_object* x_321; 
if (lean_is_scalar(x_311)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_311;
}
lean_ctor_set(x_321, 0, x_309);
lean_ctor_set(x_321, 1, x_3);
x_1 = x_310;
x_3 = x_321;
x_4 = x_314;
x_5 = x_318;
x_6 = x_319;
x_7 = x_315;
x_8 = x_313;
x_9 = x_317;
x_10 = x_312;
x_11 = x_316;
x_12 = x_320;
goto _start;
}
block_340:
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(x_337, 0, x_309);
lean_ctor_set(x_337, 1, x_329);
lean_ctor_set_uint8(x_337, sizeof(void*)*2, x_326);
lean_ctor_set_uint8(x_337, sizeof(void*)*2 + 1, x_332);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_3);
x_1 = x_310;
x_2 = x_337;
x_3 = x_338;
x_4 = x_327;
x_5 = x_333;
x_6 = x_334;
x_7 = x_328;
x_8 = x_325;
x_9 = x_331;
x_10 = x_324;
x_11 = x_330;
x_12 = x_336;
goto _start;
}
block_365:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_355 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_309);
x_356 = l_Lean_Meta_Grind_getGeneration___redArg(x_355, x_343, x_354);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_346);
x_360 = l_Lean_Meta_Grind_getGeneration___redArg(x_359, x_343, x_358);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_nat_dec_lt(x_357, x_361);
lean_dec(x_361);
lean_dec(x_357);
if (x_363 == 0)
{
uint8_t x_364; 
x_364 = lean_nat_dec_lt(x_348, x_349);
lean_dec(x_349);
if (x_364 == 0)
{
lean_dec(x_348);
lean_dec(x_346);
x_312 = x_341;
x_313 = x_342;
x_314 = x_343;
x_315 = x_344;
x_316 = x_350;
x_317 = x_351;
x_318 = x_345;
x_319 = x_353;
x_320 = x_362;
goto block_323;
}
else
{
lean_dec(x_311);
lean_dec(x_2);
x_324 = x_341;
x_325 = x_342;
x_326 = x_347;
x_327 = x_343;
x_328 = x_344;
x_329 = x_348;
x_330 = x_350;
x_331 = x_351;
x_332 = x_352;
x_333 = x_345;
x_334 = x_353;
x_335 = x_346;
x_336 = x_362;
goto block_340;
}
}
else
{
lean_dec(x_349);
lean_dec(x_311);
lean_dec(x_2);
x_324 = x_341;
x_325 = x_342;
x_326 = x_347;
x_327 = x_343;
x_328 = x_344;
x_329 = x_348;
x_330 = x_350;
x_331 = x_351;
x_332 = x_352;
x_333 = x_345;
x_334 = x_353;
x_335 = x_346;
x_336 = x_362;
goto block_340;
}
}
block_383:
{
if (x_380 == 0)
{
x_341 = x_366;
x_342 = x_367;
x_343 = x_368;
x_344 = x_369;
x_345 = x_370;
x_346 = x_371;
x_347 = x_372;
x_348 = x_373;
x_349 = x_374;
x_350 = x_375;
x_351 = x_376;
x_352 = x_377;
x_353 = x_378;
x_354 = x_379;
goto block_365;
}
else
{
lean_object* x_381; uint8_t x_382; 
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_dec_lt(x_381, x_374);
if (x_382 == 0)
{
x_341 = x_366;
x_342 = x_367;
x_343 = x_368;
x_344 = x_369;
x_345 = x_370;
x_346 = x_371;
x_347 = x_372;
x_348 = x_373;
x_349 = x_374;
x_350 = x_375;
x_351 = x_376;
x_352 = x_377;
x_353 = x_378;
x_354 = x_379;
goto block_365;
}
else
{
lean_dec(x_374);
lean_dec(x_311);
lean_dec(x_2);
x_324 = x_366;
x_325 = x_367;
x_326 = x_372;
x_327 = x_368;
x_328 = x_369;
x_329 = x_373;
x_330 = x_375;
x_331 = x_376;
x_332 = x_377;
x_333 = x_370;
x_334 = x_378;
x_335 = x_371;
x_336 = x_379;
goto block_340;
}
}
}
block_401:
{
lean_object* x_399; uint8_t x_400; 
x_399 = lean_unsigned_to_nat(1u);
x_400 = lean_nat_dec_eq(x_391, x_399);
if (x_400 == 0)
{
x_366 = x_384;
x_367 = x_385;
x_368 = x_386;
x_369 = x_387;
x_370 = x_388;
x_371 = x_389;
x_372 = x_390;
x_373 = x_391;
x_374 = x_392;
x_375 = x_393;
x_376 = x_394;
x_377 = x_395;
x_378 = x_396;
x_379 = x_397;
x_380 = x_400;
goto block_383;
}
else
{
if (x_390 == 0)
{
x_366 = x_384;
x_367 = x_385;
x_368 = x_386;
x_369 = x_387;
x_370 = x_388;
x_371 = x_389;
x_372 = x_390;
x_373 = x_391;
x_374 = x_392;
x_375 = x_393;
x_376 = x_394;
x_377 = x_395;
x_378 = x_396;
x_379 = x_397;
x_380 = x_400;
goto block_383;
}
else
{
x_366 = x_384;
x_367 = x_385;
x_368 = x_386;
x_369 = x_387;
x_370 = x_388;
x_371 = x_389;
x_372 = x_390;
x_373 = x_391;
x_374 = x_392;
x_375 = x_393;
x_376 = x_394;
x_377 = x_395;
x_378 = x_396;
x_379 = x_397;
x_380 = x_398;
goto block_383;
}
}
}
block_424:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_415; 
lean_dec(x_311);
x_415 = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(x_415, 0, x_309);
lean_ctor_set(x_415, 1, x_407);
lean_ctor_set_uint8(x_415, sizeof(void*)*2, x_404);
lean_ctor_set_uint8(x_415, sizeof(void*)*2 + 1, x_410);
x_1 = x_310;
x_2 = x_415;
x_4 = x_405;
x_5 = x_411;
x_6 = x_412;
x_7 = x_406;
x_8 = x_403;
x_9 = x_409;
x_10 = x_402;
x_11 = x_408;
x_12 = x_413;
goto _start;
}
else
{
uint8_t x_417; 
x_417 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
if (x_417 == 0)
{
if (x_410 == 0)
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_2, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_2, 1);
lean_inc(x_419);
x_384 = x_402;
x_385 = x_403;
x_386 = x_405;
x_387 = x_406;
x_388 = x_411;
x_389 = x_418;
x_390 = x_404;
x_391 = x_407;
x_392 = x_419;
x_393 = x_408;
x_394 = x_409;
x_395 = x_410;
x_396 = x_412;
x_397 = x_413;
x_398 = x_410;
goto block_401;
}
else
{
lean_dec(x_407);
x_312 = x_402;
x_313 = x_403;
x_314 = x_405;
x_315 = x_406;
x_316 = x_408;
x_317 = x_409;
x_318 = x_411;
x_319 = x_412;
x_320 = x_413;
goto block_323;
}
}
else
{
if (x_410 == 0)
{
lean_object* x_420; 
lean_dec(x_311);
x_420 = lean_ctor_get(x_2, 0);
lean_inc(x_420);
lean_dec(x_2);
x_324 = x_402;
x_325 = x_403;
x_326 = x_404;
x_327 = x_405;
x_328 = x_406;
x_329 = x_407;
x_330 = x_408;
x_331 = x_409;
x_332 = x_410;
x_333 = x_411;
x_334 = x_412;
x_335 = x_420;
x_336 = x_413;
goto block_340;
}
else
{
if (x_414 == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_2, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_2, 1);
lean_inc(x_422);
x_384 = x_402;
x_385 = x_403;
x_386 = x_405;
x_387 = x_406;
x_388 = x_411;
x_389 = x_421;
x_390 = x_404;
x_391 = x_407;
x_392 = x_422;
x_393 = x_408;
x_394 = x_409;
x_395 = x_410;
x_396 = x_412;
x_397 = x_413;
x_398 = x_414;
goto block_401;
}
else
{
lean_object* x_423; 
lean_dec(x_311);
x_423 = lean_ctor_get(x_2, 0);
lean_inc(x_423);
lean_dec(x_2);
x_324 = x_402;
x_325 = x_403;
x_326 = x_404;
x_327 = x_405;
x_328 = x_406;
x_329 = x_407;
x_330 = x_408;
x_331 = x_409;
x_332 = x_410;
x_333 = x_411;
x_334 = x_412;
x_335 = x_423;
x_336 = x_413;
goto block_340;
}
}
}
}
}
block_465:
{
lean_object* x_434; 
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_309);
x_434 = l_Lean_Meta_Grind_checkSplitStatus(x_309, x_425, x_426, x_427, x_428, x_429, x_430, x_431, x_432, x_433);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
switch (lean_obj_tag(x_435)) {
case 0:
{
lean_object* x_436; 
lean_dec(x_311);
lean_dec(x_309);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_1 = x_310;
x_4 = x_425;
x_5 = x_426;
x_6 = x_427;
x_7 = x_428;
x_8 = x_429;
x_9 = x_430;
x_10 = x_431;
x_11 = x_432;
x_12 = x_436;
goto _start;
}
case 1:
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_311);
x_438 = lean_ctor_get(x_434, 1);
lean_inc(x_438);
lean_dec(x_434);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_309);
lean_ctor_set(x_439, 1, x_3);
x_1 = x_310;
x_3 = x_439;
x_4 = x_425;
x_5 = x_426;
x_6 = x_427;
x_7 = x_428;
x_8 = x_429;
x_9 = x_430;
x_10 = x_431;
x_11 = x_432;
x_12 = x_438;
goto _start;
}
default: 
{
lean_object* x_441; lean_object* x_442; uint8_t x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_441 = lean_ctor_get(x_434, 1);
lean_inc(x_441);
lean_dec(x_434);
x_442 = lean_ctor_get(x_435, 0);
lean_inc(x_442);
x_443 = lean_ctor_get_uint8(x_435, sizeof(void*)*1);
x_444 = lean_ctor_get_uint8(x_435, sizeof(void*)*1 + 1);
lean_dec(x_435);
x_445 = l_Lean_Meta_Grind_cheapCasesOnly___redArg(x_427, x_441);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_unbox(x_446);
if (x_447 == 0)
{
lean_object* x_448; uint8_t x_449; 
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_448);
lean_dec(x_445);
x_449 = lean_unbox(x_446);
lean_dec(x_446);
x_402 = x_431;
x_403 = x_429;
x_404 = x_443;
x_405 = x_425;
x_406 = x_428;
x_407 = x_442;
x_408 = x_432;
x_409 = x_430;
x_410 = x_444;
x_411 = x_426;
x_412 = x_427;
x_413 = x_448;
x_414 = x_449;
goto block_424;
}
else
{
uint8_t x_450; 
lean_dec(x_446);
x_450 = !lean_is_exclusive(x_445);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_451 = lean_ctor_get(x_445, 1);
x_452 = lean_ctor_get(x_445, 0);
lean_dec(x_452);
x_453 = lean_unsigned_to_nat(1u);
x_454 = lean_nat_dec_lt(x_453, x_442);
if (x_454 == 0)
{
lean_free_object(x_445);
x_402 = x_431;
x_403 = x_429;
x_404 = x_443;
x_405 = x_425;
x_406 = x_428;
x_407 = x_442;
x_408 = x_432;
x_409 = x_430;
x_410 = x_444;
x_411 = x_426;
x_412 = x_427;
x_413 = x_451;
x_414 = x_454;
goto block_424;
}
else
{
lean_dec(x_442);
lean_dec(x_311);
lean_ctor_set_tag(x_445, 1);
lean_ctor_set(x_445, 1, x_3);
lean_ctor_set(x_445, 0, x_309);
x_1 = x_310;
x_3 = x_445;
x_4 = x_425;
x_5 = x_426;
x_6 = x_427;
x_7 = x_428;
x_8 = x_429;
x_9 = x_430;
x_10 = x_431;
x_11 = x_432;
x_12 = x_451;
goto _start;
}
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_456 = lean_ctor_get(x_445, 1);
lean_inc(x_456);
lean_dec(x_445);
x_457 = lean_unsigned_to_nat(1u);
x_458 = lean_nat_dec_lt(x_457, x_442);
if (x_458 == 0)
{
x_402 = x_431;
x_403 = x_429;
x_404 = x_443;
x_405 = x_425;
x_406 = x_428;
x_407 = x_442;
x_408 = x_432;
x_409 = x_430;
x_410 = x_444;
x_411 = x_426;
x_412 = x_427;
x_413 = x_456;
x_414 = x_458;
goto block_424;
}
else
{
lean_object* x_459; 
lean_dec(x_442);
lean_dec(x_311);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_309);
lean_ctor_set(x_459, 1, x_3);
x_1 = x_310;
x_3 = x_459;
x_4 = x_425;
x_5 = x_426;
x_6 = x_427;
x_7 = x_428;
x_8 = x_429;
x_9 = x_430;
x_10 = x_431;
x_11 = x_432;
x_12 = x_456;
goto _start;
}
}
}
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_3);
lean_dec(x_2);
x_461 = !lean_is_exclusive(x_434);
if (x_461 == 0)
{
return x_434;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_434, 0);
x_463 = lean_ctor_get(x_434, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_434);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Grind_isInconsistent___redArg(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(x_1, x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_get(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 13);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go(x_22, x_23, x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_14, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_10, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_10, 0, x_34);
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("em", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_eq_eq_false", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_eq_eq_true", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or_of_and_eq_false", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_49; uint8_t x_50; 
lean_inc(x_1);
x_49 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_64; uint8_t x_65; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
x_64 = l_Lean_Expr_cleanupAnnotations(x_51);
x_65 = l_Lean_Expr_isApp(x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_free_object(x_49);
x_53 = x_2;
x_54 = x_3;
x_55 = x_4;
x_56 = x_5;
x_57 = x_6;
x_58 = x_7;
x_59 = x_8;
x_60 = x_9;
goto block_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
x_67 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_68 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1;
x_69 = l_Lean_Expr_isConstOf(x_67, x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_isApp(x_67);
if (x_70 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_49);
x_53 = x_2;
x_54 = x_3;
x_55 = x_4;
x_56 = x_5;
x_57 = x_6;
x_58 = x_7;
x_59 = x_8;
x_60 = x_9;
goto block_63;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
x_72 = l_Lean_Expr_appFnCleanup___redArg(x_67);
x_73 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13;
x_74 = l_Lean_Expr_isConstOf(x_72, x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Expr_isApp(x_72);
if (x_75 == 0)
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_66);
lean_free_object(x_49);
x_53 = x_2;
x_54 = x_3;
x_55 = x_4;
x_56 = x_5;
x_57 = x_6;
x_58 = x_7;
x_59 = x_8;
x_60 = x_9;
goto block_63;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = l_Lean_Expr_appFnCleanup___redArg(x_72);
x_77 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17;
x_78 = l_Lean_Expr_isConstOf(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_dec(x_71);
lean_dec(x_66);
lean_free_object(x_49);
x_53 = x_2;
x_54 = x_3;
x_55 = x_4;
x_56 = x_5;
x_57 = x_6;
x_58 = x_7;
x_59 = x_8;
x_60 = x_9;
goto block_63;
}
else
{
uint8_t x_79; 
lean_inc(x_1);
x_79 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_71);
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_1);
lean_ctor_set(x_49, 0, x_80);
return x_49;
}
else
{
lean_object* x_81; 
lean_free_object(x_49);
lean_inc(x_1);
x_81 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_52);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4;
x_89 = l_Lean_mkApp3(x_88, x_71, x_66, x_87);
lean_ctor_set(x_85, 0, x_89);
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_85);
x_92 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4;
x_93 = l_Lean_mkApp3(x_92, x_71, x_66, x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
}
else
{
lean_dec(x_71);
lean_dec(x_66);
return x_85;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
lean_dec(x_81);
x_96 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7;
x_100 = l_Lean_mkApp3(x_99, x_71, x_66, x_98);
lean_ctor_set(x_96, 0, x_100);
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_96, 0);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_96);
x_103 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7;
x_104 = l_Lean_mkApp3(x_103, x_71, x_66, x_101);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
else
{
lean_dec(x_71);
lean_dec(x_66);
return x_96;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_71);
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_81);
if (x_106 == 0)
{
return x_81;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_81, 0);
x_108 = lean_ctor_get(x_81, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_81);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_72);
lean_free_object(x_49);
x_110 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10;
x_114 = l_Lean_mkApp3(x_113, x_71, x_66, x_112);
lean_ctor_set(x_110, 0, x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_110, 0);
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_110);
x_117 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10;
x_118 = l_Lean_mkApp3(x_117, x_71, x_66, x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
}
else
{
lean_dec(x_71);
lean_dec(x_66);
return x_110;
}
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_66);
lean_ctor_set(x_49, 0, x_120);
return x_49;
}
}
block_63:
{
uint8_t x_61; 
x_61 = l_Lean_Meta_Grind_isIte(x_1);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_Meta_Grind_isDIte(x_1);
x_11 = x_57;
x_12 = x_56;
x_13 = x_58;
x_14 = x_54;
x_15 = x_60;
x_16 = x_55;
x_17 = x_53;
x_18 = x_59;
x_19 = x_52;
x_20 = x_62;
goto block_48;
}
else
{
x_11 = x_57;
x_12 = x_56;
x_13 = x_58;
x_14 = x_54;
x_15 = x_60;
x_16 = x_55;
x_17 = x_53;
x_18 = x_59;
x_19 = x_52;
x_20 = x_61;
goto block_48;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_134; uint8_t x_135; 
x_121 = lean_ctor_get(x_49, 0);
x_122 = lean_ctor_get(x_49, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_49);
x_134 = l_Lean_Expr_cleanupAnnotations(x_121);
x_135 = l_Lean_Expr_isApp(x_134);
if (x_135 == 0)
{
lean_dec(x_134);
x_123 = x_2;
x_124 = x_3;
x_125 = x_4;
x_126 = x_5;
x_127 = x_6;
x_128 = x_7;
x_129 = x_8;
x_130 = x_9;
goto block_133;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
x_137 = l_Lean_Expr_appFnCleanup___redArg(x_134);
x_138 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1;
x_139 = l_Lean_Expr_isConstOf(x_137, x_138);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = l_Lean_Expr_isApp(x_137);
if (x_140 == 0)
{
lean_dec(x_137);
lean_dec(x_136);
x_123 = x_2;
x_124 = x_3;
x_125 = x_4;
x_126 = x_5;
x_127 = x_6;
x_128 = x_7;
x_129 = x_8;
x_130 = x_9;
goto block_133;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
x_142 = l_Lean_Expr_appFnCleanup___redArg(x_137);
x_143 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13;
x_144 = l_Lean_Expr_isConstOf(x_142, x_143);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = l_Lean_Expr_isApp(x_142);
if (x_145 == 0)
{
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_136);
x_123 = x_2;
x_124 = x_3;
x_125 = x_4;
x_126 = x_5;
x_127 = x_6;
x_128 = x_7;
x_129 = x_8;
x_130 = x_9;
goto block_133;
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = l_Lean_Expr_appFnCleanup___redArg(x_142);
x_147 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17;
x_148 = l_Lean_Expr_isConstOf(x_146, x_147);
lean_dec(x_146);
if (x_148 == 0)
{
lean_dec(x_141);
lean_dec(x_136);
x_123 = x_2;
x_124 = x_3;
x_125 = x_4;
x_126 = x_5;
x_127 = x_6;
x_128 = x_7;
x_129 = x_8;
x_130 = x_9;
goto block_133;
}
else
{
uint8_t x_149; 
lean_inc(x_1);
x_149 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_141);
lean_dec(x_136);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_150 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_1);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_122);
return x_151;
}
else
{
lean_object* x_152; 
lean_inc(x_1);
x_152 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_122);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_unbox(x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4;
x_161 = l_Lean_mkApp3(x_160, x_141, x_136, x_157);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_158);
return x_162;
}
else
{
lean_dec(x_141);
lean_dec(x_136);
return x_156;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_152, 1);
lean_inc(x_163);
lean_dec(x_152);
x_164 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7;
x_169 = l_Lean_mkApp3(x_168, x_141, x_136, x_165);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
return x_170;
}
else
{
lean_dec(x_141);
lean_dec(x_136);
return x_164;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_141);
lean_dec(x_136);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_152, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_152, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_173 = x_152;
} else {
 lean_dec_ref(x_152);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
}
else
{
lean_object* x_175; 
lean_dec(x_142);
x_175 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_122);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
x_179 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10;
x_180 = l_Lean_mkApp3(x_179, x_141, x_136, x_176);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_178;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_177);
return x_181;
}
else
{
lean_dec(x_141);
lean_dec(x_136);
return x_175;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_137);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_136);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_122);
return x_183;
}
}
block_133:
{
uint8_t x_131; 
x_131 = l_Lean_Meta_Grind_isIte(x_1);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = l_Lean_Meta_Grind_isDIte(x_1);
x_11 = x_127;
x_12 = x_126;
x_13 = x_128;
x_14 = x_124;
x_15 = x_130;
x_16 = x_125;
x_17 = x_123;
x_18 = x_129;
x_19 = x_122;
x_20 = x_132;
goto block_48;
}
else
{
x_11 = x_127;
x_12 = x_126;
x_13 = x_128;
x_14 = x_124;
x_15 = x_130;
x_16 = x_125;
x_17 = x_123;
x_18 = x_129;
x_19 = x_122;
x_20 = x_131;
goto block_48;
}
}
}
block_48:
{
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_1);
x_21 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_17, x_16, x_18, x_15, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
lean_inc(x_1);
x_29 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_17, x_14, x_16, x_12, x_11, x_13, x_18, x_15, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_dec(x_1);
return x_29;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_41 = lean_unsigned_to_nat(1u);
x_42 = l_Lean_Expr_getAppNumArgs(x_1);
x_43 = lean_nat_sub(x_42, x_41);
lean_dec(x_42);
x_44 = lean_nat_sub(x_43, x_41);
lean_dec(x_43);
x_45 = l_Lean_Expr_getRevArg_x21(x_1, x_44);
lean_dec(x_1);
x_46 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_19);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Grind_getConfig___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Meta_Grind_cases(x_1, x_2, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_16 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_whnfD(x_17, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_getAppFn(x_20);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Meta_Grind_saveCases___redArg(x_23, x_25, x_3, x_4, x_21);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Meta_Grind_cases(x_1, x_2, x_5, x_6, x_7, x_8, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_22);
x_29 = l_Lean_Meta_Grind_cases(x_1, x_2, x_5, x_6, x_7, x_8, x_21);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___Lean_Meta_Grind_splitNext_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_array_to_list(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 13);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 7);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
x_20 = lean_ctor_get(x_1, 8);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 9);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 10);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 11);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 12);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 14);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 15);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_8, 5);
x_29 = lean_array_get_size(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_4);
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_30);
lean_ctor_set(x_8, 5, x_5);
x_31 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_12);
lean_ctor_set(x_31, 2, x_13);
lean_ctor_set(x_31, 3, x_14);
lean_ctor_set(x_31, 4, x_15);
lean_ctor_set(x_31, 5, x_16);
lean_ctor_set(x_31, 6, x_17);
lean_ctor_set(x_31, 7, x_18);
lean_ctor_set(x_31, 8, x_20);
lean_ctor_set(x_31, 9, x_21);
lean_ctor_set(x_31, 10, x_22);
lean_ctor_set(x_31, 11, x_23);
lean_ctor_set(x_31, 12, x_24);
lean_ctor_set(x_31, 13, x_8);
lean_ctor_set(x_31, 14, x_25);
lean_ctor_set(x_31, 15, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*16, x_19);
x_32 = lean_array_push(x_6, x_31);
x_5 = x_11;
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
x_36 = lean_ctor_get(x_8, 2);
x_37 = lean_ctor_get(x_8, 3);
x_38 = lean_ctor_get(x_8, 4);
x_39 = lean_ctor_get(x_8, 5);
x_40 = lean_ctor_get(x_8, 6);
x_41 = lean_ctor_get(x_8, 7);
x_42 = lean_ctor_get(x_8, 8);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_43 = lean_array_get_size(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set(x_44, 3, x_4);
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_44);
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_35);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set(x_45, 3, x_37);
lean_ctor_set(x_45, 4, x_38);
lean_ctor_set(x_45, 5, x_5);
lean_ctor_set(x_45, 6, x_40);
lean_ctor_set(x_45, 7, x_41);
lean_ctor_set(x_45, 8, x_42);
x_46 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_46, 0, x_10);
lean_ctor_set(x_46, 1, x_12);
lean_ctor_set(x_46, 2, x_13);
lean_ctor_set(x_46, 3, x_14);
lean_ctor_set(x_46, 4, x_15);
lean_ctor_set(x_46, 5, x_16);
lean_ctor_set(x_46, 6, x_17);
lean_ctor_set(x_46, 7, x_18);
lean_ctor_set(x_46, 8, x_20);
lean_ctor_set(x_46, 9, x_21);
lean_ctor_set(x_46, 10, x_22);
lean_ctor_set(x_46, 11, x_23);
lean_ctor_set(x_46, 12, x_24);
lean_ctor_set(x_46, 13, x_45);
lean_ctor_set(x_46, 14, x_25);
lean_ctor_set(x_46, 15, x_26);
lean_ctor_set_uint8(x_46, sizeof(void*)*16, x_19);
x_47 = lean_array_push(x_6, x_46);
x_5 = x_11;
x_6 = x_47;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_49 = lean_ctor_get(x_5, 0);
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_5);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 5);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 6);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 7);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
x_59 = lean_ctor_get(x_1, 8);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 9);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 10);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 11);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 12);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 14);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 15);
lean_inc(x_65);
x_66 = lean_ctor_get(x_8, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_8, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_8, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_8, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_8, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_8, 6);
lean_inc(x_72);
x_73 = lean_ctor_get(x_8, 7);
lean_inc(x_73);
x_74 = lean_ctor_get(x_8, 8);
lean_inc(x_74);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 lean_ctor_release(x_8, 6);
 lean_ctor_release(x_8, 7);
 lean_ctor_release(x_8, 8);
 x_75 = x_8;
} else {
 lean_dec_ref(x_8);
 x_75 = lean_box(0);
}
x_76 = lean_array_get_size(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_3);
lean_ctor_set(x_77, 3, x_4);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(0, 9, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_67);
lean_ctor_set(x_79, 2, x_68);
lean_ctor_set(x_79, 3, x_69);
lean_ctor_set(x_79, 4, x_70);
lean_ctor_set(x_79, 5, x_78);
lean_ctor_set(x_79, 6, x_72);
lean_ctor_set(x_79, 7, x_73);
lean_ctor_set(x_79, 8, x_74);
x_80 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_80, 0, x_49);
lean_ctor_set(x_80, 1, x_51);
lean_ctor_set(x_80, 2, x_52);
lean_ctor_set(x_80, 3, x_53);
lean_ctor_set(x_80, 4, x_54);
lean_ctor_set(x_80, 5, x_55);
lean_ctor_set(x_80, 6, x_56);
lean_ctor_set(x_80, 7, x_57);
lean_ctor_set(x_80, 8, x_59);
lean_ctor_set(x_80, 9, x_60);
lean_ctor_set(x_80, 10, x_61);
lean_ctor_set(x_80, 11, x_62);
lean_ctor_set(x_80, 12, x_63);
lean_ctor_set(x_80, 13, x_79);
lean_ctor_set(x_80, 14, x_64);
lean_ctor_set(x_80, 15, x_65);
lean_ctor_set_uint8(x_80, sizeof(void*)*16, x_58);
x_81 = lean_array_push(x_6, x_80);
x_5 = x_50;
x_6 = x_81;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_8, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_21);
lean_ctor_set(x_22, 0, x_17);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set(x_17, 0, x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_15, x_29);
lean_dec(x_15);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Meta_Grind_getGoal___redArg(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1___lam__0___boxed), 9, 0);
lean_inc(x_2);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_st_ref_take(x_2, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
lean_ctor_set(x_22, 0, x_20);
x_26 = lean_st_ref_set(x_2, x_22, x_23);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = l_Lean_Meta_isMatcherAppCore(x_19, x_1);
x_30 = lean_box(x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l_Lean_Meta_isMatcherAppCore(x_19, x_1);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_st_ref_set(x_2, x_36, x_23);
lean_dec(x_2);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = l_Lean_Meta_isMatcherAppCore(x_19, x_1);
x_41 = lean_box(x_40);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_7, 12);
x_19 = lean_st_ref_get(x_16, x_17);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_18);
lean_ctor_set(x_14, 1, x_21);
lean_ctor_set(x_14, 0, x_18);
lean_ctor_set(x_19, 0, x_14);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_18);
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_ctor_get(x_7, 12);
x_28 = lean_st_ref_get(x_25, x_26);
lean_dec(x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
lean_inc(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_7, 2);
x_19 = lean_st_ref_get(x_16, x_17);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_18);
lean_ctor_set(x_14, 1, x_21);
lean_ctor_set(x_14, 0, x_18);
lean_ctor_set(x_19, 0, x_14);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_18);
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_ctor_get(x_7, 2);
x_28 = lean_st_ref_get(x_25, x_26);
lean_dec(x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
lean_inc(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Meta_Grind_getGoal___redArg(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__0___boxed), 9, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_st_ref_take(x_2, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
lean_ctor_set(x_22, 0, x_20);
x_26 = lean_st_ref_set(x_2, x_22, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Meta_Grind_getGoal___redArg(x_2, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__1___boxed), 9, 0);
lean_inc(x_2);
x_33 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_31, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_st_ref_take(x_2, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
lean_ctor_set(x_39, 0, x_37);
x_43 = lean_st_ref_set(x_2, x_39, x_40);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = l_Lean_checkTraceOption(x_19, x_36, x_1);
lean_dec(x_36);
lean_dec(x_19);
x_47 = lean_box(x_46);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = l_Lean_checkTraceOption(x_19, x_36, x_1);
lean_dec(x_36);
lean_dec(x_19);
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_dec(x_39);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_st_ref_set(x_2, x_53, x_40);
lean_dec(x_2);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = l_Lean_checkTraceOption(x_19, x_36, x_1);
lean_dec(x_36);
lean_dec(x_19);
x_58 = lean_box(x_57);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_33);
if (x_60 == 0)
{
return x_33;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_33, 0);
x_62 = lean_ctor_get(x_33, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_33);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
lean_dec(x_22);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_20);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_st_ref_set(x_2, x_65, x_23);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Meta_Grind_getGoal___redArg(x_2, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__1___boxed), 9, 0);
lean_inc(x_2);
x_73 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_71, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_st_ref_take(x_2, x_75);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_st_ref_set(x_2, x_83, x_80);
lean_dec(x_2);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = l_Lean_checkTraceOption(x_19, x_76, x_1);
lean_dec(x_76);
lean_dec(x_19);
x_88 = lean_box(x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_92 = x_73;
} else {
 lean_dec_ref(x_73);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_16);
if (x_94 == 0)
{
return x_16;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_16, 0);
x_96 = lean_ctor_get(x_16, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_16);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_1, x_6, x_7, x_8, x_9, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_18, 1, x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_st_ref_get(x_16, x_28);
lean_dec(x_16);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
static double _init_l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_mk_ref(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_11, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 4);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_21, 4);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; double x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__0;
x_31 = lean_box(0);
x_32 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4;
x_33 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_float(x_33, sizeof(void*)*2, x_30);
lean_ctor_set_float(x_33, sizeof(void*)*2 + 8, x_30);
x_34 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2 + 16, x_34);
x_35 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__1;
x_36 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_20, 1, x_36);
lean_ctor_set(x_20, 0, x_3);
x_37 = l_Lean_PersistentArray_push___redArg(x_29, x_20);
lean_ctor_set(x_22, 0, x_37);
x_38 = lean_st_ref_set(x_11, x_21, x_24);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 1);
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = lean_st_ref_get(x_18, x_40);
lean_dec(x_18);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_box(0);
lean_ctor_set(x_38, 1, x_44);
lean_ctor_set(x_38, 0, x_45);
lean_ctor_set(x_42, 0, x_38);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_box(0);
lean_ctor_set(x_38, 1, x_46);
lean_ctor_set(x_38, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_st_ref_get(x_18, x_50);
lean_dec(x_18);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
else
{
uint64_t x_58; lean_object* x_59; double x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_58 = lean_ctor_get_uint64(x_22, sizeof(void*)*1);
x_59 = lean_ctor_get(x_22, 0);
lean_inc(x_59);
lean_dec(x_22);
x_60 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__0;
x_61 = lean_box(0);
x_62 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4;
x_63 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_float(x_63, sizeof(void*)*2, x_60);
lean_ctor_set_float(x_63, sizeof(void*)*2 + 8, x_60);
x_64 = lean_unbox(x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*2 + 16, x_64);
x_65 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__1;
x_66 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_2);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_20, 1, x_66);
lean_ctor_set(x_20, 0, x_3);
x_67 = l_Lean_PersistentArray_push___redArg(x_59, x_20);
x_68 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set_uint64(x_68, sizeof(void*)*1, x_58);
lean_ctor_set(x_21, 4, x_68);
x_69 = lean_st_ref_set(x_11, x_21, x_24);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_st_ref_get(x_18, x_70);
lean_dec(x_18);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_75;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint64_t x_87; lean_object* x_88; lean_object* x_89; double x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_79 = lean_ctor_get(x_21, 0);
x_80 = lean_ctor_get(x_21, 1);
x_81 = lean_ctor_get(x_21, 2);
x_82 = lean_ctor_get(x_21, 3);
x_83 = lean_ctor_get(x_21, 5);
x_84 = lean_ctor_get(x_21, 6);
x_85 = lean_ctor_get(x_21, 7);
x_86 = lean_ctor_get(x_21, 8);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_21);
x_87 = lean_ctor_get_uint64(x_22, sizeof(void*)*1);
x_88 = lean_ctor_get(x_22, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_89 = x_22;
} else {
 lean_dec_ref(x_22);
 x_89 = lean_box(0);
}
x_90 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__0;
x_91 = lean_box(0);
x_92 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4;
x_93 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set_float(x_93, sizeof(void*)*2, x_90);
lean_ctor_set_float(x_93, sizeof(void*)*2 + 8, x_90);
x_94 = lean_unbox(x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 16, x_94);
x_95 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__1;
x_96 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_2);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_20, 1, x_96);
lean_ctor_set(x_20, 0, x_3);
x_97 = l_Lean_PersistentArray_push___redArg(x_88, x_20);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(0, 1, 8);
} else {
 x_98 = x_89;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set_uint64(x_98, sizeof(void*)*1, x_87);
x_99 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_99, 0, x_79);
lean_ctor_set(x_99, 1, x_80);
lean_ctor_set(x_99, 2, x_81);
lean_ctor_set(x_99, 3, x_82);
lean_ctor_set(x_99, 4, x_98);
lean_ctor_set(x_99, 5, x_83);
lean_ctor_set(x_99, 6, x_84);
lean_ctor_set(x_99, 7, x_85);
lean_ctor_set(x_99, 8, x_86);
x_100 = lean_st_ref_set(x_11, x_99, x_24);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_st_ref_get(x_18, x_101);
lean_dec(x_18);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint64_t x_120; lean_object* x_121; lean_object* x_122; double x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_110 = lean_ctor_get(x_20, 1);
lean_inc(x_110);
lean_dec(x_20);
x_111 = lean_ctor_get(x_21, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_21, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_21, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_21, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_21, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_21, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_21, 7);
lean_inc(x_117);
x_118 = lean_ctor_get(x_21, 8);
lean_inc(x_118);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 lean_ctor_release(x_21, 6);
 lean_ctor_release(x_21, 7);
 lean_ctor_release(x_21, 8);
 x_119 = x_21;
} else {
 lean_dec_ref(x_21);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get_uint64(x_22, sizeof(void*)*1);
x_121 = lean_ctor_get(x_22, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_122 = x_22;
} else {
 lean_dec_ref(x_22);
 x_122 = lean_box(0);
}
x_123 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__0;
x_124 = lean_box(0);
x_125 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4;
x_126 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set_float(x_126, sizeof(void*)*2, x_123);
lean_ctor_set_float(x_126, sizeof(void*)*2 + 8, x_123);
x_127 = lean_unbox(x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*2 + 16, x_127);
x_128 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__1;
x_129 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_2);
lean_ctor_set(x_129, 2, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_3);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_PersistentArray_push___redArg(x_121, x_130);
if (lean_is_scalar(x_122)) {
 x_132 = lean_alloc_ctor(0, 1, 8);
} else {
 x_132 = x_122;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set_uint64(x_132, sizeof(void*)*1, x_120);
if (lean_is_scalar(x_119)) {
 x_133 = lean_alloc_ctor(0, 9, 0);
} else {
 x_133 = x_119;
}
lean_ctor_set(x_133, 0, x_111);
lean_ctor_set(x_133, 1, x_112);
lean_ctor_set(x_133, 2, x_113);
lean_ctor_set(x_133, 3, x_114);
lean_ctor_set(x_133, 4, x_132);
lean_ctor_set(x_133, 5, x_115);
lean_ctor_set(x_133, 6, x_116);
lean_ctor_set(x_133, 7, x_117);
lean_ctor_set(x_133, 8, x_118);
x_134 = lean_st_ref_set(x_11, x_133, x_110);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = lean_st_ref_get(x_18, x_135);
lean_dec(x_18);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = lean_box(0);
if (lean_is_scalar(x_136)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_136;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_138);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_139);
return x_143;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 5);
lean_inc(x_12);
x_13 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__0___boxed), 10, 1);
lean_closure_set(x_17, 0, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_st_ref_take(x_3, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_st_ref_set(x_3, x_24, x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___boxed), 12, 3);
lean_closure_set(x_34, 0, x_1);
lean_closure_set(x_34, 1, x_21);
lean_closure_set(x_34, 2, x_12);
lean_inc(x_3);
x_35 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_st_ref_take(x_3, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_ctor_set(x_41, 0, x_39);
x_45 = lean_st_ref_set(x_3, x_41, x_42);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_38);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_st_ref_set(x_3, x_51, x_42);
lean_dec(x_3);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_38);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
return x_35;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_35, 0);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_35);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_dec(x_24);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_22);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_st_ref_set(x_3, x_61, x_25);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_closure((void*)(l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___boxed), 12, 3);
lean_closure_set(x_68, 0, x_1);
lean_closure_set(x_68, 1, x_21);
lean_closure_set(x_68, 2, x_12);
lean_inc(x_3);
x_69 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_67, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_st_ref_take(x_3, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_st_ref_set(x_3, x_79, x_76);
lean_dec(x_3);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_3);
x_84 = lean_ctor_get(x_69, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_69, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_86 = x_69;
} else {
 lean_dec_ref(x_69);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_18);
if (x_88 == 0)
{
return x_18;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_18, 0);
x_90 = lean_ctor_get(x_18, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_18);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Meta_Grind_updateLastTag(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_st_ref_get(x_16, x_19);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_20);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = l_Lean_Meta_Grind_updateLastTag(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = lean_st_ref_get(x_31, x_34);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_31);
x_33 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_16, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_18, 1, x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_st_ref_get(x_16, x_28);
lean_dec(x_16);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Meta_Grind_markCaseSplitAsResolved(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_st_ref_get(x_17, x_20);
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_21);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_15);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = l_Lean_Meta_Grind_markCaseSplitAsResolved(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_st_ref_get(x_32, x_35);
lean_dec(x_32);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_38);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_32);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_45 = x_34;
} else {
 lean_dec_ref(x_34);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_17, x_21);
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_20);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_15);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
lean_inc(x_32);
x_34 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_32, x_36);
lean_dec(x_32);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_38);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_32);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_45 = x_34;
} else {
 lean_dec_ref(x_34);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_18, x_22);
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_21);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_16, 1, x_26);
lean_ctor_set(x_16, 0, x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_16);
lean_dec(x_18);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_33, x_37);
lean_dec(x_33);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_33);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_46 = x_35;
} else {
 lean_dec_ref(x_35);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_18, x_22);
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_21);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_16, 1, x_26);
lean_ctor_set(x_16, 0, x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_16);
lean_dec(x_18);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_casesWithTrace___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_33, x_37);
lean_dec(x_33);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_33);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_46 = x_35;
} else {
 lean_dec_ref(x_35);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Meta_Grind_casesMatch(x_1, x_2, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_18, x_22);
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_21);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_16, 1, x_26);
lean_ctor_set(x_16, 0, x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_16);
lean_dec(x_18);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = l_Lean_Meta_Grind_casesMatch(x_1, x_2, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_33, x_37);
lean_dec(x_33);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_33);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_46 = x_35;
} else {
 lean_dec_ref(x_35);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_st_ref_get(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_mk_ref(x_17, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Grind_saveSplitDiagInfo___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_11, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = lean_st_ref_get(x_19, x_23);
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_21, 1, x_28);
lean_ctor_set(x_21, 0, x_25);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_21, 1, x_29);
lean_ctor_set(x_21, 0, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_box(0);
x_34 = lean_st_ref_get(x_19, x_32);
lean_dec(x_19);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_splitNext___lam__9___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_splitNext___lam__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", generation: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_splitNext___lam__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_splitNext___lam__9___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_15, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_st_ref_take(x_3, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
lean_ctor_set(x_22, 0, x_20);
x_26 = lean_st_ref_set(x_3, x_22, x_23);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_81; lean_object* x_82; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
lean_dec(x_19);
x_37 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_34);
lean_inc(x_41);
x_81 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__2___boxed), 10, 1);
lean_closure_set(x_81, 0, x_41);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_82 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_40, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_st_ref_take(x_3, x_84);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_246; uint8_t x_247; lean_object* x_248; uint8_t x_571; lean_object* x_572; lean_object* x_576; uint8_t x_577; uint8_t x_583; 
x_91 = lean_ctor_get(x_88, 0);
lean_dec(x_91);
lean_ctor_set(x_88, 0, x_86);
x_92 = lean_st_ref_set(x_3, x_88, x_89);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_41);
x_94 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__3___boxed), 10, 1);
lean_closure_set(x_94, 0, x_41);
lean_inc(x_41);
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__4___boxed), 10, 1);
lean_closure_set(x_95, 0, x_41);
x_576 = lean_unsigned_to_nat(1u);
x_583 = lean_nat_dec_lt(x_576, x_35);
if (x_583 == 0)
{
x_577 = x_36;
goto block_582;
}
else
{
x_577 = x_583;
goto block_582;
}
block_245:
{
lean_object* x_108; 
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_108 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_111 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1(x_41, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_110);
if (lean_obj_tag(x_111) == 0)
{
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_95);
x_112 = lean_ctor_get(x_34, 0);
lean_inc(x_112);
lean_dec(x_34);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Meta_Grind_getGoal___redArg(x_99, x_113);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_114);
lean_inc(x_109);
x_120 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__5___boxed), 11, 2);
lean_closure_set(x_120, 0, x_109);
lean_closure_set(x_120, 1, x_119);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_121 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_118, x_120, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_117);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_st_ref_take(x_99, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = !lean_is_exclusive(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_127, 0);
lean_dec(x_130);
lean_ctor_set(x_127, 0, x_125);
x_131 = lean_st_ref_set(x_99, x_127, x_128);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_42 = x_96;
x_43 = x_97;
x_44 = x_98;
x_45 = x_109;
x_46 = x_124;
x_47 = x_99;
x_48 = x_100;
x_49 = x_101;
x_50 = x_102;
x_51 = x_103;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_132;
goto block_80;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
lean_dec(x_127);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_st_ref_set(x_99, x_134, x_128);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_42 = x_96;
x_43 = x_97;
x_44 = x_98;
x_45 = x_109;
x_46 = x_124;
x_47 = x_99;
x_48 = x_100;
x_49 = x_101;
x_50 = x_102;
x_51 = x_103;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_136;
goto block_80;
}
}
else
{
uint8_t x_137; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_41);
x_137 = !lean_is_exclusive(x_121);
if (x_137 == 0)
{
return x_121;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_121, 0);
x_139 = lean_ctor_get(x_121, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_121);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; uint8_t x_142; 
lean_dec(x_34);
x_141 = lean_ctor_get(x_111, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_111, 1);
lean_inc(x_143);
lean_dec(x_111);
x_144 = l_Lean_Meta_Grind_getGoal___redArg(x_99, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
lean_dec(x_145);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_148 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_147, x_95, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_146);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_st_ref_take(x_99, x_150);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = !lean_is_exclusive(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_157 = lean_ctor_get(x_154, 0);
lean_dec(x_157);
lean_ctor_set(x_154, 0, x_152);
x_158 = lean_st_ref_set(x_99, x_154, x_155);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = l_Lean_Meta_Grind_getGoal___redArg(x_99, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_109);
x_164 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__6___boxed), 11, 2);
lean_closure_set(x_164, 0, x_109);
lean_closure_set(x_164, 1, x_151);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_165 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_163, x_164, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_162);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_st_ref_take(x_99, x_167);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_171, 0);
lean_dec(x_174);
lean_ctor_set(x_171, 0, x_169);
x_175 = lean_st_ref_set(x_99, x_171, x_172);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_42 = x_96;
x_43 = x_97;
x_44 = x_98;
x_45 = x_109;
x_46 = x_168;
x_47 = x_99;
x_48 = x_100;
x_49 = x_101;
x_50 = x_102;
x_51 = x_103;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_176;
goto block_80;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
lean_dec(x_171);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_169);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_st_ref_set(x_99, x_178, x_172);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_42 = x_96;
x_43 = x_97;
x_44 = x_98;
x_45 = x_109;
x_46 = x_168;
x_47 = x_99;
x_48 = x_100;
x_49 = x_101;
x_50 = x_102;
x_51 = x_103;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_180;
goto block_80;
}
}
else
{
uint8_t x_181; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_41);
x_181 = !lean_is_exclusive(x_165);
if (x_181 == 0)
{
return x_165;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_165, 0);
x_183 = lean_ctor_get(x_165, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_165);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_185 = lean_ctor_get(x_154, 1);
lean_inc(x_185);
lean_dec(x_154);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_152);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_st_ref_set(x_99, x_186, x_155);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = l_Lean_Meta_Grind_getGoal___redArg(x_99, x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_109);
x_193 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__6___boxed), 11, 2);
lean_closure_set(x_193, 0, x_109);
lean_closure_set(x_193, 1, x_151);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_194 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_192, x_193, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_191);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_199 = lean_st_ref_take(x_99, x_196);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_198);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_st_ref_set(x_99, x_204, x_201);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_42 = x_96;
x_43 = x_97;
x_44 = x_98;
x_45 = x_109;
x_46 = x_197;
x_47 = x_99;
x_48 = x_100;
x_49 = x_101;
x_50 = x_102;
x_51 = x_103;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_206;
goto block_80;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_41);
x_207 = lean_ctor_get(x_194, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_194, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_209 = x_194;
} else {
 lean_dec_ref(x_194);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_41);
x_211 = !lean_is_exclusive(x_148);
if (x_211 == 0)
{
return x_148;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_148, 0);
x_213 = lean_ctor_get(x_148, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_148);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_95);
x_215 = lean_ctor_get(x_111, 1);
lean_inc(x_215);
lean_dec(x_111);
x_216 = l_Lean_Meta_Grind_getGoal___redArg(x_99, x_215);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_41);
lean_inc(x_109);
x_220 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__7___boxed), 11, 2);
lean_closure_set(x_220, 0, x_109);
lean_closure_set(x_220, 1, x_41);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_221 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_219, x_220, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_218);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_st_ref_take(x_99, x_223);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = !lean_is_exclusive(x_227);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_227, 0);
lean_dec(x_230);
lean_ctor_set(x_227, 0, x_225);
x_231 = lean_st_ref_set(x_99, x_227, x_228);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_42 = x_96;
x_43 = x_97;
x_44 = x_98;
x_45 = x_109;
x_46 = x_224;
x_47 = x_99;
x_48 = x_100;
x_49 = x_101;
x_50 = x_102;
x_51 = x_103;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_232;
goto block_80;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_227, 1);
lean_inc(x_233);
lean_dec(x_227);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_225);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_st_ref_set(x_99, x_234, x_228);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_42 = x_96;
x_43 = x_97;
x_44 = x_98;
x_45 = x_109;
x_46 = x_224;
x_47 = x_99;
x_48 = x_100;
x_49 = x_101;
x_50 = x_102;
x_51 = x_103;
x_52 = x_104;
x_53 = x_105;
x_54 = x_106;
x_55 = x_236;
goto block_80;
}
}
else
{
uint8_t x_237; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_41);
x_237 = !lean_is_exclusive(x_221);
if (x_237 == 0)
{
return x_221;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_221, 0);
x_239 = lean_ctor_get(x_221, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_221);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
}
}
else
{
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
return x_111;
}
}
else
{
uint8_t x_241; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
x_241 = !lean_is_exclusive(x_108);
if (x_241 == 0)
{
return x_108;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_108, 0);
x_243 = lean_ctor_get(x_108, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_108);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
block_570:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_249 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_93);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_248);
lean_inc(x_246);
lean_inc(x_41);
x_253 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__8___boxed), 13, 4);
lean_closure_set(x_253, 0, x_41);
lean_closure_set(x_253, 1, x_246);
lean_closure_set(x_253, 2, x_35);
lean_closure_set(x_253, 3, x_248);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_254 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_252, x_253, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_251);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_st_ref_take(x_3, x_256);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = !lean_is_exclusive(x_259);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_262 = lean_ctor_get(x_259, 0);
lean_dec(x_262);
lean_ctor_set(x_259, 0, x_257);
x_263 = lean_st_ref_set(x_3, x_259, x_260);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_265 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
lean_dec(x_266);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_269 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_268, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_267);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_st_ref_take(x_3, x_271);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = !lean_is_exclusive(x_274);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_274, 0);
lean_dec(x_277);
lean_ctor_set(x_274, 0, x_272);
x_278 = lean_st_ref_set(x_3, x_274, x_275);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_280 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_281 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2(x_280, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_279);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_unbox(x_282);
lean_dec(x_282);
if (x_283 == 0)
{
lean_object* x_284; 
lean_dec(x_85);
lean_dec(x_2);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
lean_dec(x_281);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_284;
goto block_245;
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_281, 1);
lean_inc(x_285);
lean_dec(x_281);
x_286 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_285);
x_287 = !lean_is_exclusive(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_286, 0);
x_289 = lean_ctor_get(x_286, 1);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
lean_dec(x_288);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_291 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_290, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_289);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = !lean_is_exclusive(x_292);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_295 = lean_ctor_get(x_292, 1);
x_296 = lean_ctor_get(x_292, 0);
lean_dec(x_296);
x_297 = lean_st_ref_take(x_3, x_293);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_301 = lean_ctor_get(x_297, 1);
x_302 = lean_ctor_get(x_299, 0);
lean_dec(x_302);
lean_ctor_set(x_299, 0, x_295);
x_303 = lean_st_ref_set(x_3, x_299, x_301);
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_305 = lean_ctor_get(x_303, 1);
x_306 = lean_ctor_get(x_303, 0);
lean_dec(x_306);
x_307 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_41);
x_308 = l_Lean_MessageData_ofExpr(x_41);
lean_ctor_set_tag(x_303, 7);
lean_ctor_set(x_303, 1, x_308);
lean_ctor_set(x_303, 0, x_307);
x_309 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
lean_ctor_set_tag(x_297, 7);
lean_ctor_set(x_297, 1, x_309);
lean_ctor_set(x_297, 0, x_303);
x_310 = l_Nat_reprFast(x_85);
x_311 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_311, 0, x_310);
x_312 = l_Lean_MessageData_ofFormat(x_311);
lean_ctor_set_tag(x_292, 7);
lean_ctor_set(x_292, 1, x_312);
lean_ctor_set(x_292, 0, x_297);
lean_ctor_set_tag(x_286, 7);
lean_ctor_set(x_286, 1, x_307);
lean_ctor_set(x_286, 0, x_292);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_313 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_280, x_286, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_305);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_314;
goto block_245;
}
else
{
uint8_t x_315; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_315 = !lean_is_exclusive(x_313);
if (x_315 == 0)
{
return x_313;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_313, 0);
x_317 = lean_ctor_get(x_313, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_313);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = lean_ctor_get(x_303, 1);
lean_inc(x_319);
lean_dec(x_303);
x_320 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_41);
x_321 = l_Lean_MessageData_ofExpr(x_41);
x_322 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
lean_ctor_set_tag(x_297, 7);
lean_ctor_set(x_297, 1, x_323);
lean_ctor_set(x_297, 0, x_322);
x_324 = l_Nat_reprFast(x_85);
x_325 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = l_Lean_MessageData_ofFormat(x_325);
lean_ctor_set_tag(x_292, 7);
lean_ctor_set(x_292, 1, x_326);
lean_ctor_set(x_292, 0, x_297);
lean_ctor_set_tag(x_286, 7);
lean_ctor_set(x_286, 1, x_320);
lean_ctor_set(x_286, 0, x_292);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_327 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_280, x_286, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_319);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; 
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_328;
goto block_245;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_329 = lean_ctor_get(x_327, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_327, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_331 = x_327;
} else {
 lean_dec_ref(x_327);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_333 = lean_ctor_get(x_297, 1);
x_334 = lean_ctor_get(x_299, 1);
lean_inc(x_334);
lean_dec(x_299);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_295);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_st_ref_set(x_3, x_335, x_333);
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_338 = x_336;
} else {
 lean_dec_ref(x_336);
 x_338 = lean_box(0);
}
x_339 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_41);
x_340 = l_Lean_MessageData_ofExpr(x_41);
if (lean_is_scalar(x_338)) {
 x_341 = lean_alloc_ctor(7, 2, 0);
} else {
 x_341 = x_338;
 lean_ctor_set_tag(x_341, 7);
}
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_342 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
lean_ctor_set_tag(x_297, 7);
lean_ctor_set(x_297, 1, x_342);
lean_ctor_set(x_297, 0, x_341);
x_343 = l_Nat_reprFast(x_85);
x_344 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_344, 0, x_343);
x_345 = l_Lean_MessageData_ofFormat(x_344);
lean_ctor_set_tag(x_292, 7);
lean_ctor_set(x_292, 1, x_345);
lean_ctor_set(x_292, 0, x_297);
lean_ctor_set_tag(x_286, 7);
lean_ctor_set(x_286, 1, x_339);
lean_ctor_set(x_286, 0, x_292);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_346 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_280, x_286, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_337);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; 
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
lean_dec(x_346);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_347;
goto block_245;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_348 = lean_ctor_get(x_346, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_350 = x_346;
} else {
 lean_dec_ref(x_346);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_352 = lean_ctor_get(x_297, 0);
x_353 = lean_ctor_get(x_297, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_297);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_355 = x_352;
} else {
 lean_dec_ref(x_352);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_295);
lean_ctor_set(x_356, 1, x_354);
x_357 = lean_st_ref_set(x_3, x_356, x_353);
x_358 = lean_ctor_get(x_357, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_359 = x_357;
} else {
 lean_dec_ref(x_357);
 x_359 = lean_box(0);
}
x_360 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_41);
x_361 = l_Lean_MessageData_ofExpr(x_41);
if (lean_is_scalar(x_359)) {
 x_362 = lean_alloc_ctor(7, 2, 0);
} else {
 x_362 = x_359;
 lean_ctor_set_tag(x_362, 7);
}
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
x_363 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
x_364 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
x_365 = l_Nat_reprFast(x_85);
x_366 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_366, 0, x_365);
x_367 = l_Lean_MessageData_ofFormat(x_366);
lean_ctor_set_tag(x_292, 7);
lean_ctor_set(x_292, 1, x_367);
lean_ctor_set(x_292, 0, x_364);
lean_ctor_set_tag(x_286, 7);
lean_ctor_set(x_286, 1, x_360);
lean_ctor_set(x_286, 0, x_292);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_368 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_280, x_286, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_358);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; 
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_369;
goto block_245;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_372 = x_368;
} else {
 lean_dec_ref(x_368);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_374 = lean_ctor_get(x_292, 1);
lean_inc(x_374);
lean_dec(x_292);
x_375 = lean_st_ref_take(x_3, x_293);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_376, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_380 = x_376;
} else {
 lean_dec_ref(x_376);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_374);
lean_ctor_set(x_381, 1, x_379);
x_382 = lean_st_ref_set(x_3, x_381, x_377);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
x_385 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_41);
x_386 = l_Lean_MessageData_ofExpr(x_41);
if (lean_is_scalar(x_384)) {
 x_387 = lean_alloc_ctor(7, 2, 0);
} else {
 x_387 = x_384;
 lean_ctor_set_tag(x_387, 7);
}
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_378)) {
 x_389 = lean_alloc_ctor(7, 2, 0);
} else {
 x_389 = x_378;
 lean_ctor_set_tag(x_389, 7);
}
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = l_Nat_reprFast(x_85);
x_391 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_391, 0, x_390);
x_392 = l_Lean_MessageData_ofFormat(x_391);
x_393 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_393, 0, x_389);
lean_ctor_set(x_393, 1, x_392);
lean_ctor_set_tag(x_286, 7);
lean_ctor_set(x_286, 1, x_385);
lean_ctor_set(x_286, 0, x_393);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_394 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_280, x_286, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_383);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; 
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_395;
goto block_245;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_396 = lean_ctor_get(x_394, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_394, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_398 = x_394;
} else {
 lean_dec_ref(x_394);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
}
else
{
uint8_t x_400; 
lean_free_object(x_286);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_400 = !lean_is_exclusive(x_291);
if (x_400 == 0)
{
return x_291;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_291, 0);
x_402 = lean_ctor_get(x_291, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_291);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_404 = lean_ctor_get(x_286, 0);
x_405 = lean_ctor_get(x_286, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_286);
x_406 = lean_ctor_get(x_404, 0);
lean_inc(x_406);
lean_dec(x_404);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_407 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_406, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_405);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_411 = x_408;
} else {
 lean_dec_ref(x_408);
 x_411 = lean_box(0);
}
x_412 = lean_st_ref_take(x_3, x_409);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_415 = x_412;
} else {
 lean_dec_ref(x_412);
 x_415 = lean_box(0);
}
x_416 = lean_ctor_get(x_413, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_417 = x_413;
} else {
 lean_dec_ref(x_413);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_410);
lean_ctor_set(x_418, 1, x_416);
x_419 = lean_st_ref_set(x_3, x_418, x_414);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_421 = x_419;
} else {
 lean_dec_ref(x_419);
 x_421 = lean_box(0);
}
x_422 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_41);
x_423 = l_Lean_MessageData_ofExpr(x_41);
if (lean_is_scalar(x_421)) {
 x_424 = lean_alloc_ctor(7, 2, 0);
} else {
 x_424 = x_421;
 lean_ctor_set_tag(x_424, 7);
}
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_415)) {
 x_426 = lean_alloc_ctor(7, 2, 0);
} else {
 x_426 = x_415;
 lean_ctor_set_tag(x_426, 7);
}
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
x_427 = l_Nat_reprFast(x_85);
x_428 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_428, 0, x_427);
x_429 = l_Lean_MessageData_ofFormat(x_428);
if (lean_is_scalar(x_411)) {
 x_430 = lean_alloc_ctor(7, 2, 0);
} else {
 x_430 = x_411;
 lean_ctor_set_tag(x_430, 7);
}
lean_ctor_set(x_430, 0, x_426);
lean_ctor_set(x_430, 1, x_429);
x_431 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_422);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_432 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_280, x_431, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_420);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; 
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_433;
goto block_245;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_436 = x_432;
} else {
 lean_dec_ref(x_432);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_438 = lean_ctor_get(x_407, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_407, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_440 = x_407;
} else {
 lean_dec_ref(x_407);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
}
}
else
{
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_281;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_442 = lean_ctor_get(x_274, 1);
lean_inc(x_442);
lean_dec(x_274);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_272);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_st_ref_set(x_3, x_443, x_275);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec(x_444);
x_446 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_447 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2(x_446, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_445);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; uint8_t x_449; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_unbox(x_448);
lean_dec(x_448);
if (x_449 == 0)
{
lean_object* x_450; 
lean_dec(x_85);
lean_dec(x_2);
x_450 = lean_ctor_get(x_447, 1);
lean_inc(x_450);
lean_dec(x_447);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_450;
goto block_245;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_451 = lean_ctor_get(x_447, 1);
lean_inc(x_451);
lean_dec(x_447);
x_452 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_451);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_455 = x_452;
} else {
 lean_dec_ref(x_452);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_453, 0);
lean_inc(x_456);
lean_dec(x_453);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_457 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_456, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_454);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_461 = x_458;
} else {
 lean_dec_ref(x_458);
 x_461 = lean_box(0);
}
x_462 = lean_st_ref_take(x_3, x_459);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_465 = x_462;
} else {
 lean_dec_ref(x_462);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_467 = x_463;
} else {
 lean_dec_ref(x_463);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_460);
lean_ctor_set(x_468, 1, x_466);
x_469 = lean_st_ref_set(x_3, x_468, x_464);
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_471 = x_469;
} else {
 lean_dec_ref(x_469);
 x_471 = lean_box(0);
}
x_472 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_41);
x_473 = l_Lean_MessageData_ofExpr(x_41);
if (lean_is_scalar(x_471)) {
 x_474 = lean_alloc_ctor(7, 2, 0);
} else {
 x_474 = x_471;
 lean_ctor_set_tag(x_474, 7);
}
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
x_475 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_465)) {
 x_476 = lean_alloc_ctor(7, 2, 0);
} else {
 x_476 = x_465;
 lean_ctor_set_tag(x_476, 7);
}
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_475);
x_477 = l_Nat_reprFast(x_85);
x_478 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_478, 0, x_477);
x_479 = l_Lean_MessageData_ofFormat(x_478);
if (lean_is_scalar(x_461)) {
 x_480 = lean_alloc_ctor(7, 2, 0);
} else {
 x_480 = x_461;
 lean_ctor_set_tag(x_480, 7);
}
lean_ctor_set(x_480, 0, x_476);
lean_ctor_set(x_480, 1, x_479);
if (lean_is_scalar(x_455)) {
 x_481 = lean_alloc_ctor(7, 2, 0);
} else {
 x_481 = x_455;
 lean_ctor_set_tag(x_481, 7);
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_472);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_482 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_446, x_481, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_470);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; 
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
lean_dec(x_482);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_483;
goto block_245;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_482, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_486 = x_482;
} else {
 lean_dec_ref(x_482);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 2, 0);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_485);
return x_487;
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_455);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_488 = lean_ctor_get(x_457, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_457, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_490 = x_457;
} else {
 lean_dec_ref(x_457);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_489);
return x_491;
}
}
}
else
{
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_447;
}
}
}
else
{
uint8_t x_492; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_492 = !lean_is_exclusive(x_269);
if (x_492 == 0)
{
return x_269;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_269, 0);
x_494 = lean_ctor_get(x_269, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_269);
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
return x_495;
}
}
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_496 = lean_ctor_get(x_259, 1);
lean_inc(x_496);
lean_dec(x_259);
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_257);
lean_ctor_set(x_497, 1, x_496);
x_498 = lean_st_ref_set(x_3, x_497, x_260);
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
lean_dec(x_498);
x_500 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_499);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_ctor_get(x_501, 0);
lean_inc(x_503);
lean_dec(x_501);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_504 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_503, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_502);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_st_ref_take(x_3, x_506);
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_512 = x_509;
} else {
 lean_dec_ref(x_509);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_507);
lean_ctor_set(x_513, 1, x_511);
x_514 = lean_st_ref_set(x_3, x_513, x_510);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec(x_514);
x_516 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_517 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2(x_516, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_515);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; uint8_t x_519; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_unbox(x_518);
lean_dec(x_518);
if (x_519 == 0)
{
lean_object* x_520; 
lean_dec(x_85);
lean_dec(x_2);
x_520 = lean_ctor_get(x_517, 1);
lean_inc(x_520);
lean_dec(x_517);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_520;
goto block_245;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_521 = lean_ctor_get(x_517, 1);
lean_inc(x_521);
lean_dec(x_517);
x_522 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_521);
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_525 = x_522;
} else {
 lean_dec_ref(x_522);
 x_525 = lean_box(0);
}
x_526 = lean_ctor_get(x_523, 0);
lean_inc(x_526);
lean_dec(x_523);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_527 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_526, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_524);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_531 = x_528;
} else {
 lean_dec_ref(x_528);
 x_531 = lean_box(0);
}
x_532 = lean_st_ref_take(x_3, x_529);
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_535 = x_532;
} else {
 lean_dec_ref(x_532);
 x_535 = lean_box(0);
}
x_536 = lean_ctor_get(x_533, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_537 = x_533;
} else {
 lean_dec_ref(x_533);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_530);
lean_ctor_set(x_538, 1, x_536);
x_539 = lean_st_ref_set(x_3, x_538, x_534);
x_540 = lean_ctor_get(x_539, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_541 = x_539;
} else {
 lean_dec_ref(x_539);
 x_541 = lean_box(0);
}
x_542 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_41);
x_543 = l_Lean_MessageData_ofExpr(x_41);
if (lean_is_scalar(x_541)) {
 x_544 = lean_alloc_ctor(7, 2, 0);
} else {
 x_544 = x_541;
 lean_ctor_set_tag(x_544, 7);
}
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
x_545 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_535)) {
 x_546 = lean_alloc_ctor(7, 2, 0);
} else {
 x_546 = x_535;
 lean_ctor_set_tag(x_546, 7);
}
lean_ctor_set(x_546, 0, x_544);
lean_ctor_set(x_546, 1, x_545);
x_547 = l_Nat_reprFast(x_85);
x_548 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_548, 0, x_547);
x_549 = l_Lean_MessageData_ofFormat(x_548);
if (lean_is_scalar(x_531)) {
 x_550 = lean_alloc_ctor(7, 2, 0);
} else {
 x_550 = x_531;
 lean_ctor_set_tag(x_550, 7);
}
lean_ctor_set(x_550, 0, x_546);
lean_ctor_set(x_550, 1, x_549);
if (lean_is_scalar(x_525)) {
 x_551 = lean_alloc_ctor(7, 2, 0);
} else {
 x_551 = x_525;
 lean_ctor_set_tag(x_551, 7);
}
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_542);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_552 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_516, x_551, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_540);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; 
x_553 = lean_ctor_get(x_552, 1);
lean_inc(x_553);
lean_dec(x_552);
x_96 = x_247;
x_97 = x_248;
x_98 = x_246;
x_99 = x_3;
x_100 = x_4;
x_101 = x_5;
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_10;
x_107 = x_553;
goto block_245;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_554 = lean_ctor_get(x_552, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_552, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_556 = x_552;
} else {
 lean_dec_ref(x_552);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(1, 2, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_554);
lean_ctor_set(x_557, 1, x_555);
return x_557;
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_525);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_558 = lean_ctor_get(x_527, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_527, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_560 = x_527;
} else {
 lean_dec_ref(x_527);
 x_560 = lean_box(0);
}
if (lean_is_scalar(x_560)) {
 x_561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_561 = x_560;
}
lean_ctor_set(x_561, 0, x_558);
lean_ctor_set(x_561, 1, x_559);
return x_561;
}
}
}
else
{
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_517;
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_562 = lean_ctor_get(x_504, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_504, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_564 = x_504;
} else {
 lean_dec_ref(x_504);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(1, 2, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_562);
lean_ctor_set(x_565, 1, x_563);
return x_565;
}
}
}
else
{
uint8_t x_566; 
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_566 = !lean_is_exclusive(x_254);
if (x_566 == 0)
{
return x_254;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_254, 0);
x_568 = lean_ctor_get(x_254, 1);
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_254);
x_569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_569, 0, x_567);
lean_ctor_set(x_569, 1, x_568);
return x_569;
}
}
}
block_575:
{
if (lean_obj_tag(x_34) == 2)
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_34, 4);
lean_inc(x_573);
x_246 = x_572;
x_247 = x_571;
x_248 = x_573;
goto block_570;
}
else
{
lean_object* x_574; 
x_574 = lean_ctor_get(x_34, 1);
lean_inc(x_574);
x_246 = x_572;
x_247 = x_571;
x_248 = x_574;
goto block_570;
}
}
block_582:
{
lean_object* x_578; 
x_578 = lean_box(1);
if (x_577 == 0)
{
uint8_t x_579; 
x_579 = lean_unbox(x_578);
lean_inc(x_85);
x_571 = x_579;
x_572 = x_85;
goto block_575;
}
else
{
lean_object* x_580; uint8_t x_581; 
x_580 = lean_nat_add(x_85, x_576);
x_581 = lean_unbox(x_578);
x_571 = x_581;
x_572 = x_580;
goto block_575;
}
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_706; uint8_t x_707; lean_object* x_708; uint8_t x_797; lean_object* x_798; lean_object* x_802; uint8_t x_803; uint8_t x_809; 
x_584 = lean_ctor_get(x_88, 1);
lean_inc(x_584);
lean_dec(x_88);
x_585 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_585, 0, x_86);
lean_ctor_set(x_585, 1, x_584);
x_586 = lean_st_ref_set(x_3, x_585, x_89);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
lean_dec(x_586);
lean_inc(x_41);
x_588 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__3___boxed), 10, 1);
lean_closure_set(x_588, 0, x_41);
lean_inc(x_41);
x_589 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__4___boxed), 10, 1);
lean_closure_set(x_589, 0, x_41);
x_802 = lean_unsigned_to_nat(1u);
x_809 = lean_nat_dec_lt(x_802, x_35);
if (x_809 == 0)
{
x_803 = x_36;
goto block_808;
}
else
{
x_803 = x_809;
goto block_808;
}
block_705:
{
lean_object* x_602; 
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
x_602 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(x_593, x_594, x_595, x_596, x_597, x_598, x_599, x_600, x_601);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
x_605 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1(x_41, x_593, x_594, x_595, x_596, x_597, x_598, x_599, x_600, x_604);
if (lean_obj_tag(x_605) == 0)
{
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_589);
x_606 = lean_ctor_get(x_34, 0);
lean_inc(x_606);
lean_dec(x_34);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec(x_605);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_609 = l_Lean_Meta_Grind_getGoal___redArg(x_593, x_607);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = lean_ctor_get(x_610, 0);
lean_inc(x_612);
lean_dec(x_610);
x_613 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_608);
lean_inc(x_603);
x_614 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__5___boxed), 11, 2);
lean_closure_set(x_614, 0, x_603);
lean_closure_set(x_614, 1, x_613);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
x_615 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_612, x_614, x_593, x_594, x_595, x_596, x_597, x_598, x_599, x_600, x_611);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec(x_615);
x_618 = lean_ctor_get(x_616, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_616, 1);
lean_inc(x_619);
lean_dec(x_616);
x_620 = lean_st_ref_take(x_593, x_617);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_624 = x_621;
} else {
 lean_dec_ref(x_621);
 x_624 = lean_box(0);
}
if (lean_is_scalar(x_624)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_624;
}
lean_ctor_set(x_625, 0, x_619);
lean_ctor_set(x_625, 1, x_623);
x_626 = lean_st_ref_set(x_593, x_625, x_622);
x_627 = lean_ctor_get(x_626, 1);
lean_inc(x_627);
lean_dec(x_626);
x_42 = x_590;
x_43 = x_591;
x_44 = x_592;
x_45 = x_603;
x_46 = x_618;
x_47 = x_593;
x_48 = x_594;
x_49 = x_595;
x_50 = x_596;
x_51 = x_597;
x_52 = x_598;
x_53 = x_599;
x_54 = x_600;
x_55 = x_627;
goto block_80;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_603);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_41);
x_628 = lean_ctor_get(x_615, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_615, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_630 = x_615;
} else {
 lean_dec_ref(x_615);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(1, 2, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_628);
lean_ctor_set(x_631, 1, x_629);
return x_631;
}
}
else
{
lean_object* x_632; uint8_t x_633; 
lean_dec(x_34);
x_632 = lean_ctor_get(x_605, 0);
lean_inc(x_632);
x_633 = lean_unbox(x_632);
lean_dec(x_632);
if (x_633 == 0)
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_634 = lean_ctor_get(x_605, 1);
lean_inc(x_634);
lean_dec(x_605);
x_635 = l_Lean_Meta_Grind_getGoal___redArg(x_593, x_634);
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_ctor_get(x_636, 0);
lean_inc(x_638);
lean_dec(x_636);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
x_639 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_638, x_589, x_593, x_594, x_595, x_596, x_597, x_598, x_599, x_600, x_637);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
lean_dec(x_639);
x_642 = lean_ctor_get(x_640, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_640, 1);
lean_inc(x_643);
lean_dec(x_640);
x_644 = lean_st_ref_take(x_593, x_641);
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec(x_644);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_648 = x_645;
} else {
 lean_dec_ref(x_645);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_643);
lean_ctor_set(x_649, 1, x_647);
x_650 = lean_st_ref_set(x_593, x_649, x_646);
x_651 = lean_ctor_get(x_650, 1);
lean_inc(x_651);
lean_dec(x_650);
x_652 = l_Lean_Meta_Grind_getGoal___redArg(x_593, x_651);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
x_655 = lean_ctor_get(x_653, 0);
lean_inc(x_655);
lean_dec(x_653);
lean_inc(x_603);
x_656 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__6___boxed), 11, 2);
lean_closure_set(x_656, 0, x_603);
lean_closure_set(x_656, 1, x_642);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
x_657 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_655, x_656, x_593, x_594, x_595, x_596, x_597, x_598, x_599, x_600, x_654);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
x_660 = lean_ctor_get(x_658, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_658, 1);
lean_inc(x_661);
lean_dec(x_658);
x_662 = lean_st_ref_take(x_593, x_659);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
lean_dec(x_662);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_666 = x_663;
} else {
 lean_dec_ref(x_663);
 x_666 = lean_box(0);
}
if (lean_is_scalar(x_666)) {
 x_667 = lean_alloc_ctor(0, 2, 0);
} else {
 x_667 = x_666;
}
lean_ctor_set(x_667, 0, x_661);
lean_ctor_set(x_667, 1, x_665);
x_668 = lean_st_ref_set(x_593, x_667, x_664);
x_669 = lean_ctor_get(x_668, 1);
lean_inc(x_669);
lean_dec(x_668);
x_42 = x_590;
x_43 = x_591;
x_44 = x_592;
x_45 = x_603;
x_46 = x_660;
x_47 = x_593;
x_48 = x_594;
x_49 = x_595;
x_50 = x_596;
x_51 = x_597;
x_52 = x_598;
x_53 = x_599;
x_54 = x_600;
x_55 = x_669;
goto block_80;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_603);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_41);
x_670 = lean_ctor_get(x_657, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_657, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_672 = x_657;
} else {
 lean_dec_ref(x_657);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(1, 2, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_670);
lean_ctor_set(x_673, 1, x_671);
return x_673;
}
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
lean_dec(x_603);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_41);
x_674 = lean_ctor_get(x_639, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_639, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_676 = x_639;
} else {
 lean_dec_ref(x_639);
 x_676 = lean_box(0);
}
if (lean_is_scalar(x_676)) {
 x_677 = lean_alloc_ctor(1, 2, 0);
} else {
 x_677 = x_676;
}
lean_ctor_set(x_677, 0, x_674);
lean_ctor_set(x_677, 1, x_675);
return x_677;
}
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_589);
x_678 = lean_ctor_get(x_605, 1);
lean_inc(x_678);
lean_dec(x_605);
x_679 = l_Lean_Meta_Grind_getGoal___redArg(x_593, x_678);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
lean_dec(x_679);
x_682 = lean_ctor_get(x_680, 0);
lean_inc(x_682);
lean_dec(x_680);
lean_inc(x_41);
lean_inc(x_603);
x_683 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__7___boxed), 11, 2);
lean_closure_set(x_683, 0, x_603);
lean_closure_set(x_683, 1, x_41);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
x_684 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_682, x_683, x_593, x_594, x_595, x_596, x_597, x_598, x_599, x_600, x_681);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
lean_dec(x_684);
x_687 = lean_ctor_get(x_685, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_685, 1);
lean_inc(x_688);
lean_dec(x_685);
x_689 = lean_st_ref_take(x_593, x_686);
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec(x_689);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_693 = x_690;
} else {
 lean_dec_ref(x_690);
 x_693 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_694 = lean_alloc_ctor(0, 2, 0);
} else {
 x_694 = x_693;
}
lean_ctor_set(x_694, 0, x_688);
lean_ctor_set(x_694, 1, x_692);
x_695 = lean_st_ref_set(x_593, x_694, x_691);
x_696 = lean_ctor_get(x_695, 1);
lean_inc(x_696);
lean_dec(x_695);
x_42 = x_590;
x_43 = x_591;
x_44 = x_592;
x_45 = x_603;
x_46 = x_687;
x_47 = x_593;
x_48 = x_594;
x_49 = x_595;
x_50 = x_596;
x_51 = x_597;
x_52 = x_598;
x_53 = x_599;
x_54 = x_600;
x_55 = x_696;
goto block_80;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_603);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_41);
x_697 = lean_ctor_get(x_684, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_684, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_699 = x_684;
} else {
 lean_dec_ref(x_684);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(1, 2, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_697);
lean_ctor_set(x_700, 1, x_698);
return x_700;
}
}
}
}
else
{
lean_dec(x_603);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_589);
lean_dec(x_41);
lean_dec(x_34);
return x_605;
}
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_589);
lean_dec(x_41);
lean_dec(x_34);
x_701 = lean_ctor_get(x_602, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_602, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_703 = x_602;
} else {
 lean_dec_ref(x_602);
 x_703 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_704 = lean_alloc_ctor(1, 2, 0);
} else {
 x_704 = x_703;
}
lean_ctor_set(x_704, 0, x_701);
lean_ctor_set(x_704, 1, x_702);
return x_704;
}
}
block_796:
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_709 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_587);
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec(x_709);
x_712 = lean_ctor_get(x_710, 0);
lean_inc(x_712);
lean_dec(x_710);
lean_inc(x_708);
lean_inc(x_706);
lean_inc(x_41);
x_713 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__8___boxed), 13, 4);
lean_closure_set(x_713, 0, x_41);
lean_closure_set(x_713, 1, x_706);
lean_closure_set(x_713, 2, x_35);
lean_closure_set(x_713, 3, x_708);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_714 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_712, x_713, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_711);
if (lean_obj_tag(x_714) == 0)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_714, 1);
lean_inc(x_716);
lean_dec(x_714);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_718 = lean_st_ref_take(x_3, x_716);
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_722 = x_719;
} else {
 lean_dec_ref(x_719);
 x_722 = lean_box(0);
}
if (lean_is_scalar(x_722)) {
 x_723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_723 = x_722;
}
lean_ctor_set(x_723, 0, x_717);
lean_ctor_set(x_723, 1, x_721);
x_724 = lean_st_ref_set(x_3, x_723, x_720);
x_725 = lean_ctor_get(x_724, 1);
lean_inc(x_725);
lean_dec(x_724);
x_726 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_725);
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_726, 1);
lean_inc(x_728);
lean_dec(x_726);
x_729 = lean_ctor_get(x_727, 0);
lean_inc(x_729);
lean_dec(x_727);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_730 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_729, x_588, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_728);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec(x_731);
x_734 = lean_st_ref_take(x_3, x_732);
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_738 = x_735;
} else {
 lean_dec_ref(x_735);
 x_738 = lean_box(0);
}
if (lean_is_scalar(x_738)) {
 x_739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_739 = x_738;
}
lean_ctor_set(x_739, 0, x_733);
lean_ctor_set(x_739, 1, x_737);
x_740 = lean_st_ref_set(x_3, x_739, x_736);
x_741 = lean_ctor_get(x_740, 1);
lean_inc(x_741);
lean_dec(x_740);
x_742 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_743 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2(x_742, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_741);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; uint8_t x_745; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_unbox(x_744);
lean_dec(x_744);
if (x_745 == 0)
{
lean_object* x_746; 
lean_dec(x_85);
lean_dec(x_2);
x_746 = lean_ctor_get(x_743, 1);
lean_inc(x_746);
lean_dec(x_743);
x_590 = x_707;
x_591 = x_708;
x_592 = x_706;
x_593 = x_3;
x_594 = x_4;
x_595 = x_5;
x_596 = x_6;
x_597 = x_7;
x_598 = x_8;
x_599 = x_9;
x_600 = x_10;
x_601 = x_746;
goto block_705;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_747 = lean_ctor_get(x_743, 1);
lean_inc(x_747);
lean_dec(x_743);
x_748 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_747);
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_751 = x_748;
} else {
 lean_dec_ref(x_748);
 x_751 = lean_box(0);
}
x_752 = lean_ctor_get(x_749, 0);
lean_inc(x_752);
lean_dec(x_749);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_753 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_752, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_750);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
lean_dec(x_753);
x_756 = lean_ctor_get(x_754, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_754)) {
 lean_ctor_release(x_754, 0);
 lean_ctor_release(x_754, 1);
 x_757 = x_754;
} else {
 lean_dec_ref(x_754);
 x_757 = lean_box(0);
}
x_758 = lean_st_ref_take(x_3, x_755);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_761 = x_758;
} else {
 lean_dec_ref(x_758);
 x_761 = lean_box(0);
}
x_762 = lean_ctor_get(x_759, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 x_763 = x_759;
} else {
 lean_dec_ref(x_759);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(0, 2, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_756);
lean_ctor_set(x_764, 1, x_762);
x_765 = lean_st_ref_set(x_3, x_764, x_760);
x_766 = lean_ctor_get(x_765, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_765)) {
 lean_ctor_release(x_765, 0);
 lean_ctor_release(x_765, 1);
 x_767 = x_765;
} else {
 lean_dec_ref(x_765);
 x_767 = lean_box(0);
}
x_768 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_41);
x_769 = l_Lean_MessageData_ofExpr(x_41);
if (lean_is_scalar(x_767)) {
 x_770 = lean_alloc_ctor(7, 2, 0);
} else {
 x_770 = x_767;
 lean_ctor_set_tag(x_770, 7);
}
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
x_771 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_761)) {
 x_772 = lean_alloc_ctor(7, 2, 0);
} else {
 x_772 = x_761;
 lean_ctor_set_tag(x_772, 7);
}
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
x_773 = l_Nat_reprFast(x_85);
x_774 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_774, 0, x_773);
x_775 = l_Lean_MessageData_ofFormat(x_774);
if (lean_is_scalar(x_757)) {
 x_776 = lean_alloc_ctor(7, 2, 0);
} else {
 x_776 = x_757;
 lean_ctor_set_tag(x_776, 7);
}
lean_ctor_set(x_776, 0, x_772);
lean_ctor_set(x_776, 1, x_775);
if (lean_is_scalar(x_751)) {
 x_777 = lean_alloc_ctor(7, 2, 0);
} else {
 x_777 = x_751;
 lean_ctor_set_tag(x_777, 7);
}
lean_ctor_set(x_777, 0, x_776);
lean_ctor_set(x_777, 1, x_768);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_778 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_742, x_777, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_766);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; 
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
lean_dec(x_778);
x_590 = x_707;
x_591 = x_708;
x_592 = x_706;
x_593 = x_3;
x_594 = x_4;
x_595 = x_5;
x_596 = x_6;
x_597 = x_7;
x_598 = x_8;
x_599 = x_9;
x_600 = x_10;
x_601 = x_779;
goto block_705;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_708);
lean_dec(x_706);
lean_dec(x_589);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_780 = lean_ctor_get(x_778, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_778, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_782 = x_778;
} else {
 lean_dec_ref(x_778);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(1, 2, 0);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_780);
lean_ctor_set(x_783, 1, x_781);
return x_783;
}
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_751);
lean_dec(x_708);
lean_dec(x_706);
lean_dec(x_589);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_784 = lean_ctor_get(x_753, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_753, 1);
lean_inc(x_785);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_786 = x_753;
} else {
 lean_dec_ref(x_753);
 x_786 = lean_box(0);
}
if (lean_is_scalar(x_786)) {
 x_787 = lean_alloc_ctor(1, 2, 0);
} else {
 x_787 = x_786;
}
lean_ctor_set(x_787, 0, x_784);
lean_ctor_set(x_787, 1, x_785);
return x_787;
}
}
}
else
{
lean_dec(x_708);
lean_dec(x_706);
lean_dec(x_589);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_743;
}
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; 
lean_dec(x_708);
lean_dec(x_706);
lean_dec(x_589);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_788 = lean_ctor_get(x_730, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_730, 1);
lean_inc(x_789);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_790 = x_730;
} else {
 lean_dec_ref(x_730);
 x_790 = lean_box(0);
}
if (lean_is_scalar(x_790)) {
 x_791 = lean_alloc_ctor(1, 2, 0);
} else {
 x_791 = x_790;
}
lean_ctor_set(x_791, 0, x_788);
lean_ctor_set(x_791, 1, x_789);
return x_791;
}
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_708);
lean_dec(x_706);
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_85);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_792 = lean_ctor_get(x_714, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_714, 1);
lean_inc(x_793);
if (lean_is_exclusive(x_714)) {
 lean_ctor_release(x_714, 0);
 lean_ctor_release(x_714, 1);
 x_794 = x_714;
} else {
 lean_dec_ref(x_714);
 x_794 = lean_box(0);
}
if (lean_is_scalar(x_794)) {
 x_795 = lean_alloc_ctor(1, 2, 0);
} else {
 x_795 = x_794;
}
lean_ctor_set(x_795, 0, x_792);
lean_ctor_set(x_795, 1, x_793);
return x_795;
}
}
block_801:
{
if (lean_obj_tag(x_34) == 2)
{
lean_object* x_799; 
x_799 = lean_ctor_get(x_34, 4);
lean_inc(x_799);
x_706 = x_798;
x_707 = x_797;
x_708 = x_799;
goto block_796;
}
else
{
lean_object* x_800; 
x_800 = lean_ctor_get(x_34, 1);
lean_inc(x_800);
x_706 = x_798;
x_707 = x_797;
x_708 = x_800;
goto block_796;
}
}
block_808:
{
lean_object* x_804; 
x_804 = lean_box(1);
if (x_803 == 0)
{
uint8_t x_805; 
x_805 = lean_unbox(x_804);
lean_inc(x_85);
x_797 = x_805;
x_798 = x_85;
goto block_801;
}
else
{
lean_object* x_806; uint8_t x_807; 
x_806 = lean_nat_add(x_85, x_802);
x_807 = lean_unbox(x_804);
x_797 = x_807;
x_798 = x_806;
goto block_801;
}
}
}
}
else
{
uint8_t x_810; 
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_810 = !lean_is_exclusive(x_82);
if (x_810 == 0)
{
return x_82;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
x_811 = lean_ctor_get(x_82, 0);
x_812 = lean_ctor_get(x_82, 1);
lean_inc(x_812);
lean_inc(x_811);
lean_dec(x_82);
x_813 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_813, 0, x_811);
lean_ctor_set(x_813, 1, x_812);
return x_813;
}
}
block_80:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = l_Lean_Meta_Grind_getGoal___redArg(x_47, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_List_lengthTR___redArg(x_46);
x_60 = l_Lean_Meta_Grind_splitNext___lam__9___closed__0;
x_61 = l_List_mapIdx_go___at___Lean_Meta_Grind_splitNext_spec__0(x_57, x_41, x_59, x_43, x_46, x_60);
x_62 = l_Lean_Expr_mvar___override(x_45);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_44);
x_63 = l_Lean_Meta_Grind_mkChoice(x_62, x_61, x_44, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_58);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_Meta_Grind_intros(x_44, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
x_68 = lean_box(x_42);
lean_ctor_set(x_65, 0, x_68);
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_box(x_42);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_65);
if (x_72 == 0)
{
return x_65;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_65, 0);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_65);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_44);
x_76 = !lean_is_exclusive(x_63);
if (x_76 == 0)
{
return x_63;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_63, 0);
x_78 = lean_ctor_get(x_63, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_63);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_814 = lean_ctor_get(x_22, 1);
lean_inc(x_814);
lean_dec(x_22);
x_815 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_815, 0, x_20);
lean_ctor_set(x_815, 1, x_814);
x_816 = lean_st_ref_set(x_3, x_815, x_23);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_817 = lean_ctor_get(x_816, 1);
lean_inc(x_817);
if (lean_is_exclusive(x_816)) {
 lean_ctor_release(x_816, 0);
 lean_ctor_release(x_816, 1);
 x_818 = x_816;
} else {
 lean_dec_ref(x_816);
 x_818 = lean_box(0);
}
x_819 = lean_box(0);
if (lean_is_scalar(x_818)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_818;
}
lean_ctor_set(x_820, 0, x_819);
lean_ctor_set(x_820, 1, x_817);
return x_820;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; uint8_t x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; uint8_t x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_867; lean_object* x_868; 
x_821 = lean_ctor_get(x_816, 1);
lean_inc(x_821);
lean_dec(x_816);
x_822 = lean_ctor_get(x_19, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_19, 1);
lean_inc(x_823);
x_824 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
lean_dec(x_19);
x_825 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_821);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
x_828 = lean_ctor_get(x_826, 0);
lean_inc(x_828);
lean_dec(x_826);
x_829 = l_Lean_Meta_Grind_SplitInfo_getExpr(x_822);
lean_inc(x_829);
x_867 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__2___boxed), 10, 1);
lean_closure_set(x_867, 0, x_829);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_868 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_828, x_867, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_827);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; uint8_t x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_999; uint8_t x_1000; lean_object* x_1001; uint8_t x_1090; lean_object* x_1091; lean_object* x_1095; uint8_t x_1096; uint8_t x_1102; 
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = lean_ctor_get(x_869, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_869, 1);
lean_inc(x_872);
lean_dec(x_869);
x_873 = lean_st_ref_take(x_3, x_870);
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
x_876 = lean_ctor_get(x_874, 1);
lean_inc(x_876);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 lean_ctor_release(x_874, 1);
 x_877 = x_874;
} else {
 lean_dec_ref(x_874);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_877)) {
 x_878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_878 = x_877;
}
lean_ctor_set(x_878, 0, x_872);
lean_ctor_set(x_878, 1, x_876);
x_879 = lean_st_ref_set(x_3, x_878, x_875);
x_880 = lean_ctor_get(x_879, 1);
lean_inc(x_880);
lean_dec(x_879);
lean_inc(x_829);
x_881 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__3___boxed), 10, 1);
lean_closure_set(x_881, 0, x_829);
lean_inc(x_829);
x_882 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__4___boxed), 10, 1);
lean_closure_set(x_882, 0, x_829);
x_1095 = lean_unsigned_to_nat(1u);
x_1102 = lean_nat_dec_lt(x_1095, x_823);
if (x_1102 == 0)
{
x_1096 = x_824;
goto block_1101;
}
else
{
x_1096 = x_1102;
goto block_1101;
}
block_998:
{
lean_object* x_895; 
lean_inc(x_893);
lean_inc(x_892);
lean_inc(x_891);
lean_inc(x_890);
lean_inc(x_889);
lean_inc(x_888);
lean_inc(x_887);
lean_inc(x_886);
x_895 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(x_886, x_887, x_888, x_889, x_890, x_891, x_892, x_893, x_894);
if (lean_obj_tag(x_895) == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_896 = lean_ctor_get(x_895, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_895, 1);
lean_inc(x_897);
lean_dec(x_895);
lean_inc(x_893);
lean_inc(x_892);
lean_inc(x_891);
lean_inc(x_890);
lean_inc(x_889);
lean_inc(x_888);
lean_inc(x_887);
lean_inc(x_886);
x_898 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1(x_829, x_886, x_887, x_888, x_889, x_890, x_891, x_892, x_893, x_897);
if (lean_obj_tag(x_898) == 0)
{
if (lean_obj_tag(x_822) == 1)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
lean_dec(x_882);
x_899 = lean_ctor_get(x_822, 0);
lean_inc(x_899);
lean_dec(x_822);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
lean_dec(x_898);
x_901 = lean_ctor_get(x_899, 1);
lean_inc(x_901);
lean_dec(x_899);
x_902 = l_Lean_Meta_Grind_getGoal___redArg(x_886, x_900);
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
lean_dec(x_902);
x_905 = lean_ctor_get(x_903, 0);
lean_inc(x_905);
lean_dec(x_903);
x_906 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM(x_901);
lean_inc(x_896);
x_907 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__5___boxed), 11, 2);
lean_closure_set(x_907, 0, x_896);
lean_closure_set(x_907, 1, x_906);
lean_inc(x_893);
lean_inc(x_892);
lean_inc(x_891);
lean_inc(x_890);
lean_inc(x_889);
lean_inc(x_888);
lean_inc(x_887);
lean_inc(x_886);
x_908 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_905, x_907, x_886, x_887, x_888, x_889, x_890, x_891, x_892, x_893, x_904);
if (lean_obj_tag(x_908) == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_909 = lean_ctor_get(x_908, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_908, 1);
lean_inc(x_910);
lean_dec(x_908);
x_911 = lean_ctor_get(x_909, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_909, 1);
lean_inc(x_912);
lean_dec(x_909);
x_913 = lean_st_ref_take(x_886, x_910);
x_914 = lean_ctor_get(x_913, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_913, 1);
lean_inc(x_915);
lean_dec(x_913);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 x_917 = x_914;
} else {
 lean_dec_ref(x_914);
 x_917 = lean_box(0);
}
if (lean_is_scalar(x_917)) {
 x_918 = lean_alloc_ctor(0, 2, 0);
} else {
 x_918 = x_917;
}
lean_ctor_set(x_918, 0, x_912);
lean_ctor_set(x_918, 1, x_916);
x_919 = lean_st_ref_set(x_886, x_918, x_915);
x_920 = lean_ctor_get(x_919, 1);
lean_inc(x_920);
lean_dec(x_919);
x_830 = x_883;
x_831 = x_884;
x_832 = x_885;
x_833 = x_896;
x_834 = x_911;
x_835 = x_886;
x_836 = x_887;
x_837 = x_888;
x_838 = x_889;
x_839 = x_890;
x_840 = x_891;
x_841 = x_892;
x_842 = x_893;
x_843 = x_920;
goto block_866;
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec(x_896);
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_885);
lean_dec(x_884);
lean_dec(x_829);
x_921 = lean_ctor_get(x_908, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_908, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_908)) {
 lean_ctor_release(x_908, 0);
 lean_ctor_release(x_908, 1);
 x_923 = x_908;
} else {
 lean_dec_ref(x_908);
 x_923 = lean_box(0);
}
if (lean_is_scalar(x_923)) {
 x_924 = lean_alloc_ctor(1, 2, 0);
} else {
 x_924 = x_923;
}
lean_ctor_set(x_924, 0, x_921);
lean_ctor_set(x_924, 1, x_922);
return x_924;
}
}
else
{
lean_object* x_925; uint8_t x_926; 
lean_dec(x_822);
x_925 = lean_ctor_get(x_898, 0);
lean_inc(x_925);
x_926 = lean_unbox(x_925);
lean_dec(x_925);
if (x_926 == 0)
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_927 = lean_ctor_get(x_898, 1);
lean_inc(x_927);
lean_dec(x_898);
x_928 = l_Lean_Meta_Grind_getGoal___redArg(x_886, x_927);
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
lean_dec(x_928);
x_931 = lean_ctor_get(x_929, 0);
lean_inc(x_931);
lean_dec(x_929);
lean_inc(x_893);
lean_inc(x_892);
lean_inc(x_891);
lean_inc(x_890);
lean_inc(x_889);
lean_inc(x_888);
lean_inc(x_887);
lean_inc(x_886);
x_932 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_931, x_882, x_886, x_887, x_888, x_889, x_890, x_891, x_892, x_893, x_930);
if (lean_obj_tag(x_932) == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_932, 1);
lean_inc(x_934);
lean_dec(x_932);
x_935 = lean_ctor_get(x_933, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_933, 1);
lean_inc(x_936);
lean_dec(x_933);
x_937 = lean_st_ref_take(x_886, x_934);
x_938 = lean_ctor_get(x_937, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_937, 1);
lean_inc(x_939);
lean_dec(x_937);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_938)) {
 lean_ctor_release(x_938, 0);
 lean_ctor_release(x_938, 1);
 x_941 = x_938;
} else {
 lean_dec_ref(x_938);
 x_941 = lean_box(0);
}
if (lean_is_scalar(x_941)) {
 x_942 = lean_alloc_ctor(0, 2, 0);
} else {
 x_942 = x_941;
}
lean_ctor_set(x_942, 0, x_936);
lean_ctor_set(x_942, 1, x_940);
x_943 = lean_st_ref_set(x_886, x_942, x_939);
x_944 = lean_ctor_get(x_943, 1);
lean_inc(x_944);
lean_dec(x_943);
x_945 = l_Lean_Meta_Grind_getGoal___redArg(x_886, x_944);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec(x_945);
x_948 = lean_ctor_get(x_946, 0);
lean_inc(x_948);
lean_dec(x_946);
lean_inc(x_896);
x_949 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__6___boxed), 11, 2);
lean_closure_set(x_949, 0, x_896);
lean_closure_set(x_949, 1, x_935);
lean_inc(x_893);
lean_inc(x_892);
lean_inc(x_891);
lean_inc(x_890);
lean_inc(x_889);
lean_inc(x_888);
lean_inc(x_887);
lean_inc(x_886);
x_950 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_948, x_949, x_886, x_887, x_888, x_889, x_890, x_891, x_892, x_893, x_947);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_950, 1);
lean_inc(x_952);
lean_dec(x_950);
x_953 = lean_ctor_get(x_951, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_951, 1);
lean_inc(x_954);
lean_dec(x_951);
x_955 = lean_st_ref_take(x_886, x_952);
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_955, 1);
lean_inc(x_957);
lean_dec(x_955);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_959 = x_956;
} else {
 lean_dec_ref(x_956);
 x_959 = lean_box(0);
}
if (lean_is_scalar(x_959)) {
 x_960 = lean_alloc_ctor(0, 2, 0);
} else {
 x_960 = x_959;
}
lean_ctor_set(x_960, 0, x_954);
lean_ctor_set(x_960, 1, x_958);
x_961 = lean_st_ref_set(x_886, x_960, x_957);
x_962 = lean_ctor_get(x_961, 1);
lean_inc(x_962);
lean_dec(x_961);
x_830 = x_883;
x_831 = x_884;
x_832 = x_885;
x_833 = x_896;
x_834 = x_953;
x_835 = x_886;
x_836 = x_887;
x_837 = x_888;
x_838 = x_889;
x_839 = x_890;
x_840 = x_891;
x_841 = x_892;
x_842 = x_893;
x_843 = x_962;
goto block_866;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_dec(x_896);
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_885);
lean_dec(x_884);
lean_dec(x_829);
x_963 = lean_ctor_get(x_950, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_950, 1);
lean_inc(x_964);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_965 = x_950;
} else {
 lean_dec_ref(x_950);
 x_965 = lean_box(0);
}
if (lean_is_scalar(x_965)) {
 x_966 = lean_alloc_ctor(1, 2, 0);
} else {
 x_966 = x_965;
}
lean_ctor_set(x_966, 0, x_963);
lean_ctor_set(x_966, 1, x_964);
return x_966;
}
}
else
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_896);
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_885);
lean_dec(x_884);
lean_dec(x_829);
x_967 = lean_ctor_get(x_932, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_932, 1);
lean_inc(x_968);
if (lean_is_exclusive(x_932)) {
 lean_ctor_release(x_932, 0);
 lean_ctor_release(x_932, 1);
 x_969 = x_932;
} else {
 lean_dec_ref(x_932);
 x_969 = lean_box(0);
}
if (lean_is_scalar(x_969)) {
 x_970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_970 = x_969;
}
lean_ctor_set(x_970, 0, x_967);
lean_ctor_set(x_970, 1, x_968);
return x_970;
}
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_882);
x_971 = lean_ctor_get(x_898, 1);
lean_inc(x_971);
lean_dec(x_898);
x_972 = l_Lean_Meta_Grind_getGoal___redArg(x_886, x_971);
x_973 = lean_ctor_get(x_972, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_972, 1);
lean_inc(x_974);
lean_dec(x_972);
x_975 = lean_ctor_get(x_973, 0);
lean_inc(x_975);
lean_dec(x_973);
lean_inc(x_829);
lean_inc(x_896);
x_976 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__7___boxed), 11, 2);
lean_closure_set(x_976, 0, x_896);
lean_closure_set(x_976, 1, x_829);
lean_inc(x_893);
lean_inc(x_892);
lean_inc(x_891);
lean_inc(x_890);
lean_inc(x_889);
lean_inc(x_888);
lean_inc(x_887);
lean_inc(x_886);
x_977 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_975, x_976, x_886, x_887, x_888, x_889, x_890, x_891, x_892, x_893, x_974);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_977, 1);
lean_inc(x_979);
lean_dec(x_977);
x_980 = lean_ctor_get(x_978, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_978, 1);
lean_inc(x_981);
lean_dec(x_978);
x_982 = lean_st_ref_take(x_886, x_979);
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_982, 1);
lean_inc(x_984);
lean_dec(x_982);
x_985 = lean_ctor_get(x_983, 1);
lean_inc(x_985);
if (lean_is_exclusive(x_983)) {
 lean_ctor_release(x_983, 0);
 lean_ctor_release(x_983, 1);
 x_986 = x_983;
} else {
 lean_dec_ref(x_983);
 x_986 = lean_box(0);
}
if (lean_is_scalar(x_986)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_986;
}
lean_ctor_set(x_987, 0, x_981);
lean_ctor_set(x_987, 1, x_985);
x_988 = lean_st_ref_set(x_886, x_987, x_984);
x_989 = lean_ctor_get(x_988, 1);
lean_inc(x_989);
lean_dec(x_988);
x_830 = x_883;
x_831 = x_884;
x_832 = x_885;
x_833 = x_896;
x_834 = x_980;
x_835 = x_886;
x_836 = x_887;
x_837 = x_888;
x_838 = x_889;
x_839 = x_890;
x_840 = x_891;
x_841 = x_892;
x_842 = x_893;
x_843 = x_989;
goto block_866;
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_dec(x_896);
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_885);
lean_dec(x_884);
lean_dec(x_829);
x_990 = lean_ctor_get(x_977, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_977, 1);
lean_inc(x_991);
if (lean_is_exclusive(x_977)) {
 lean_ctor_release(x_977, 0);
 lean_ctor_release(x_977, 1);
 x_992 = x_977;
} else {
 lean_dec_ref(x_977);
 x_992 = lean_box(0);
}
if (lean_is_scalar(x_992)) {
 x_993 = lean_alloc_ctor(1, 2, 0);
} else {
 x_993 = x_992;
}
lean_ctor_set(x_993, 0, x_990);
lean_ctor_set(x_993, 1, x_991);
return x_993;
}
}
}
}
else
{
lean_dec(x_896);
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_885);
lean_dec(x_884);
lean_dec(x_882);
lean_dec(x_829);
lean_dec(x_822);
return x_898;
}
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_891);
lean_dec(x_890);
lean_dec(x_889);
lean_dec(x_888);
lean_dec(x_887);
lean_dec(x_886);
lean_dec(x_885);
lean_dec(x_884);
lean_dec(x_882);
lean_dec(x_829);
lean_dec(x_822);
x_994 = lean_ctor_get(x_895, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_895, 1);
lean_inc(x_995);
if (lean_is_exclusive(x_895)) {
 lean_ctor_release(x_895, 0);
 lean_ctor_release(x_895, 1);
 x_996 = x_895;
} else {
 lean_dec_ref(x_895);
 x_996 = lean_box(0);
}
if (lean_is_scalar(x_996)) {
 x_997 = lean_alloc_ctor(1, 2, 0);
} else {
 x_997 = x_996;
}
lean_ctor_set(x_997, 0, x_994);
lean_ctor_set(x_997, 1, x_995);
return x_997;
}
}
block_1089:
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
x_1002 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_880);
x_1003 = lean_ctor_get(x_1002, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_1002, 1);
lean_inc(x_1004);
lean_dec(x_1002);
x_1005 = lean_ctor_get(x_1003, 0);
lean_inc(x_1005);
lean_dec(x_1003);
lean_inc(x_1001);
lean_inc(x_999);
lean_inc(x_829);
x_1006 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__8___boxed), 13, 4);
lean_closure_set(x_1006, 0, x_829);
lean_closure_set(x_1006, 1, x_999);
lean_closure_set(x_1006, 2, x_823);
lean_closure_set(x_1006, 3, x_1001);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1007 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1005, x_1006, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1004);
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1008 = lean_ctor_get(x_1007, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_1007, 1);
lean_inc(x_1009);
lean_dec(x_1007);
x_1010 = lean_ctor_get(x_1008, 1);
lean_inc(x_1010);
lean_dec(x_1008);
x_1011 = lean_st_ref_take(x_3, x_1009);
x_1012 = lean_ctor_get(x_1011, 0);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_1011, 1);
lean_inc(x_1013);
lean_dec(x_1011);
x_1014 = lean_ctor_get(x_1012, 1);
lean_inc(x_1014);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 lean_ctor_release(x_1012, 1);
 x_1015 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1015 = lean_box(0);
}
if (lean_is_scalar(x_1015)) {
 x_1016 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1016 = x_1015;
}
lean_ctor_set(x_1016, 0, x_1010);
lean_ctor_set(x_1016, 1, x_1014);
x_1017 = lean_st_ref_set(x_3, x_1016, x_1013);
x_1018 = lean_ctor_get(x_1017, 1);
lean_inc(x_1018);
lean_dec(x_1017);
x_1019 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_1018);
x_1020 = lean_ctor_get(x_1019, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1019, 1);
lean_inc(x_1021);
lean_dec(x_1019);
x_1022 = lean_ctor_get(x_1020, 0);
lean_inc(x_1022);
lean_dec(x_1020);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1023 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1022, x_881, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1021);
if (lean_obj_tag(x_1023) == 0)
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
x_1024 = lean_ctor_get(x_1023, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_1023, 1);
lean_inc(x_1025);
lean_dec(x_1023);
x_1026 = lean_ctor_get(x_1024, 1);
lean_inc(x_1026);
lean_dec(x_1024);
x_1027 = lean_st_ref_take(x_3, x_1025);
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec(x_1027);
x_1030 = lean_ctor_get(x_1028, 1);
lean_inc(x_1030);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 lean_ctor_release(x_1028, 1);
 x_1031 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1031 = lean_box(0);
}
if (lean_is_scalar(x_1031)) {
 x_1032 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1032 = x_1031;
}
lean_ctor_set(x_1032, 0, x_1026);
lean_ctor_set(x_1032, 1, x_1030);
x_1033 = lean_st_ref_set(x_3, x_1032, x_1029);
x_1034 = lean_ctor_get(x_1033, 1);
lean_inc(x_1034);
lean_dec(x_1033);
x_1035 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1036 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2(x_1035, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1034);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; uint8_t x_1038; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_unbox(x_1037);
lean_dec(x_1037);
if (x_1038 == 0)
{
lean_object* x_1039; 
lean_dec(x_871);
lean_dec(x_2);
x_1039 = lean_ctor_get(x_1036, 1);
lean_inc(x_1039);
lean_dec(x_1036);
x_883 = x_1000;
x_884 = x_1001;
x_885 = x_999;
x_886 = x_3;
x_887 = x_4;
x_888 = x_5;
x_889 = x_6;
x_890 = x_7;
x_891 = x_8;
x_892 = x_9;
x_893 = x_10;
x_894 = x_1039;
goto block_998;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
x_1040 = lean_ctor_get(x_1036, 1);
lean_inc(x_1040);
lean_dec(x_1036);
x_1041 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_1040);
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1044 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1044 = lean_box(0);
}
x_1045 = lean_ctor_get(x_1042, 0);
lean_inc(x_1045);
lean_dec(x_1042);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1046 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1045, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1043);
if (lean_obj_tag(x_1046) == 0)
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
lean_dec(x_1046);
x_1049 = lean_ctor_get(x_1047, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 lean_ctor_release(x_1047, 1);
 x_1050 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1050 = lean_box(0);
}
x_1051 = lean_st_ref_take(x_3, x_1048);
x_1052 = lean_ctor_get(x_1051, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1051, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_1051)) {
 lean_ctor_release(x_1051, 0);
 lean_ctor_release(x_1051, 1);
 x_1054 = x_1051;
} else {
 lean_dec_ref(x_1051);
 x_1054 = lean_box(0);
}
x_1055 = lean_ctor_get(x_1052, 1);
lean_inc(x_1055);
if (lean_is_exclusive(x_1052)) {
 lean_ctor_release(x_1052, 0);
 lean_ctor_release(x_1052, 1);
 x_1056 = x_1052;
} else {
 lean_dec_ref(x_1052);
 x_1056 = lean_box(0);
}
if (lean_is_scalar(x_1056)) {
 x_1057 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1057 = x_1056;
}
lean_ctor_set(x_1057, 0, x_1049);
lean_ctor_set(x_1057, 1, x_1055);
x_1058 = lean_st_ref_set(x_3, x_1057, x_1053);
x_1059 = lean_ctor_get(x_1058, 1);
lean_inc(x_1059);
if (lean_is_exclusive(x_1058)) {
 lean_ctor_release(x_1058, 0);
 lean_ctor_release(x_1058, 1);
 x_1060 = x_1058;
} else {
 lean_dec_ref(x_1058);
 x_1060 = lean_box(0);
}
x_1061 = l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5;
lean_inc(x_829);
x_1062 = l_Lean_MessageData_ofExpr(x_829);
if (lean_is_scalar(x_1060)) {
 x_1063 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1063 = x_1060;
 lean_ctor_set_tag(x_1063, 7);
}
lean_ctor_set(x_1063, 0, x_1061);
lean_ctor_set(x_1063, 1, x_1062);
x_1064 = l_Lean_Meta_Grind_splitNext___lam__9___closed__2;
if (lean_is_scalar(x_1054)) {
 x_1065 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1065 = x_1054;
 lean_ctor_set_tag(x_1065, 7);
}
lean_ctor_set(x_1065, 0, x_1063);
lean_ctor_set(x_1065, 1, x_1064);
x_1066 = l_Nat_reprFast(x_871);
x_1067 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1067, 0, x_1066);
x_1068 = l_Lean_MessageData_ofFormat(x_1067);
if (lean_is_scalar(x_1050)) {
 x_1069 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1069 = x_1050;
 lean_ctor_set_tag(x_1069, 7);
}
lean_ctor_set(x_1069, 0, x_1065);
lean_ctor_set(x_1069, 1, x_1068);
if (lean_is_scalar(x_1044)) {
 x_1070 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1070 = x_1044;
 lean_ctor_set_tag(x_1070, 7);
}
lean_ctor_set(x_1070, 0, x_1069);
lean_ctor_set(x_1070, 1, x_1061);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1071 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3(x_1035, x_1070, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1059);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1072; 
x_1072 = lean_ctor_get(x_1071, 1);
lean_inc(x_1072);
lean_dec(x_1071);
x_883 = x_1000;
x_884 = x_1001;
x_885 = x_999;
x_886 = x_3;
x_887 = x_4;
x_888 = x_5;
x_889 = x_6;
x_890 = x_7;
x_891 = x_8;
x_892 = x_9;
x_893 = x_10;
x_894 = x_1072;
goto block_998;
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
lean_dec(x_1001);
lean_dec(x_999);
lean_dec(x_882);
lean_dec(x_829);
lean_dec(x_822);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1073 = lean_ctor_get(x_1071, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1071, 1);
lean_inc(x_1074);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1075 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1075 = lean_box(0);
}
if (lean_is_scalar(x_1075)) {
 x_1076 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1076 = x_1075;
}
lean_ctor_set(x_1076, 0, x_1073);
lean_ctor_set(x_1076, 1, x_1074);
return x_1076;
}
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
lean_dec(x_1044);
lean_dec(x_1001);
lean_dec(x_999);
lean_dec(x_882);
lean_dec(x_871);
lean_dec(x_829);
lean_dec(x_822);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1077 = lean_ctor_get(x_1046, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1046, 1);
lean_inc(x_1078);
if (lean_is_exclusive(x_1046)) {
 lean_ctor_release(x_1046, 0);
 lean_ctor_release(x_1046, 1);
 x_1079 = x_1046;
} else {
 lean_dec_ref(x_1046);
 x_1079 = lean_box(0);
}
if (lean_is_scalar(x_1079)) {
 x_1080 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1080 = x_1079;
}
lean_ctor_set(x_1080, 0, x_1077);
lean_ctor_set(x_1080, 1, x_1078);
return x_1080;
}
}
}
else
{
lean_dec(x_1001);
lean_dec(x_999);
lean_dec(x_882);
lean_dec(x_871);
lean_dec(x_829);
lean_dec(x_822);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1036;
}
}
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
lean_dec(x_1001);
lean_dec(x_999);
lean_dec(x_882);
lean_dec(x_871);
lean_dec(x_829);
lean_dec(x_822);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1081 = lean_ctor_get(x_1023, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1023, 1);
lean_inc(x_1082);
if (lean_is_exclusive(x_1023)) {
 lean_ctor_release(x_1023, 0);
 lean_ctor_release(x_1023, 1);
 x_1083 = x_1023;
} else {
 lean_dec_ref(x_1023);
 x_1083 = lean_box(0);
}
if (lean_is_scalar(x_1083)) {
 x_1084 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1084 = x_1083;
}
lean_ctor_set(x_1084, 0, x_1081);
lean_ctor_set(x_1084, 1, x_1082);
return x_1084;
}
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
lean_dec(x_1001);
lean_dec(x_999);
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_871);
lean_dec(x_829);
lean_dec(x_822);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1085 = lean_ctor_get(x_1007, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1007, 1);
lean_inc(x_1086);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1087 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1087 = lean_box(0);
}
if (lean_is_scalar(x_1087)) {
 x_1088 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1088 = x_1087;
}
lean_ctor_set(x_1088, 0, x_1085);
lean_ctor_set(x_1088, 1, x_1086);
return x_1088;
}
}
block_1094:
{
if (lean_obj_tag(x_822) == 2)
{
lean_object* x_1092; 
x_1092 = lean_ctor_get(x_822, 4);
lean_inc(x_1092);
x_999 = x_1091;
x_1000 = x_1090;
x_1001 = x_1092;
goto block_1089;
}
else
{
lean_object* x_1093; 
x_1093 = lean_ctor_get(x_822, 1);
lean_inc(x_1093);
x_999 = x_1091;
x_1000 = x_1090;
x_1001 = x_1093;
goto block_1089;
}
}
block_1101:
{
lean_object* x_1097; 
x_1097 = lean_box(1);
if (x_1096 == 0)
{
uint8_t x_1098; 
x_1098 = lean_unbox(x_1097);
lean_inc(x_871);
x_1090 = x_1098;
x_1091 = x_871;
goto block_1094;
}
else
{
lean_object* x_1099; uint8_t x_1100; 
x_1099 = lean_nat_add(x_871, x_1095);
x_1100 = lean_unbox(x_1097);
x_1090 = x_1100;
x_1091 = x_1099;
goto block_1094;
}
}
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
lean_dec(x_829);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1103 = lean_ctor_get(x_868, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_868, 1);
lean_inc(x_1104);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_1105 = x_868;
} else {
 lean_dec_ref(x_868);
 x_1105 = lean_box(0);
}
if (lean_is_scalar(x_1105)) {
 x_1106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1106 = x_1105;
}
lean_ctor_set(x_1106, 0, x_1103);
lean_ctor_set(x_1106, 1, x_1104);
return x_1106;
}
block_866:
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_844 = l_Lean_Meta_Grind_getGoal___redArg(x_835, x_843);
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_844, 1);
lean_inc(x_846);
lean_dec(x_844);
x_847 = l_List_lengthTR___redArg(x_834);
x_848 = l_Lean_Meta_Grind_splitNext___lam__9___closed__0;
x_849 = l_List_mapIdx_go___at___Lean_Meta_Grind_splitNext_spec__0(x_845, x_829, x_847, x_831, x_834, x_848);
x_850 = l_Lean_Expr_mvar___override(x_833);
lean_inc(x_842);
lean_inc(x_841);
lean_inc(x_840);
lean_inc(x_839);
lean_inc(x_838);
lean_inc(x_837);
lean_inc(x_836);
lean_inc(x_835);
lean_inc(x_832);
x_851 = l_Lean_Meta_Grind_mkChoice(x_850, x_849, x_832, x_835, x_836, x_837, x_838, x_839, x_840, x_841, x_842, x_846);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; 
x_852 = lean_ctor_get(x_851, 1);
lean_inc(x_852);
lean_dec(x_851);
x_853 = l_Lean_Meta_Grind_intros(x_832, x_835, x_836, x_837, x_838, x_839, x_840, x_841, x_842, x_852);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_854 = lean_ctor_get(x_853, 1);
lean_inc(x_854);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_855 = x_853;
} else {
 lean_dec_ref(x_853);
 x_855 = lean_box(0);
}
x_856 = lean_box(x_830);
if (lean_is_scalar(x_855)) {
 x_857 = lean_alloc_ctor(0, 2, 0);
} else {
 x_857 = x_855;
}
lean_ctor_set(x_857, 0, x_856);
lean_ctor_set(x_857, 1, x_854);
return x_857;
}
else
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_858 = lean_ctor_get(x_853, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_853, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_860 = x_853;
} else {
 lean_dec_ref(x_853);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_860)) {
 x_861 = lean_alloc_ctor(1, 2, 0);
} else {
 x_861 = x_860;
}
lean_ctor_set(x_861, 0, x_858);
lean_ctor_set(x_861, 1, x_859);
return x_861;
}
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_842);
lean_dec(x_841);
lean_dec(x_840);
lean_dec(x_839);
lean_dec(x_838);
lean_dec(x_837);
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_832);
x_862 = lean_ctor_get(x_851, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_851, 1);
lean_inc(x_863);
if (lean_is_exclusive(x_851)) {
 lean_ctor_release(x_851, 0);
 lean_ctor_release(x_851, 1);
 x_864 = x_851;
} else {
 lean_dec_ref(x_851);
 x_864 = lean_box(0);
}
if (lean_is_scalar(x_864)) {
 x_865 = lean_alloc_ctor(1, 2, 0);
} else {
 x_865 = x_864;
}
lean_ctor_set(x_865, 0, x_862);
lean_ctor_set(x_865, 1, x_863);
return x_865;
}
}
}
}
}
else
{
uint8_t x_1107; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1107 = !lean_is_exclusive(x_16);
if (x_1107 == 0)
{
return x_16;
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1108 = lean_ctor_get(x_16, 0);
x_1109 = lean_ctor_get(x_16, 1);
lean_inc(x_1109);
lean_inc(x_1108);
lean_dec(x_16);
x_1110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1110, 0, x_1108);
lean_ctor_set(x_1110, 1, x_1109);
return x_1110;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__0___boxed), 9, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__1___boxed), 9, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_splitNext___lam__9), 11, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_13, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Grind_splitNext_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_splitNext_spec__2___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_splitNext___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_splitNext___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_splitNext___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_splitNext___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_splitNext___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_splitNext___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_splitNext___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_splitNext___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitNext___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_splitNext___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_SearchM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SearchM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedSplitStatus = _init_l_Lean_Meta_Grind_instInhabitedSplitStatus();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSplitStatus);
l_Lean_Meta_Grind_instBEqSplitStatus___closed__0 = _init_l_Lean_Meta_Grind_instBEqSplitStatus___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqSplitStatus___closed__0);
l_Lean_Meta_Grind_instBEqSplitStatus = _init_l_Lean_Meta_Grind_instBEqSplitStatus();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqSplitStatus);
l_Lean_Meta_Grind_reprSplitStatus___closed__0____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_ = _init_l_Lean_Meta_Grind_reprSplitStatus___closed__0____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_();
lean_mark_persistent(l_Lean_Meta_Grind_reprSplitStatus___closed__0____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_);
l_Lean_Meta_Grind_reprSplitStatus___closed__1____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_ = _init_l_Lean_Meta_Grind_reprSplitStatus___closed__1____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_();
lean_mark_persistent(l_Lean_Meta_Grind_reprSplitStatus___closed__1____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_);
l_Lean_Meta_Grind_reprSplitStatus___closed__2____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_ = _init_l_Lean_Meta_Grind_reprSplitStatus___closed__2____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_();
lean_mark_persistent(l_Lean_Meta_Grind_reprSplitStatus___closed__2____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_);
l_Lean_Meta_Grind_reprSplitStatus___closed__3____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_ = _init_l_Lean_Meta_Grind_reprSplitStatus___closed__3____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_();
lean_mark_persistent(l_Lean_Meta_Grind_reprSplitStatus___closed__3____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_);
l_Lean_Meta_Grind_reprSplitStatus___closed__4____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_ = _init_l_Lean_Meta_Grind_reprSplitStatus___closed__4____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_();
lean_mark_persistent(l_Lean_Meta_Grind_reprSplitStatus___closed__4____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_);
l_Lean_Meta_Grind_reprSplitStatus___closed__5____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_ = _init_l_Lean_Meta_Grind_reprSplitStatus___closed__5____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_();
lean_mark_persistent(l_Lean_Meta_Grind_reprSplitStatus___closed__5____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_);
l_Lean_Meta_Grind_reprSplitStatus___closed__6____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_ = _init_l_Lean_Meta_Grind_reprSplitStatus___closed__6____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_();
lean_mark_persistent(l_Lean_Meta_Grind_reprSplitStatus___closed__6____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_);
l_Lean_Meta_Grind_reprSplitStatus___closed__7____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_ = _init_l_Lean_Meta_Grind_reprSplitStatus___closed__7____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_();
lean_mark_persistent(l_Lean_Meta_Grind_reprSplitStatus___closed__7____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_);
l_Lean_Meta_Grind_reprSplitStatus___closed__8____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_ = _init_l_Lean_Meta_Grind_reprSplitStatus___closed__8____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_();
lean_mark_persistent(l_Lean_Meta_Grind_reprSplitStatus___closed__8____x40_Lean_Meta_Tactic_Grind_Split___hyg_168_);
l_Lean_Meta_Grind_instReprSplitStatus___closed__0 = _init_l_Lean_Meta_Grind_instReprSplitStatus___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus___closed__0);
l_Lean_Meta_Grind_instReprSplitStatus = _init_l_Lean_Meta_Grind_instReprSplitStatus();
lean_mark_persistent(l_Lean_Meta_Grind_instReprSplitStatus);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__0);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__2);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__3);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__4);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__5);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__6);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__7);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__8);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__9);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__10);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__11);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__12);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__13);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__14);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__15);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__16);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_checkDefaultSplitStatus___closed__17);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__0);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__1);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__2);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__3);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__4);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__5);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__6);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__7);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__8);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__9);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__10);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__11);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__12);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_checkSplitInfoArgStatus_spec__0_spec__0___closed__13);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__0);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_selectNextSplit_x3f_go___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__0);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__2);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__3);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkGrindEM___closed__4);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__0);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__1);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__2);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__3);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__4);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__5);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__6);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__7);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__8);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__9);
l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Split_0__Lean_Meta_Grind_mkCasesMajor___closed__10);
l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__0();
l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_splitNext_spec__3___lam__1___closed__1);
l_Lean_Meta_Grind_splitNext___lam__9___closed__0 = _init_l_Lean_Meta_Grind_splitNext___lam__9___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_splitNext___lam__9___closed__0);
l_Lean_Meta_Grind_splitNext___lam__9___closed__1 = _init_l_Lean_Meta_Grind_splitNext___lam__9___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_splitNext___lam__9___closed__1);
l_Lean_Meta_Grind_splitNext___lam__9___closed__2 = _init_l_Lean_Meta_Grind_splitNext___lam__9___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_splitNext___lam__9___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
